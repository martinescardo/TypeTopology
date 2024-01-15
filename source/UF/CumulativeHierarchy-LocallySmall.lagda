Tom de Jong, 29 November 2022.
In collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu.

Cleaned up on 16 and 19 December 2022.

The cumulative hierarchy 𝕍 with respect to a universe 𝓤 is a large type, meaning
it lives in the next universe 𝓤 ⁺. Hence, for elements x, y : 𝕍, the identity type
x ＝ y of 𝕍 also lives in 𝓤 ⁺. However, as pointed out in the HoTT Book
[Section 10.5, 1], it is possible to define a binary relation on 𝕍 that takes
values in 𝓤 and prove it equivalent to the identity type of 𝕍. This makes 𝕍 an
example of a locally 𝓤-small type.

The membership relation on 𝕍 makes use of equality on 𝕍, and hence, has values
in 𝓤 ⁺ too. But, using that 𝕍 is locally 𝓤-small we can define an equivalent
𝓤-small membership relation.

These facts are used in our development relating set theoretic and type
theoretic ordinals, see Ordinals/CumulativeHierarchy-Addendum.lagda.

References
----------

[1] The Univalent Foundations Program
    Homotopy Type Theory: Univalent Foundations of Mathematics
    https://homotopytypetheory.org/book
    Institute for Advanced Study
    2013

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module UF.CumulativeHierarchy-LocallySmall
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Size
open import UF.Sets-Properties
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

The idea is to have a 𝓤-valued equality relation on 𝕍 by defining:
  𝕍-set {A} f ＝⁻ 𝕍-set {B} g
inductively as
    (Π a : A , ∃ b : B , f a ＝⁻ g b)
  × (Π b : B , ∃ a : A , g b ＝⁻ f a).

Of course, we need to formally check that this definition respects the 𝕍-set-ext
constructor of 𝕍 in both arguments, which is provided by the setup below.

\begin{code}

open import UF.CumulativeHierarchy pt fe pe

module 𝕍-is-locally-small
        {𝓤 : Universe}
        (ch : cumulative-hierarchy-exists 𝓤)
       where

 open cumulative-hierarchy-exists ch

 private
  module _
          {A : 𝓤 ̇ }
          (f : A → 𝕍)
          (r : A → 𝕍 → Ω 𝓤)
         where

   ＝⁻-aux₁ : {B : 𝓤 ̇ } → (B → 𝕍) → Ω 𝓤
   ＝⁻-aux₁ {B} g = (Ɐ a ꞉ A , Ǝ b ꞉ B , r a (g b) holds)
                  ∧ (Ɐ b ꞉ B , Ǝ a ꞉ A , r a (g b) holds)

   ＝⁻-aux₁-respects-≈ : {B' B : 𝓤 ̇ } (g' : B' → 𝕍) (g : B → 𝕍)
                       → g' ≈ g
                       → ＝⁻-aux₁ g' holds
                       → ＝⁻-aux₁ g  holds
   ＝⁻-aux₁-respects-≈ {B'} {B} g' g (s , t) (u , v) = ⦅1⦆ , ⦅2⦆
    where
     ⦅1⦆ : (a : A) → ∃ b ꞉ B , r a (g b) holds
     ⦅1⦆ a = ∥∥-rec ∃-is-prop h₁ (u a)
      where
       h₁ : (Σ b' ꞉ B' , r a (g' b') holds) → ∃ b ꞉ B , r a (g b) holds
       h₁ (b' , p) = ∥∥-functor h₂ (s b')
        where
         h₂ : (Σ b ꞉ B , g b ＝ g' b') → Σ b ꞉ B , r a (g b) holds
         h₂ (b , e) = b , transport (λ - → (r a -) holds) (e ⁻¹) p
     ⦅2⦆ : (b : B) → ∃ a ꞉ A , r a (g b) holds
     ⦅2⦆ b = ∥∥-rec ∃-is-prop h₁ (t b)
      where
       h₁ : (Σ b' ꞉ B' , g' b' ＝ g b) → ∃ a ꞉ A , r a (g b) holds
       h₁ (b' , e) = ∥∥-functor h₂ (v b')
        where
         h₂ : (Σ a ꞉ A , r a (g' b') holds) → Σ a ꞉ A , r a (g b) holds
         h₂ (a , p) = a , transport (λ - → (r a -) holds) e p

   ＝⁻-aux₁-respects-≈' : {B' B : 𝓤 ̇ } (g' : B' → 𝕍) (g : B → 𝕍)
                        → g' ≈ g
                        → ＝⁻-aux₁ g' ＝ ＝⁻-aux₁ g
   ＝⁻-aux₁-respects-≈' {B'} {B} g' g e =
    Ω-extensionality pe fe
     (＝⁻-aux₁-respects-≈ g' g e)
     (＝⁻-aux₁-respects-≈ g g' (≈-sym e))

   ＝⁻-aux₂ : 𝕍 → Ω 𝓤
   ＝⁻-aux₂ = 𝕍-recursion (Ω-is-set fe pe) (λ g _ → ＝⁻-aux₁ g)
                          (λ g' g _ _ _ _ e → ＝⁻-aux₁-respects-≈' g' g e)

   ＝⁻-aux₂-behaviour : {B : 𝓤 ̇ } (g : B → 𝕍) → ＝⁻-aux₂ (𝕍-set g) ＝ ＝⁻-aux₁ g
   ＝⁻-aux₂-behaviour g =
    𝕍-recursion-computes (Ω-is-set fe pe) (λ g₁ _ → ＝⁻-aux₁ g₁)
                         (λ g' g _ _ _ _ e → ＝⁻-aux₁-respects-≈' g' g e)
                         g (λ _ → 𝟙 , 𝟙-is-prop)

  ＝⁻-aux₂-respects-≈ : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                      → (r₁ : A → 𝕍 → Ω 𝓤) (r₂ : B → 𝕍 → Ω 𝓤)
                      → ((a : A) → ∃ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
                      → ((b : B) → ∃ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
                      → {C : 𝓤 ̇ } (h : C → 𝕍)
                      → ＝⁻-aux₁ f r₁ h holds
                      → ＝⁻-aux₁ g r₂ h holds
  ＝⁻-aux₂-respects-≈ {A} {B} f g r₁ r₂ s t {C} h (u , v) = ⦅1⦆ , ⦅2⦆
   where
    ⦅1⦆ : (b : B) → ∃ c ꞉ C , r₂ b (h c) holds
    ⦅1⦆ b = ∥∥-rec ∃-is-prop m (t b)
     where
      m : (Σ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
        → ∃ c ꞉ C , r₂ b (h c) holds
      m (a , _ , q) = ∥∥-functor n (u a)
       where
        n : (Σ c ꞉ C , r₁ a (h c) holds)
          → Σ c ꞉ C , r₂ b (h c) holds
        n (c , w) = c , Idtofun (ap _holds (happly (q ⁻¹) (h c))) w
    ⦅2⦆ : (c : C) → ∃ b ꞉ B , r₂ b (h c) holds
    ⦅2⦆ c = ∥∥-rec ∃-is-prop n (v c)
     where
      n : (Σ a ꞉ A , r₁ a (h c) holds)
        → ∃ b ꞉ B , r₂ b (h c) holds
      n (a , w) = ∥∥-functor m (s a)
       where
        m : (Σ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
          → Σ b ꞉ B , r₂ b (h c) holds
        m (b , _ , q) = b , Idtofun (ap _holds (happly q (h c))) w

  ＝⁻-aux₂-respects-≈' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
                         (r₁ : A → 𝕍 → Ω 𝓤) (r₂ : B → 𝕍 → Ω 𝓤)
                       → ((a : A) → ∃ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
                       → ((b : B) → ∃ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
                       → f ≈ g
                       → ＝⁻-aux₂ f r₁ ＝ ＝⁻-aux₂ g r₂
  ＝⁻-aux₂-respects-≈' {A} {B} f g r₁ r₂ IH₁ IH₂ _ =
   dfunext fe (𝕍-prop-simple-induction (λ x → ＝⁻-aux₂ f r₁ x ＝ ＝⁻-aux₂ g r₂ x)
                                       (λ _ → Ω-is-set fe pe)
                                       σ)
    where
     σ : {C : 𝓤 ̇ } (h : C → 𝕍)
       → ＝⁻-aux₂ f r₁ (𝕍-set h) ＝ ＝⁻-aux₂ g r₂ (𝕍-set h)
     σ h = ＝⁻-aux₂ f r₁ (𝕍-set h) ＝⟨ ＝⁻-aux₂-behaviour f r₁ h      ⟩
           ＝⁻-aux₁ f r₁ h         ＝⟨ e                              ⟩
           ＝⁻-aux₁ g r₂ h         ＝⟨ (＝⁻-aux₂-behaviour g r₂ h) ⁻¹ ⟩
           ＝⁻-aux₂ g r₂ (𝕍-set h) ∎
      where
       e = Ω-extensionality pe fe
            (＝⁻-aux₂-respects-≈ f g r₁ r₂ IH₁ IH₂ h)
            (＝⁻-aux₂-respects-≈ g f r₂ r₁ IH₂ IH₁ h)

\end{code}

We package up the above in the following definition which records the behaviour
of the relation on the 𝕍-set constructor.

\begin{code}

  ＝⁻[Ω]-packaged : Σ ϕ ꞉ (𝕍 → 𝕍 → Ω 𝓤) , ({A : 𝓤 ̇ } (f : A → 𝕍)
                                           (r : A → 𝕍 → Ω 𝓤)
                                        → ϕ (𝕍-set f) ＝ ＝⁻-aux₂ f r)
  ＝⁻[Ω]-packaged = 𝕍-recursion-with-computation
                     (Π-is-set fe (λ _ → Ω-is-set fe pe))
                     ＝⁻-aux₂
                     ＝⁻-aux₂-respects-≈'

 _＝⁻[Ω]_ : 𝕍 → 𝕍 → Ω 𝓤
 _＝⁻[Ω]_ = pr₁ ＝⁻[Ω]-packaged

 _＝⁻_ : 𝕍 → 𝕍 → 𝓤 ̇
 x ＝⁻ y = (x ＝⁻[Ω] y) holds

 ＝⁻-is-prop-valued : {x y : 𝕍} → is-prop (x ＝⁻ y)
 ＝⁻-is-prop-valued {x} {y} = holds-is-prop (x ＝⁻[Ω] y)

\end{code}

The following lemma shows that the relation ＝⁻ indeed implements the idea
announced in the comment above.

\begin{code}

 private
  ＝⁻-behaviour : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
               → (𝕍-set f ＝⁻ 𝕍-set g)
               ＝ ( ((a : A) → ∃ b ꞉ B , f a ＝⁻ g b)
                  × ((b : B) → ∃ a ꞉ A , f a ＝⁻ g b))
  ＝⁻-behaviour {A} {B} f g =
   (𝕍-set f ＝⁻ 𝕍-set g)          ＝⟨ ⦅1⦆ ⟩
   (＝⁻-aux₂ f r (𝕍-set g) holds) ＝⟨ ⦅2⦆ ⟩
   T                              ∎
    where
     T : 𝓤 ̇
     T = ((a : A) → ∃ b ꞉ B , f a ＝⁻ g b)
       × ((b : B) → ∃ a ꞉ A , f a ＝⁻ g b)
     r : A → 𝕍 → Ω 𝓤
     r a y = f a ＝⁻[Ω] y
     ⦅1⦆ = ap _holds (happly (pr₂ ＝⁻[Ω]-packaged f r) (𝕍-set g))
     ⦅2⦆ = ap _holds (＝⁻-aux₂-behaviour f r g)

\end{code}

Finally, we show that ＝⁻ and ＝ are equivalent, making 𝕍 a locally small type.

\begin{code}

 ＝⁻-to-＝ : {x y : 𝕍} → x ＝⁻ y → x ＝ y
 ＝⁻-to-＝ {x} {y} =
  𝕍-prop-induction (λ u → ((v : 𝕍) → u ＝⁻ v → u ＝ v))
                   (λ _ → Π₂-is-prop fe (λ _ _ → 𝕍-is-large-set))
                   (λ {A} f r → 𝕍-prop-simple-induction _
                                 (λ _ → Π-is-prop fe (λ _ → 𝕍-is-large-set))
                                 (λ {B} g → h f g r))
                   x y
   where
    h : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
      → ((a : A) (v : 𝕍) → f a ＝⁻ v → f a ＝ v)
      → 𝕍-set f ＝⁻ 𝕍-set g → 𝕍-set f ＝ 𝕍-set g
    h {A} {B} f g r e = 𝕍-set-ext f g (⦅1⦆ , ⦅2⦆)
     where
      u : (a : A) → ∃ b ꞉ B , f a ＝⁻ g b
      u = pr₁ (Idtofun (＝⁻-behaviour f g) e)
      v : (b : B) → ∃ a ꞉ A , f a ＝⁻ g b
      v = pr₂ (Idtofun (＝⁻-behaviour f g) e)
      ⦅1⦆ : (a : A) → ∃ b ꞉ B , g b ＝ f a
      ⦅1⦆ a = ∥∥-functor (λ (b , p) → b , ((r a (g b) p) ⁻¹)) (u a)
      ⦅2⦆ : (b : B) → ∃ a ꞉ A , f a ＝ g b
      ⦅2⦆ b = ∥∥-functor (λ (a , p) → a , r a (g b) p) (v b)

 ＝⁻-is-reflexive : {x : 𝕍} → x ＝⁻ x
 ＝⁻-is-reflexive {x} = 𝕍-prop-induction (λ - → - ＝⁻ -)
                                         (λ _ → ＝⁻-is-prop-valued)
                                         h x
  where
   h : {A : 𝓤 ̇ } (f : A → 𝕍)
     → ((a : A) → f a ＝⁻ f a)
     → 𝕍-set f ＝⁻ 𝕍-set f
   h {A} f r = Idtofun⁻¹ (＝⁻-behaviour f f)
                         ((λ a → ∣ a , r a ∣) , (λ a → ∣ a , r a ∣))

 ＝-to-＝⁻ : {x y : 𝕍} → x ＝ y → x ＝⁻ y
 ＝-to-＝⁻ refl = ＝⁻-is-reflexive

 ＝⁻-≃-＝ : {x y : 𝕍} → (x ＝⁻ y) ≃ (x ＝ y)
 ＝⁻-≃-＝ = logically-equivalent-props-are-equivalent
             ＝⁻-is-prop-valued
             𝕍-is-large-set
             ＝⁻-to-＝
             ＝-to-＝⁻

 𝕍-is-locally-small : is-locally-small 𝕍
 𝕍-is-locally-small x y = (x ＝⁻ y) , ＝⁻-≃-＝

 ＝⁻-is-transitive : {x y z : 𝕍} → x ＝⁻ y → y ＝⁻ z → x ＝⁻ z
 ＝⁻-is-transitive {x} {y} {z} u v = ＝-to-＝⁻ (＝⁻-to-＝ u ∙ ＝⁻-to-＝ v)

 ＝⁻-is-symmetric : {x y : 𝕍} → x ＝⁻ y → y ＝⁻ x
 ＝⁻-is-symmetric {x} {y} e = ＝-to-＝⁻ ((＝⁻-to-＝ e)⁻¹)

\end{code}

We now make use of the fact that 𝕍 is locally small by introducing a
small-valued membership relation on 𝕍.

\begin{code}

 _∈⁻[Ω]_ : 𝕍 → 𝕍 → Ω 𝓤
 _∈⁻[Ω]_ x = 𝕍-prop-simple-recursion
              (λ {A} f → (∃ a ꞉ A , f a ＝⁻ x) , ∃-is-prop) e
  where
   e : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
     → f ≲ g → (∃ a ꞉ A , f a ＝⁻ x) → (∃ b ꞉ B , g b ＝⁻ x)
   e {A} {B} f g s =
    ∥∥-rec ∃-is-prop
           (λ (a , p) → ∥∥-functor (λ (b , q)
                                      → b , ＝-to-＝⁻ (q ∙ ＝⁻-to-＝ p))
                                   (s a))

 _∈⁻_ : 𝕍 → 𝕍 → 𝓤  ̇
 x ∈⁻ y = (x ∈⁻[Ω] y) holds

 ∈⁻-for-𝕍-sets : (x : 𝕍) {A : 𝓤 ̇ } (f : A → 𝕍)
               → (x ∈⁻ 𝕍-set f) ＝ (∃ a ꞉ A , f a ＝⁻ x)
 ∈⁻-for-𝕍-sets x f = ap pr₁ (𝕍-prop-simple-recursion-computes _ _ f)

 ∈⁻-is-prop-valued : {x y : 𝕍} → is-prop (x ∈⁻ y)
 ∈⁻-is-prop-valued {x} {y} = holds-is-prop (x ∈⁻[Ω] y)

 ∈⁻-≃-∈ : {x y : 𝕍} → x ∈⁻ y ≃ x ∈ y
 ∈⁻-≃-∈ {x} {y} =
  𝕍-prop-simple-induction _ (λ _ → ≃-is-prop (λ _ _ → fe) ∈-is-prop-valued) h y
   where
    h : {A : 𝓤 ̇ } (f : A → 𝕍) → (x ∈⁻ 𝕍-set f) ≃ (x ∈ 𝕍-set f)
    h {A} f = x ∈⁻ 𝕍-set f          ≃⟨ ⦅1⦆ ⟩
              (∃ a ꞉ A , f a ＝⁻ x) ≃⟨ ⦅2⦆ ⟩
              (∃ a ꞉ A , f a ＝ x)  ≃⟨ ⦅3⦆ ⟩
              x ∈ 𝕍-set f           ■
     where
      ⦅1⦆ = idtoeq _ _ (∈⁻-for-𝕍-sets x f)
      ⦅2⦆ = ∃-cong pt (λ a → ＝⁻-≃-＝)
      ⦅3⦆ = idtoeq _ _ ((∈-for-𝕍-sets x f) ⁻¹)

 ∈⁻-to-∈ : {x y : 𝕍} → x ∈⁻ y → x ∈ y
 ∈⁻-to-∈ {x} {y} = ⌜ ∈⁻-≃-∈ ⌝

 ∈-to-∈⁻ : {x y : 𝕍} → x ∈ y → x ∈⁻ y
 ∈-to-∈⁻ {x} {y} = ⌜ ∈⁻-≃-∈ ⌝⁻¹

\end{code}
