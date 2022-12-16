Tom de Jong, ?? ─ ??
In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

TO DO: - Clean up lemma names
       - Input dates
       - Write comments

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

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
open import UF.Size
open import UF.Subsingletons-FunExt
open import UF.Subsingleton-Combinators

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

Notice that since 𝕍 is a type in 𝓤 ⁺ the type x ＝ y also lives in 𝓤 ⁺ whenever
x, y : 𝕍. However, as pointed out in the HoTT Book [Section 10.5, 1], it is
possible to define a 𝓤-small relation and prove it equivalent to the identity
type of 𝕍, making 𝕍 (essentially) locally 𝓤-small. This also allows us to define
a 𝓤-small membership relation.

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

   ρ₁ : {B : 𝓤 ̇ } → (B → 𝕍) → Ω 𝓤
   ρ₁ {B} g = (Ɐ a ∶ A , Ǝ b ∶ B , r a (g b) holds)
            ∧ (Ɐ b ∶ B , Ǝ a ∶ A , r a (g b) holds)

   τ₁' : {B' B : 𝓤 ̇} (g' : B' → 𝕍) (g : B → 𝕍) → g' ≈ g → ρ₁ g' holds → ρ₁ g holds
   τ₁' {B'} {B} g' g (s , t) (u , v) = ⦅1⦆ , ⦅2⦆
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

   τ₁ : {B' B : 𝓤 ̇} (g' : B' → 𝕍) (g : B → 𝕍) → g' ≈ g → ρ₁ g' ＝ ρ₁ g
   τ₁ {B'} {B} g' g e = Ω-extensionality fe pe (τ₁' g' g e) (τ₁' g g' (≈-sym e))

   ρ₂ : 𝕍 → Ω 𝓤
   ρ₂ = 𝕍-recursion (Ω-is-set fe pe) (λ g _ → ρ₁ g)
                    (λ g' g _ _ _ _ e → τ₁ g' g e)

   ρ₂-behaviour : {B : 𝓤 ̇ } (g : B → 𝕍) → ρ₂ (𝕍-set g) ＝ ρ₁ g
   ρ₂-behaviour g =
    𝕍-recursion-computes (Ω-is-set fe pe) (λ g₁ _ → ρ₁ g₁)
                         (λ g' g _ _ _ _ e → τ₁ g' g e)
                         g (λ _ → 𝟙 , 𝟙-is-prop)

  τ' : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
     → (r₁ : A → 𝕍 → Ω 𝓤) (r₂ : B → 𝕍 → Ω 𝓤)
     → ((a : A) → ∃ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
     → ((b : B) → ∃ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
     → {C : 𝓤 ̇ } (h : C → 𝕍) → ρ₁ f r₁ h holds → ρ₁ g r₂ h holds
  τ' {A} {B} f g r₁ r₂ s t {C} h (u , v) = ⦅1⦆ , ⦅2⦆
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

  τ : {A B : 𝓤 ̇} (f : A → 𝕍) (g : B → 𝕍)
      (r₁ : A → 𝕍 → Ω 𝓤) (r₂ : B → 𝕍 → Ω 𝓤)
    → ((a : A) → ∃ b ꞉ B , (f a ＝ g b) × (r₁ a ＝ r₂ b))
    → ((b : B) → ∃ a ꞉ A , (g b ＝ f a) × (r₂ b ＝ r₁ a))
    → f ≈ g → ρ₂ f r₁ ＝ ρ₂ g r₂
  τ {A} {B} f g r₁ r₂ IH₁ IH₂ _ =
   dfunext fe (𝕍-prop-simple-induction (λ x → ρ₂ f r₁ x ＝ ρ₂ g r₂ x)
                                       (λ _ → Ω-is-set fe pe)
                                       σ)
    where
     σ : {C : 𝓤 ̇ } (h : C → 𝕍) → ρ₂ f r₁ (𝕍-set h) ＝ ρ₂ g r₂ (𝕍-set h)
     σ h = ρ₂ f r₁ (𝕍-set h) ＝⟨ ρ₂-behaviour f r₁ h ⟩
           ρ₁ f r₁ h         ＝⟨ e ⟩
           ρ₁ g r₂ h         ＝⟨ (ρ₂-behaviour g r₂ h) ⁻¹ ⟩
           ρ₂ g r₂ (𝕍-set h) ∎
      where
       e = Ω-extensionality fe pe
            (τ' f g r₁ r₂ IH₁ IH₂ h)
            (τ' g f r₂ r₁ IH₂ IH₁ h)

  ＝⁻[Ω]-packaged : Σ ϕ ꞉ (𝕍 → 𝕍 → Ω 𝓤) , ({A : 𝓤 ̇} (f : A → 𝕍)
                                           (r : A → 𝕍 → Ω 𝓤)
                                         → ϕ (𝕍-set f) ＝ ρ₂ f r)
  ＝⁻[Ω]-packaged =
   𝕍-recursion-with-computation (Π-is-set fe (λ _ → Ω-is-set fe pe)) ρ₂ τ

 _＝⁻[Ω]_ : 𝕍 → 𝕍 → Ω 𝓤
 _＝⁻[Ω]_ = pr₁ ＝⁻[Ω]-packaged

 _＝⁻_ : 𝕍 → 𝕍 → 𝓤 ̇
 x ＝⁻ y = (x ＝⁻[Ω] y) holds

 ＝⁻-is-prop-valued : {x y : 𝕍} → is-prop (x ＝⁻ y)
 ＝⁻-is-prop-valued {x} {y} = holds-is-prop (x ＝⁻[Ω] y)

 private
  ＝⁻-behaviour : {A B : 𝓤 ̇ } (f : A → 𝕍) (g : B → 𝕍)
               → (𝕍-set f ＝⁻ 𝕍-set g)
               ＝ ( ((a : A) → ∃ b ꞉ B , f a ＝⁻ g b)
                  × ((b : B) → ∃ a ꞉ A , f a ＝⁻ g b))
  ＝⁻-behaviour {A} {B} f g =
   (𝕍-set f ＝⁻ 𝕍-set g)    ＝⟨ ⦅1⦆ ⟩
   (ρ₂ f r (𝕍-set g) holds) ＝⟨ ⦅2⦆ ⟩
   T                        ∎
    where
     T : 𝓤 ̇
     T = ((a : A) → ∃ b ꞉ B , f a ＝⁻ g b)
       × ((b : B) → ∃ a ꞉ A , f a ＝⁻ g b)
     r : A → 𝕍 → Ω 𝓤
     r a y = f a ＝⁻[Ω] y
     ⦅1⦆ = ap _holds (happly (pr₂ ＝⁻[Ω]-packaged f r) (𝕍-set g))
     ⦅2⦆ = ap _holds (ρ₂-behaviour f r g)

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
   h {A} f r = back-Idtofun (＝⁻-behaviour f f)
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
              x ∈ 𝕍-set f ■
     where
      ⦅1⦆ = idtoeq _ _ (∈⁻-for-𝕍-sets x f)
      ⦅2⦆ = ∃-cong pt (λ a → ＝⁻-≃-＝)
      ⦅3⦆ = idtoeq _ _ ((∈-for-𝕍-sets x f) ⁻¹)

 ∈⁻-to-∈ : {x y : 𝕍} → x ∈⁻ y → x ∈ y
 ∈⁻-to-∈ {x} {y} = ⌜ ∈⁻-≃-∈ ⌝

 ∈-to-∈⁻ : {x y : 𝕍} → x ∈ y → x ∈⁻ y
 ∈-to-∈⁻ {x} {y} = ⌜ ∈⁻-≃-∈ ⌝⁻¹

\end{code}
