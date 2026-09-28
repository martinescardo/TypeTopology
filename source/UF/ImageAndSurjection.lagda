Martin Escardo.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module UF.ImageAndSurjection (pt : propositional-truncations-exist) where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Hedberg
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

\end{code}

A main application of propositional truncations is to be able to
define images and surjections:

\begin{code}

open PropositionalTruncation pt

_∈image_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → (X → Y) → 𝓤 ⊔ 𝓥 ̇
y ∈image f = ∃ x ꞉ domain f , f x ＝ y

being-in-the-image-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y) (f : X → Y)
                           → is-prop (y ∈image f)
being-in-the-image-is-prop y f = ∃-is-prop

image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
image f = Σ y ꞉ codomain f , y ∈image f

complement-of-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
complement-of-image f = Σ y ꞉ codomain f , ¬(y ∈image f)

restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
            → image f → Y
restriction f (y , _) = y

corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → X → image f
corestriction f x = f x , ∣ x , refl ∣

image-factorization : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → f ∼ restriction f ∘ corestriction f
image-factorization f x = refl

restrictions-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-embedding (restriction f)
restrictions-are-embeddings f = pr₁-is-embedding (λ y → ∥∥-is-prop)

is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-surjection f = ∀ y → y ∈image f

being-surjection-is-prop : FunExt
                         → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                         → is-prop (is-surjection f)
being-surjection-is-prop fe f = Π-is-prop (fe _ _) (λ y → being-in-the-image-is-prop y f)


corestrictions-are-surjections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                               → is-surjection (corestriction f)
corestrictions-are-surjections f (y , s) = ∥∥-functor g s
 where
  g : (Σ x ꞉ domain f , f x ＝ y) → Σ x ꞉ domain f , corestriction f x ＝ (y , s)
  g (x , p) = x , to-Σ-＝ (p , ∥∥-is-prop _ _)

id-is-surjection : {X : 𝓤 ̇ } → is-surjection (𝑖𝑑 X)
id-is-surjection = λ y → ∣ y , refl ∣

_↠_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↠ Y = Σ f ꞉ (X → Y) , is-surjection f

⌞_⌟ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↠ Y) → (X → Y)
⌞ (f , i) ⌟ = f

⌞⌟-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (𝓯 : X ↠ Y) → is-surjection ⌞ 𝓯 ⌟
⌞⌟-is-surjection (f , i) = i

_is-image-of_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
Y is-image-of X = X ↠ Y

image-is-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → is-set Y
             → is-set (image f)
image-is-set f i = subsets-of-sets-are-sets _
                    (λ y → y ∈image f) i
                    (being-in-the-image-is-prop _ f)

vv-equivs-are-surjections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                          → is-vv-equiv f
                          → is-surjection f
vv-equivs-are-surjections f i y =
 pr₂ (lr-implication the-singletons-are-the-inhabited-propositions (i y))

surjective-embeddings-are-vv-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                    → is-embedding f
                                    → is-surjection f
                                    → is-vv-equiv f
surjective-embeddings-are-vv-equivs f e s y =
 rl-implication the-singletons-are-the-inhabited-propositions (e y , s y)

surjective-embeddings-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → is-embedding f
                                 → is-surjection f
                                 → is-equiv f
surjective-embeddings-are-equivs f e s =
 vv-equivs-are-equivs f (surjective-embeddings-are-vv-equivs f e s)

vv-equiv-iff-embedding-and-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                      → is-vv-equiv f
                                      ↔ is-embedding f × is-surjection f
vv-equiv-iff-embedding-and-surjection f =
  (λ i → vv-equivs-are-embeddings f i , vv-equivs-are-surjections f i) ,
  (λ (e , s) → surjective-embeddings-are-vv-equivs f e s)

pt-is-surjection : {X : 𝓤 ̇ } → is-surjection (λ (x : X) → ∣ x ∣)
pt-is-surjection t = ∥∥-rec ∥∥-is-prop (λ x → ∣ x , ∥∥-is-prop (∣ x ∣) t ∣) t


NatΣ-is-surjection : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                   → ((x : X) → is-surjection (ζ x))
                   → is-surjection (NatΣ ζ)
NatΣ-is-surjection A B ζ i (x , b) = γ
 where
  δ : (Σ a ꞉ A x , ζ x a ＝ b)
    → Σ (x' , a) ꞉ Σ A , (x' , ζ x' a) ＝ (x , b)
  δ (a , p) = (x , a) , (ap (x ,_) p)

  γ : ∃ (x' , a) ꞉ Σ A , (x' , ζ x' a) ＝ (x , b)
  γ = ∥∥-functor δ (i x b)

\end{code}

TODO. The converse of the above holds.

Surjections can be characterized as follows, modulo size:

\begin{code}

Surjection-Induction : ∀ {𝓦 𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
Surjection-Induction {𝓦} {𝓤} {𝓥} {X} {Y} f = (P : Y → 𝓦 ̇ )
                                             → ((y : Y) → is-prop (P y))
                                             → ((x : X) → P (f x))
                                             → (y : Y) → P y

surjection-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-surjection f
                     → Surjection-Induction {𝓦} f
surjection-induction f is P P-is-prop a y =
 ∥∥-rec
  (P-is-prop y)
  (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
  (is y)

surjection-induction-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                              → Surjection-Induction f
                              → is-surjection f
surjection-induction-converse f is' = is' (λ y → ∥ Σ (λ x → f x ＝ y) ∥)
                                      (λ y → ∥∥-is-prop)
                                      (λ x → ∣ x , refl ∣)

image-induction : ∀ {𝓦} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  (f : X → Y) (P : image f → 𝓦 ̇ )
                → (∀ y' → is-prop (P y'))
                → (∀ x → P (corestriction f x))
                → ∀ y' → P y'
image-induction f = surjection-induction
                     (corestriction f)
                     (corestrictions-are-surjections f)

set-right-cancellable : {X : 𝓤 ̇ } {A : 𝓥 ̇ } → (X → A) → 𝓤ω
set-right-cancellable f = {𝓦 : Universe}
                        → (B : 𝓦 ̇ )
                        → is-set B
                        → (g h : codomain f → B)
                        → g ∘ f ∼ h ∘ f
                        → g ∼ h

surjections-are-set-rc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (f : X → A)
                       → is-surjection f
                       → set-right-cancellable f
surjections-are-set-rc f f-is-surjection B B-is-set g h H =
 surjection-induction
  f
  f-is-surjection
  (λ a → g a ＝ h a)
  (λ a → B-is-set)
  (λ x → g (f x) ＝⟨ (H x) ⟩
         h (f x) ∎)

retractions-are-surjections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → has-section f
                            → is-surjection f
retractions-are-surjections {𝓤} {𝓥} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

pr₁-is-surjection : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                  → ((x : X) → ∥ A x ∥)
                  → is-surjection (λ (σ : Σ A) → pr₁ σ)
pr₁-is-surjection A s x = γ
 where
  δ : A x → Σ σ ꞉ Σ A , pr₁ σ ＝ x
  δ a = (x , a) , refl

  γ : ∃ σ ꞉ Σ A , pr₁ σ ＝ x
  γ = ∥∥-functor δ (s x)

pr₁-is-surjection-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                           → is-surjection (λ (σ : Σ A) → pr₁ σ)
                           → ((x : X) → ∥ A x ∥)
pr₁-is-surjection-converse A s x = γ
 where
  δ : (Σ σ ꞉ Σ A , pr₁ σ ＝ x) → A x
  δ ((.x , a) , refl) = a

  γ : ∥ A x ∥
  γ = ∥∥-functor δ (s x)

wconstant-maps-to-sets-have-propositional-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                                 → is-set Y
                                                 → (f : X → Y)
                                                 → wconstant f
                                                 → is-prop (image f)
wconstant-maps-to-sets-have-propositional-images
 {𝓤} {𝓥} {X} {Y} s f c (y , p) (y' , p') =
  to-subtype-＝ (λ _ → ∥∥-is-prop) (∥∥-rec s q p)
   where
    q : (Σ x ꞉ X , f x ＝ y) → y ＝ y'
    q u = ∥∥-rec s (h u) p'
     where
      h : (Σ x ꞉ X , f x ＝ y) → (Σ x' ꞉ X , f x' ＝ y') → y ＝ y'
      h (x , e) (x' , e') = y    ＝⟨ e ⁻¹ ⟩
                            f x  ＝⟨ c x x' ⟩
                            f x' ＝⟨ e' ⟩
                            y'   ∎

wconstant-map-to-set-factors-through-truncation-of-domain :
   {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-set Y
 → (f : X → Y)
 → wconstant f
 → Σ f' ꞉ (∥ X ∥ → Y) , f ∼ f' ∘ ∣_∣
wconstant-map-to-set-factors-through-truncation-of-domain
 {𝓤} {𝓥} {X} {Y} Y-is-set f f-is-wconstant = f' , h
  where
   i : is-prop (image f)
   i = wconstant-maps-to-sets-have-propositional-images
        Y-is-set f f-is-wconstant

   f'' : ∥ X ∥ → image f
   f'' = ∥∥-rec i (corestriction f)

   f' : ∥ X ∥ → Y
   f' = restriction f ∘ f''

   h : f ∼ f' ∘ ∣_∣
   h x = f x                               ＝⟨refl⟩
         restriction f (corestriction f x) ＝⟨ ρ    ⟩
         restriction f (f'' ∣ x ∣)          ＝⟨refl⟩
         f' ∣ x ∣                           ∎
    where
     ρ = ap (restriction f) (i (corestriction f x) (f'' ∣ x ∣))

factor-through-surjection : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                          → (f : X → A)
                          → is-surjection f
                          → {B : 𝓦 ̇ }
                          → is-set B
                          → (g : X → B)
                          → ((x y : X) → f x ＝ f y → g x ＝ g y)
                          → Σ h ꞉ (A → B) , h ∘ f ∼ g
factor-through-surjection {𝓤} {𝓥} {𝓦} {X} {A}
                          f f-is-surjection {B} B-is-set g g-respects-f = γ
 where
  φ : (a : A) → fiber f a → B
  φ _ (x , _) = g x

  φ-is-wconstant : (a : A) (u v : fiber f a) → φ a u ＝ φ a v
  φ-is-wconstant a (x , p) (y , q) = g-respects-f x y
                                      (f x ＝⟨ p ⟩
                                       a   ＝⟨ q ⁻¹ ⟩
                                       f y ∎)

  σ : (a : A) → Σ ψ ꞉ (∥ fiber f a ∥ → B) , φ a ∼ ψ ∘ ∣_∣
  σ a = wconstant-map-to-set-factors-through-truncation-of-domain
         B-is-set
         (φ a)
         (φ-is-wconstant a)

  h : A → B
  h a = pr₁ (σ a) (f-is-surjection a)

  H : h ∘ f ∼ g
  H x = h (f x)                               ＝⟨refl⟩
        pr₁ (σ (f x)) (f-is-surjection (f x)) ＝⟨ i ⟩
        pr₁ (σ (f x)) ∣ x , refl ∣             ＝⟨ ii ⟩
        φ (f x) (x , refl)                    ＝⟨refl⟩
        g x                                   ∎
         where
          i = ap (pr₁ (σ (f x))) (∥∥-is-prop (f-is-surjection (f x)) ∣ x , refl ∣)
          ii = (pr₂ (σ (f x)) (x , refl))⁻¹

  γ : Σ h ꞉ (A → B) , h ∘ f ∼ g
  γ = (h , H)

factor-through-surjection! : Fun-Ext
                           → {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                           → (f : X → A)
                           → is-surjection f
                           → {B : 𝓦 ̇ }
                           → is-set B
                           → (g : X → B)
                           → ((x y : X) → f x ＝ f y → g x ＝ g y)
                           → ∃! h ꞉ (A → B) , h ∘ f ∼ g
factor-through-surjection! fe {X} {A}
                           f f-is-surjection {B} B-is-set g g-respects-f = IV
 where
  I : (Σ h ꞉ (A → B) , h ∘ f ∼ g) → ∃! h ꞉ (A → B) , h ∘ f ∼ g
  I (h , H) = III
   where
    II : (k : A → B)
       → k ∘ f ∼ g
       → h ∼ k
    II k K = surjections-are-set-rc f f-is-surjection B B-is-set h k
              (λ x → h (f x) ＝⟨ H x ⟩
                     g x     ＝⟨ (K x)⁻¹ ⟩
                     k (f x) ∎)

    III : ∃! h ꞉ (A → B) , h ∘ f ∼ g
    III = (h , H) ,
          (λ (k , K) → to-subtype-＝
                        (λ - → Π-is-prop fe (λ x → B-is-set))
                        (dfunext fe (II k K)))

  IV : ∃! h ꞉ (A → B) , h ∘ f ∼ g
  IV = I (factor-through-surjection f f-is-surjection B-is-set g g-respects-f)

factor-through-image : Fun-Ext
                     → {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                     → (f : X → A)
                     → {B : 𝓦 ̇ }
                     → is-set B
                     → (g : X → B)
                     → ((x y : X) → f x ＝ f y → g x ＝ g y)
                     → ∃! h ꞉ (image f → B) , h ∘ corestriction f ∼ g
factor-through-image fe f  B-is-set g g-respects-f =
 factor-through-surjection!
  fe
  (corestriction f)
  (corestrictions-are-surjections f)
  B-is-set
  g
  r
 where
  r : ∀ x y → f x , ∣ x , refl ∣ ＝ f y , ∣ y , refl ∣ → g x ＝ g y
  r x y p = g-respects-f x y (ap pr₁ p)

\end{code}

Added by Tom de Jong on 4 December 2020.

\begin{code}

corestriction-of-embedding-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                          → is-embedding f
                                          → is-equiv (corestriction f)
corestriction-of-embedding-is-equivalence f e =
 surjective-embeddings-are-equivs f' e' s'
  where
   f' : domain f → image f
   f' = corestriction f
   s' : is-surjection f'
   s' = corestrictions-are-surjections f
   e' : is-embedding f'
   e' (y , p) = retract-of-prop γ (e y)
    where
     γ : fiber f' (y , p) ◁ fiber f y
     γ = Σ-retract (λ x → f' x ＝ y , p) (λ x → f x ＝ y) ϕ
      where
       ϕ : (x : domain f) → (f' x ＝ (y , p)) ◁ (f x ＝ y)
       ϕ x = ρ , σ , η
        where
         ρ : f x ＝ y → f' x ＝ (y , p)
         ρ q = to-subtype-＝ (λ y' → ∥∥-is-prop) q
         σ : f' x ＝ (y , p) → f x ＝ y
         σ q' = ap pr₁ q'
         η : ρ ∘ σ ∼ id
         η refl = to-Σ-＝ (refl , q)    ＝⟨ ap (λ - → to-Σ-＝ (refl , -)) h ⟩
                  to-Σ-＝ (refl , refl) ＝⟨refl⟩
                  refl                 ∎
          where
           q : ∣ x , refl ∣ ＝ ∣ x , refl ∣
           q = ∥∥-is-prop ∣ x , refl ∣ ∣ x , refl ∣
           h : q ＝ refl
           h = props-are-sets ∥∥-is-prop q refl

embedding-if-corestriction-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                          → is-equiv (corestriction f)
                                          → is-embedding f
embedding-if-corestriction-is-equivalence f i =
 embedding-closed-under-∼ f' f (∘-is-embedding e₁ e₂) H
  where
   f' : domain f → codomain f
   f' = pr₁ ∘ corestriction f
   H : f ∼ pr₁ ∘ corestriction f
   H x = refl
   e₁ : is-embedding (corestriction f)
   e₁ = equivs-are-embeddings (corestriction f) i
   e₂ : is-embedding pr₁
   e₂ = pr₁-is-embedding (λ y → ∥∥-is-prop)

\end{code}

Added 13 February 2020 by Tom de Jong.

\begin{code}

surjection-≃-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → is-surjection f
                   → image f ≃ Y
surjection-≃-image {𝓤} {𝓥} {X} {Y} f s =
 image f                       ≃⟨by-definition⟩
 (Σ y ꞉ Y , ∃ x ꞉ X , f x ＝ y) ≃⟨ Σ-cong γ ⟩
 (Σ y ꞉ Y , 𝟙)                 ≃⟨by-definition⟩
 Y × 𝟙                         ≃⟨ 𝟙-rneutral {𝓥} {𝓥} ⟩
 Y                             ■
  where
   γ : (y : Y) → (∃ x ꞉ X , f x ＝ y) ≃ 𝟙
   γ y = singleton-≃-𝟙 (pointed-props-are-singletons (s y) ∥∥-is-prop)

\end{code}

Added 18 December 2020 by Tom de Jong.

\begin{code}

∘-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
                → is-surjection f
                → is-surjection g
                → is-surjection (g ∘ f)
∘-is-surjection {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} σ τ z =
 ∥∥-rec ∥∥-is-prop γ₁ (τ z)
  where
   γ₁ : (Σ y ꞉ Y , g y ＝ z) → ∃ x ꞉ X , (g ∘ f) x ＝ z
   γ₁ (y , q) = ∥∥-functor γ₂ (σ y)
    where
     γ₂ : (Σ x ꞉ X , f x ＝ y) → Σ x ꞉ X , (g ∘ f) x ＝ z
     γ₂ (x , p) = (x , (g (f x) ＝⟨ ap g p ⟩
                        g y     ＝⟨ q ⟩
                        z       ∎))

equivs-are-surjections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                       → is-equiv f
                       → is-surjection f
equivs-are-surjections ((ρ , η) , (σ , ε)) y = ∣ ρ y , η y ∣

\end{code}
