Martin Escardo 31 Jan 2019

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Slice.Algebras
        (𝓣 : Universe)
       where

open import UF.Base
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt

open import Slice.Slice 𝓣
open import Slice.IdentityViaSIP 𝓣
open import Slice.Monad 𝓣

double-𝓕-charac : (X : 𝓤 ̇ )
                → 𝓕 (𝓕 X) ≃ (Σ I ꞉ 𝓣 ̇ , (Σ J ꞉ (I → 𝓣 ̇ ), ((i : I) → J i → X)))
double-𝓕-charac X = Σ-cong (γ X)
 where
  γ : (X : 𝓤 ̇ ) (I : 𝓣 ̇ ) → (I → 𝓕 X) ≃ (Σ J ꞉ (I → 𝓣 ̇ ), ((i : I) → J i → X))
  γ X I = (I → Σ J ꞉ 𝓣 ̇ , (J → X))               ≃⟨ ΠΣ-distr-≃ ⟩
          (Σ J ꞉ (I → 𝓣 ̇ ), ((i : I) → J i → X)) ■

𝓕-algebra : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓕-algebra X = Σ s ꞉ (𝓕 X → X), (s ∘ η ∼ id) × (s ∘ μ ∼ s ∘ 𝓕̇ s)

free-𝓕-algebra : is-univalent 𝓣 → (X : 𝓤 ̇ ) → 𝓕-algebra (𝓕 X)
free-𝓕-algebra ua X = μ , 𝓕-unit-left∼ ua , 𝓕-assoc∼ ua

joinop : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
joinop X = {I : 𝓣 ̇ } → (I → X) → X

𝓕-alg-Law₀ : {X : 𝓤 ̇ } → joinop X → 𝓤 ̇
𝓕-alg-Law₀ {𝓤} {X} ∐ = (x : X) → ∐ (λ (i : 𝟙) → x) ＝ x

𝓕-alg-Law₁ : {X : 𝓤 ̇ } → joinop X → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓕-alg-Law₁ {𝓤} {X} ∐ = (I : 𝓣 ̇ ) (J : I → 𝓣 ̇ ) (f : Σ J → X)
                     → ∐ f ＝ ∐ (λ i → ∐ (λ j → f (i , j)))


𝓕-alg : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓕-alg X = Σ ∐ ꞉ joinop X , 𝓕-alg-Law₀ ∐ × 𝓕-alg-Law₁ ∐

⋁ : {X : 𝓤 ̇ } → (𝓕 X → X) → joinop X
⋁ s {I} f = s (I , f)

∐̇ : {X : 𝓤 ̇ } → 𝓕-algebra X → joinop X
∐̇ (s , _) = ⋁ s

∐ : {X : 𝓤 ̇ } → 𝓕-alg X → joinop X
∐ (∐ , κ , ι) = ∐

law₀ : {X : 𝓤 ̇ } (a : 𝓕-alg X) → 𝓕-alg-Law₀ (∐ a)
law₀ (∐ , κ , ι) = κ

law₁ : {X : 𝓤 ̇ } (a : 𝓕-alg X) → 𝓕-alg-Law₁ (∐ a)
law₁ (∐ , κ , ι) = ι

𝓕-morphism-charac : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    (s : 𝓕 X → X) (t : 𝓕 Y → Y)
                    (h : X → Y)

                  → (h ∘ s ∼ t ∘ 𝓕̇ h)
                  ≃ ({I : 𝓣 ̇ } (f : I → X) → h (⋁ s f) ＝ ⋁ t (h ∘ f))
𝓕-morphism-charac s t h = qinveq (λ H {I} f → H (I , f))
                                 ((λ {π (I , f) → π {I} f}) ,
                                  (λ _ → refl) ,
                                  (λ _ → refl))


𝓕-algebra-gives-alg : {X : 𝓤 ̇ } → 𝓕-algebra X → 𝓕-alg X
𝓕-algebra-gives-alg (s , unit , assoc) =
                    ⋁ s ,
                    unit ,
                    (λ I J f → assoc (I , (λ i → J i , (λ j → f (i , j)))))

𝓕-alg-gives-algebra : {X : 𝓤 ̇ } → 𝓕-alg X → 𝓕-algebra X
𝓕-alg-gives-algebra {𝓤} {X} (∐ , unit , ι) = s , unit , assoc
 where
  s : 𝓕 X → X
  s (I , f) = ∐ f
  assoc : s ∘ μ ∼ s ∘ 𝓕̇ s
  assoc (I , g) = ι I (pr₁ ∘ g) λ { (i , j) → pr₂ (g i) j }

𝓕-alg-charac : {X : 𝓤 ̇ } → 𝓕-algebra X ≃ 𝓕-alg X
𝓕-alg-charac = qinveq 𝓕-algebra-gives-alg (𝓕-alg-gives-algebra , ((λ _ → refl) , (λ _ → refl)))

Π-is-alg : funext 𝓤 𝓥
         → {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
         → ((x : X) → 𝓕-alg (A x)) → 𝓕-alg (Π A)
Π-is-alg {𝓤} {𝓥} fe {X} A α = ∐· , l₀ , l₁
 where
  ∐· : {I : 𝓣 ̇ } → (I → Π A) → Π A
  ∐· f x = ∐ (α x) (λ i → f i x)
  l₀ : (φ : Π A) → ∐· (λ i → φ) ＝ φ
  l₀ φ = dfunext fe (λ x → law₀ (α x) (φ x))
  l₁ : (I : 𝓣 ̇ ) (J : I → 𝓣 ̇ ) (f : Σ J → Π A)
    → ∐· f ＝ ∐· (λ i → ∐· (λ j → f (i , j)))
  l₁ I J f = dfunext fe (λ x → law₁ (α x) I J (λ σ → f σ x))

universe-is-algebra-Σ : is-univalent 𝓣 → 𝓕-alg (𝓣 ̇ )
universe-is-algebra-Σ ua = sum , k , ι
 where
  sum : {I : 𝓣 ̇ } → (I → 𝓣 ̇ ) → 𝓣 ̇
  sum = Σ
  k : (X : 𝓣 ̇ ) → Σ (λ i → X) ＝ X
  k X = eqtoid ua (𝟙 × X) X 𝟙-lneutral
  ι : (I : 𝓣 ̇ ) (J : I → 𝓣 ̇ ) (f : Σ J → 𝓣 ̇ )
    → Σ f ＝ Σ (λ i → Σ (λ j → f (i , j)))
  ι I J f = eqtoid ua _ _ Σ-assoc

universe-is-algebra-Π : is-univalent 𝓣 → 𝓕-alg (𝓣 ̇ )
universe-is-algebra-Π ua = prod , k , ι
 where
  fe : funext 𝓣 𝓣
  fe = univalence-gives-funext ua
  prod : {I : 𝓣 ̇ } → (I → 𝓣 ̇ ) → 𝓣 ̇
  prod = Π
  k : (X : 𝓣 ̇ ) → Π (λ i → X) ＝ X
  k X = eqtoid ua (𝟙 → X) X (≃-sym (𝟙→ (univalence-gives-funext ua)))
  ι : (I : 𝓣 ̇ ) (J : I → 𝓣 ̇ ) (f : Σ J → 𝓣 ̇ )
    → Π f ＝ Π (λ i → Π (λ j → f (i , j)))
  ι I J f = eqtoid ua _ _ (curry-uncurry' fe fe)

\end{code}
