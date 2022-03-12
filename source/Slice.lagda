Martin Escardo, 6th December 2018.

Cf. The lifting monad.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

module Slice (𝓣 : Universe) where

open import UF-Base
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Subsingletons

𝓕 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
𝓕 X = Σ I ꞉ 𝓣 ̇ , (I → X)

source : {X : 𝓤 ̇ } → 𝓕 X → 𝓣 ̇
source (I , φ) = I

family : {X : 𝓤 ̇ } (l : 𝓕 X) → source l → X
family (I , φ) = φ

η : {X : 𝓤 ̇ } → X → 𝓕 X
η x = 𝟙 , (λ _ → x)

SIGMA : {X : 𝓤 ̇ } → 𝓕  X → 𝓣 ̇
SIGMA (I , φ) = I

PI : {X : 𝓤 ̇ } → 𝓕  X → 𝓣 ⊔ 𝓤 ̇
PI {𝓤} {X} (I , φ) = Σ s ꞉ (X → I) , φ ∘ s ≡ id

pullback : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
         → (A → C) → (B → C) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
pullback f g = Σ x ꞉ domain f , Σ y ꞉ domain g , f x ≡ g y

ppr₁ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
       {f : A → C} {g : B → C}
     → pullback f g → A
ppr₁ (x , y , p) = x

ppr₂ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
       {f : A → C} {g : B → C}
     → pullback f g → B
ppr₂ (x , y , p) = y

ppr₃ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
       {f : A → C} {g : B → C}
     → (z : pullback f g) → f (ppr₁ z) ≡ g (ppr₂ z)
ppr₃ (x , y , p) = p

to-span : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
          (f : A → C) (g : B → C)
          (X : 𝓤' ̇ )
        → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ̇
to-span {𝓤} {𝓥} {𝓦} {𝓤'} {A} {B} {C} f g X =
 Σ k ꞉ (X → A) , Σ l ꞉ (X → B) , (f ∘ k ∼ g ∘ l)

→-pullback-≃ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
               (f : A → C) (g : B → C)
               (X : 𝓤' ̇ )
             → funext 𝓤' (𝓤 ⊔ 𝓥 ⊔ 𝓦)
             → (X → pullback f g) ≃ to-span f g X
→-pullback-≃ {𝓤} {𝓥} {𝓦} {𝓤̇ } {A} {B} {C} f g X fe =
 (X → pullback f g)                              ≃⟨ i ⟩
 (X → Σ p ꞉ A × B , f (pr₁ p) ≡ g (pr₂ p))       ≃⟨ ii ⟩
 (Σ j ꞉ (X → A × B) , f ∘ pr₁ ∘ j ∼ g ∘ pr₂ ∘ j) ≃⟨ iii ⟩
 to-span f g X                                   ■
  where
   i   = Π-cong fe fe X
          (λ _ → pullback f g)
          (λ _ → Σ p ꞉ A × B , f (pr₁ p) ≡ g (pr₂ p))
          (λ x → ≃-sym Σ-assoc)
   ii  = ΠΣ-distr-≃
   iii = qinveq ϕ (ψ , (λ x → refl) , (λ x → refl))
    where
     ϕ : (Σ j ꞉ (X → A × B) , f ∘ pr₁ ∘ j ∼ g ∘ pr₂ ∘ j)
       → to-span f g X
     ϕ (j , H) = (pr₁ ∘ j , pr₂ ∘ j , H)

     ψ : to-span f g X
       → (Σ j ꞉ (X → A × B) , f ∘ pr₁ ∘ j ∼ g ∘ pr₂ ∘ j)
     ψ (k , l , H) = ((λ x → (k x , l x)) , H)

pbf : {X : 𝓣 ̇ } {Y : 𝓣 ̇ } → (X → Y) → (𝓕 Y → 𝓕 X)
pbf f (Y , γ) = pullback f γ , ppr₁

∑ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓕 X → 𝓕 Y)
∑ f (A , φ) = A , f ∘ φ

-- Using Proposition 2.3 of
-- https://ncatlab.org/nlab/show/locally+cartesian+closed+category
∏ : {X : 𝓣 ̇ } {Y : 𝓣 ̇ } → (X → Y) → (𝓕 X → 𝓕 Y)
∏ {X} {Y} f (E , φ) = pullback k l , ppr₁
 where
  A : 𝓣 ̇
  A = Y

  B : 𝓣 ̇
  B = Σ τ ꞉ (X → E) , f ∼ f ∘ φ ∘ τ

  C : 𝓣 ̇
  C = Σ σ ꞉ (X → X) , f ∼ f ∘ σ

  k : Y → C
  k y = (id , λ x → refl)

  l : B → C
  l (τ , H) = (φ ∘ τ , H)

open import UF-Classifiers
open import UF-Equiv
open import UF-FunExt
open import UF-Univalence

𝓕-equiv-particular : is-univalent 𝓣
                   → funext 𝓣 (𝓣 ⁺)
                   → (X : 𝓣 ̇ ) → 𝓕 X ≃ (X → 𝓣 ̇ )
𝓕-equiv-particular = map-classification

open import UF-Size
open import UF-Base
open import UF-Equiv-FunExt
open import UF-UA-FunExt
open import UF-UniverseEmbedding
open import UF-EquivalenceExamples

𝓕-equiv : Univalence →  (X : 𝓤 ̇ ) → 𝓕 X ≃ (Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣)
𝓕-equiv {𝓤} ua X = qinveq φ (ψ , ψφ , φψ)
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  φ : 𝓕 X → Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣
  φ (I , φ) = fiber φ , I , ≃-sym (total-fiber-is-domain φ)

  ψ : (Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣) → 𝓕 X
  ψ (A , I , (f , e)) = I , pr₁ ∘ f

  φψ : (σ : Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣) → φ (ψ σ) ≡ σ
  φψ (A , I , (f , e)) = p
   where
    h : (x : X) → fiber (pr₁ ∘ f) x ≃ A x
    h x = (Σ i ꞉ I , pr₁ (f i) ≡ x) ≃⟨ Σ-change-of-variable (λ (σ : Σ A) → pr₁ σ ≡ x) f e ⟩
          (Σ σ ꞉ Σ A , pr₁ σ ≡ x)   ≃⟨ pr₁-fiber-equiv x ⟩
          A x                       ■

    p : fiber (pr₁ ∘ f) , I , ≃-sym (total-fiber-is-domain (pr₁ ∘ f)) ≡ A , I , f , e
    p = to-Σ-≡ (dfunext (fe 𝓤 ((𝓣 ⊔ 𝓤) ⁺)) (λ x → eqtoid (ua (𝓣 ⊔ 𝓤)) (fiber (pr₁ ∘ f) x) (A x) (h x)) ,
                being-small-is-prop ua (Σ A) 𝓣 _ (I , f , e))
  ψφ : (l : 𝓕 X) → ψ (φ l) ≡ l
  ψφ (I , φ) = ap (λ - → I , -) (dfunext (fe 𝓣 𝓤) (λ i → refl))

\end{code}
