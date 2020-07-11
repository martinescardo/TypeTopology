Martin Escardo, 6th December 2018.

Cf. The lifting monad.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Slice (𝓣 : Universe) where

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


open import UF-Base

{- TODO.
pullback-mediating : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
                     {f : A → C} {g : B → C}
                     {T : 𝓤' ̇ }
                     (φ : T → A) (γ : T → B)
                   → f ∘ φ  ∼ g ∘ γ
                   → ∃! h ꞉ T → pullback f g , (ppr₁ ∘ h ∼ φ) × (ppr₂ ∘ h ∼ γ)
pullback-mediating {𝓤} {𝓥} {𝓦} {𝓤'} {A} {B} {C} {f} {g} {T} φ γ r = (h , p , q) , o
 where
  h : T → pullback f g
  h t = φ t , γ t , r t
  p : ppr₁ ∘ h ∼ φ
  p t = refl
  q : ppr₂ ∘ h ∼ γ
  q t = refl
  o : (σ : Σ h' ꞉ T → pullback f g , (ppr₁ ∘ h' ∼ φ) × (ppr₂ ∘ h' ∼ γ)) → h , p , q ≡ σ
  o (h' , p' , q') = to-Σ-≡ ({!!} , {!!})
-}


pbf : {X : 𝓣 ̇ } {Y : 𝓣 ̇ } → (X → Y) → (𝓕 Y → 𝓕 X)
pbf f (Y , γ) = pullback f γ , ppr₁

∑ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓕 X → 𝓕 Y)
∑ f (X , φ) = X , f ∘ φ

{-

∏ : {X : {!!} ̇ } {Y : {!!} ̇ } → (X → Y) → (𝓕 X → 𝓕 Y)
∏ f (X , φ) = {!!}

-}


open import UF-Classifiers
open import UF-Equiv
open import UF-FunExt
open import UF-Univalence

𝓕-equiv-particular : is-univalent 𝓣 → funext 𝓣 (𝓣 ⁺)
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
  fe = FunExt-from-Univalence ua
  φ : 𝓕 X → Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣
  φ (I , φ) = fiber φ , I , ≃-sym (total-fiber-is-domain φ)
  ψ : (Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣) → 𝓕 X
  ψ (A , I , (f , e)) = I , pr₁ ∘ f
  φψ : (σ : Σ A ꞉ (X → 𝓣 ⊔ 𝓤 ̇ ), (Σ A) has-size 𝓣) → φ (ψ σ) ≡ σ
  φψ (A , I , (f , e)) = p
   where
    h : (x : X) → fiber (pr₁ ∘ f) x ≃ A x
    h x = (Σ i ꞉ I , pr₁ (f i) ≡ x) ≃⟨ Σ-change-of-variable (λ (σ : Σ A) → pr₁ σ ≡ x) f e ⟩
          (Σ σ ꞉ Σ A , pr₁ σ ≡ x)   ≃⟨ fiber-equiv x ⟩
          A x                          ■
    p : fiber (pr₁ ∘ f) , I , ≃-sym (total-fiber-is-domain (pr₁ ∘ f)) ≡ A , I , f , e
    p = to-Σ-≡ (dfunext (fe 𝓤 ((𝓣 ⊔ 𝓤) ⁺)) (λ x → eqtoid (ua (𝓣 ⊔ 𝓤)) (fiber (pr₁ ∘ f) x) (A x) (h x)) ,
                has-size-is-prop ua (Σ A) 𝓣 _ (I , f , e))
  ψφ : (l : 𝓕 X) → ψ (φ l) ≡ l
  ψφ (I , φ) = ap (λ - → I , -) (dfunext (fe 𝓣 𝓤) (λ i → refl))

\end{code}
