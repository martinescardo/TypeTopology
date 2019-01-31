
Martin Escardo 6th December 2018.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module FamiliesMonad where

open import UF-Base
open import UF-Subsingletons hiding (⊥)
open import UF-Embeddings
open import UF-FunExt
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Subsingletons-Equiv
open import UF-Retracts
open import UF-Univalence
open import UF-EquivalenceExamples
open import UF-StructureIdentityPrinciple
open import UF-UA-FunExt

module _ (𝓣 : Universe) where

 𝓕 : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓕 X = Σ \(P : 𝓣 ̇) → P → X

 η : {X : 𝓤 ̇} → X → 𝓕 X
 η x = 𝟙 , (λ _ → x)

 source : {X : 𝓤 ̇} → 𝓕 X → 𝓣 ̇
 source (P , φ) = P

 family : {X : 𝓤 ̇} (l : 𝓕  X) → source l → X
 family (P ,  φ) = φ

 _⋍_ : {X : 𝓤 ̇} → 𝓕 X → 𝓕 X → 𝓣 ⊔ 𝓤 ̇
 l ⋍ m = Σ \(e : source l ≃ source m) → family l ≡ family m ∘ eqtofun e

 module _ (ua : is-univalent 𝓣)
          (X : 𝓤 ̇)
        where

  open gsip 𝓣 (𝓣 ⊔ 𝓤) ua
            (λ P → P → X)
            (λ {l m (f , e) → family l ≡ family m ∘ f})
            (λ l → refl)
            (λ P ε δ → id)
            (λ A τ υ → refl-left-neutral)

  𝓕-identity : (l m : 𝓕 X) → (l ≡ m) ≃ (l ⋍ m)
  𝓕-identity = ≡-is-≃ₛ'

  η-is-embedding : funext 𝓣 𝓤 → is-embedding (η {𝓤} {X})
  η-is-embedding fe = embedding-criterion' η c
    where
     a : (𝟙 ≃ 𝟙) ≃ 𝟙
     a = (𝟙 ≃ 𝟙) ≃⟨ ≃-sym (is-univalent-≃ ua 𝟙 𝟙) ⟩
         (𝟙 ≡ 𝟙) ≃⟨ 𝟙-≡-≃ 𝟙 (funext-from-univalence ua) (propext-from-univalence ua) 𝟙-is-prop ⟩
         𝟙       ■
     b : (x y : X) → ((λ (_ : 𝟙) → x) ≡ (λ (_ : 𝟙) → y)) ≃ (x ≡ y)
     b x y = ((λ _ → x) ≡ (λ _ → y)) ≃⟨ ≃-funext fe (λ _ → x) (λ _ → y) ⟩
             (𝟙 → x ≡ y)             ≃⟨ ≃-sym (𝟙→ fe) ⟩
             (x ≡ y)                 ■
     c : (x y : X) → (η x ≡ η y) ≃ (x ≡ y)
     c x y = (η x ≡ η y)                       ≃⟨ 𝓕-identity (η x) (η y) ⟩
             (𝟙 ≃ 𝟙) × ((λ _ → x) ≡ (λ _ → y)) ≃⟨ ×-cong a (b x y) ⟩
             𝟙 × (x ≡ y)                       ≃⟨ 𝟙-lneutral ⟩
             (x ≡ y)                           ■

 _♯ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → 𝓕 Y) → (𝓕 X → 𝓕 Y)
 _♯ f (P , φ) = (Σ \(p : P) → source (f (φ p))) ,
                 λ σ → family (f (φ (pr₁ σ))) (pr₂ σ)

 μ : {X : 𝓤 ̇} → 𝓕 (𝓕 X) → 𝓕 X
 μ = id ♯

 𝓕→ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓕 X → 𝓕 Y
 𝓕→ f (P , φ) = P , f ∘ φ

 η-natural : {X : 𝓤 ̇} {Y : 𝓤 ̇} (f : X → Y) → 𝓕→ f ∘ η ∼ η ∘ f
 η-natural f _ = refl

 μ-natural : {X : 𝓤 ̇} {Y : 𝓤 ̇} (f : X → Y) → 𝓕→ f ∘ μ ∼ μ ∘ 𝓕→ (𝓕→ f)
 μ-natural f _ = refl

 𝓕-unit₀ : {X : 𝓤 ̇} (l : 𝓕 X) → μ (𝓕→ η l) ⋍ l
 𝓕-unit₀ (P , φ) = e , refl
  where
   e : P × 𝟙 ≃ P
   e = 𝟙-rneutral

 𝓕-unit₁ : {X : 𝓤 ̇} (l : 𝓕 X) → μ (η l) ⋍ l
 𝓕-unit₁ (P , φ) = e , refl
  where
   e : 𝟙 × P ≃ P
   e = 𝟙-lneutral

 𝓕-assoc : {X : 𝓤 ̇} (l : 𝓕 (𝓕 (𝓕 X))) → μ (μ l) ⋍ μ (𝓕→ μ l)
 𝓕-assoc (P , φ) = Σ-assoc , refl

 kleisli-law₀ : {X : 𝓤 ̇} (l : 𝓕 X) → (η ♯) l ⋍ l
 kleisli-law₀ (P , φ) = 𝟙-rneutral , refl

 kleisli-law₁ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓕 Y) (x : X) → (f ♯) (η x) ⋍ f x
 kleisli-law₁ f x = 𝟙-lneutral , refl

 kleisli-law₂ : {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓣 ̇} (f : X → 𝓕 Y) (g : Y → 𝓕 Z) (l : 𝓕 X)
              → (g ♯ ∘ f ♯) l ⋍ ((g ♯ ∘ f)♯) l
 kleisli-law₂ f g l = Σ-assoc , refl

\end{code}

TODO. Complete or decide to delete this:

  𝓕-identity₃ : (x : X) (m : 𝓕 X)
               → (η x ≡ m) ≃ Σ \(c : is-singleton (source m)) → family m (pr₁ c) ≡ x
  𝓕-identity₃ x m = {!!}
   where
    a : (η x ≡ m) ≃ Σ \(p : 𝟙 ≃ source m) → (λ _ → x) ≡ family m ∘ pr₁ p
    a = ≡-is-≃ₛ' (η x) m
    b : (Σ \(p : 𝟙 ≃ source m) → (λ _ → x) ≡ family m ∘ pr₁ p)
      ≃ Σ \(c : is-singleton (source m)) → family m (pr₁ c) ≡ x
    b = {!!}

 _⋍'_ : {X : 𝓤 ̇} → 𝓕 X → 𝓕 X → 𝓣 ⊔ 𝓤 ̇
 l ⋍' m = Σ \(f : source l → source m) → is-equiv f × (family l ≡ family m ∘ f)

 𝓕-identity' : (l m : 𝓕 X) → (l ≡ m) ≃ (l ⋍ m)
 𝓕-identity' = ≡-is-≃ₛ
