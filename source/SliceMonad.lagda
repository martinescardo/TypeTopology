Martin Escardo, 6th December 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT

module SliceMonad (𝓣 : Universe) where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

open import Slice 𝓣
open import SliceIdentityViaSIP 𝓣

\end{code}

Constructions:

\begin{code}

𝓕̇ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓕 X → 𝓕 Y
𝓕̇ f (P , φ) = P , f ∘ φ

_♯ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → 𝓕 Y) → (𝓕 X → 𝓕 Y)
_♯ f (P , φ ) = (Σ p ꞉ P , source (f (φ p))) ,
                (λ σ → family (f (φ (pr₁ σ))) (pr₂ σ))


μ : {X : 𝓤 ̇ } → 𝓕 (𝓕 X) → 𝓕 X
μ = id ♯

𝓕̇-id : {X : 𝓤 ̇ }
      → 𝓕̇ id ≡ id
𝓕̇-id {𝓤} {X} = refl {𝓤 ⊔ (𝓣 ⁺)} {𝓕 X → 𝓕 X}

𝓕̇-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
     → 𝓕̇ (g ∘ f) ≡ 𝓕̇ g ∘ 𝓕̇ f
𝓕̇-∘ f g = refl

η-natural : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
          → η ∘ f ≡ 𝓕̇ f ∘ η
η-natural f = refl

η-natural∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
           → η ∘ f ∼ 𝓕̇ f ∘ η
η-natural∼ f _ = refl

μ-natural∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
           → 𝓕̇ f ∘ μ ∼ μ ∘ 𝓕̇ (𝓕̇ f)
μ-natural∼ f _ = refl

μ-natural : funext (𝓣 ⁺ ⊔ 𝓤) (𝓣 ⁺ ⊔ 𝓥)
          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
          → 𝓕̇ f ∘ μ ≡ μ ∘ 𝓕̇ (𝓕̇ f)
μ-natural fe f = dfunext fe (μ-natural∼ f)


𝓕-unit-right⋍ : {X : 𝓤 ̇ } (l : 𝓕 X)
              → μ (𝓕̇ η l) ⋍ l
𝓕-unit-right⋍ {𝓤} {X} (P , φ) = e , refl
 where
  e : P × 𝟙 ≃ P
  e = 𝟙-rneutral

𝓕-unit-left⋍ : {X : 𝓤 ̇ } (l : 𝓕 X)
             → μ (η l) ⋍ l
𝓕-unit-left⋍ (P , φ) = e , refl
 where
  e : 𝟙 × P ≃ P
  e = 𝟙-lneutral

𝓕-unit-right∼ : is-univalent 𝓣 → {X : 𝓤 ̇ }
              → μ ∘ 𝓕̇ η ∼ id
𝓕-unit-right∼ {𝓤} ua {X} l = ⋍-gives-≡ ua (𝓕-unit-right⋍ {𝓤} {X} l)

𝓕-unit-left∼ : is-univalent 𝓣 → {X : 𝓤 ̇ }
              → μ ∘ η ∼ id
𝓕-unit-left∼ {𝓤} ua {X} l = ⋍-gives-≡ ua (𝓕-unit-left⋍ {𝓤} {X} l)

𝓕-assoc⋍ : {X : 𝓤 ̇ } (l : 𝓕 (𝓕 (𝓕 X))) → μ (μ l) ⋍ μ (𝓕̇ μ l)
𝓕-assoc⋍ (P , φ) = Σ-assoc , refl

𝓕-assoc∼ : is-univalent 𝓣 → {X : 𝓤 ̇ } → μ ∘ μ ∼ μ ∘ 𝓕̇ μ
𝓕-assoc∼ {𝓤} ua {X} l = ⋍-gives-≡ ua (𝓕-assoc⋍ {𝓤} {X} l)

𝓕-σ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × 𝓕 Y → 𝓕 (X × Y)
𝓕-σ (x , m) = 𝓕̇ (λ y → (x , y)) m

𝓕-τ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → 𝓕 X × Y → 𝓕 (X × Y)
𝓕-τ (l , y) = 𝓕̇ (λ x → (x , y)) l

𝓕-comm : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {l : 𝓕 X × 𝓕 Y}
       → μ (𝓕̇ 𝓕-σ (𝓕-τ l)) ⋍· μ (𝓕̇ 𝓕-τ (𝓕-σ l))
𝓕-comm = ×-comm , (λ z → refl)

𝓕-m : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → 𝓕 X × 𝓕 Y → 𝓕 (X × Y)
𝓕-m (l , m) = ((λ x → curry 𝓕-σ x m)♯) l

Kleisli-Law₀ : {X : 𝓤 ̇ } (l : 𝓕 X) → (η ♯) l ⋍ l
Kleisli-Law₀ (P , φ) = 𝟙-rneutral , refl

Kleisli-Law₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓕 Y) (x : X) → (f ♯) (η x) ⋍ f x
Kleisli-Law₁ f x = 𝟙-lneutral , refl

Kleisli-Law₂ : {X : 𝓥 ̇ } {Y : 𝓦 ̇ } {Z : 𝓣 ̇ } (f : X → 𝓕 Y) (g : Y → 𝓕 Z) (l : 𝓕 X)
             → (g ♯ ∘ f ♯) l ⋍ ((g ♯ ∘ f)♯) l
Kleisli-Law₂ f g l = Σ-assoc , refl

𝓕̇' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓕 X → 𝓕 Y
𝓕̇' f = (η ∘ f)♯

𝓕̇-agreement : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (l : 𝓕 X)
             → 𝓕̇' f l ⋍· 𝓕̇ f l
𝓕̇-agreement {𝓤} {𝓥} {X} {Y} f (P , φ) = 𝟙-rneutral , λ _ → refl

\end{code}
