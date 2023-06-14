\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Miscelanea
open import UF.Equiv

module TWA.Thesis.Chapter2.Sequences where

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → Y) → (ℕ → X) → (ℕ → Y)
map f α n = f (α n)

zipWith : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
        → (X → Y → Z) → (ℕ → X) → (ℕ → Y) → (ℕ → Z)
zipWith f α β n = f (α n) (β n)

head : {X : 𝓤 ̇ } → (ℕ → X) → X
head α = α 0

tail : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X)
tail α = α ∘ succ

_∶∶_ : {X : 𝓤 ̇ } → X → (ℕ → X) → (ℕ → X)
(h ∶∶ α) 0 = h
(h ∶∶ α) (succ n) = α n

_∼ⁿ_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ∼ⁿ β) n = (i : ℕ) → i < n → α i ＝ β i

seq-f-ucontinuous¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y)) → 𝓤 ⊔ 𝓥 ̇
seq-f-ucontinuous¹ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ δ ꞉ ℕ , ((x₁ x₂ : (ℕ → X))
 → (x₁ ∼ⁿ x₂) δ → (f x₁ ∼ⁿ f x₂) ϵ)

seq-f-ucontinuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                   → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
seq-f-ucontinuous² {𝓤} {𝓥} {𝓦} {X} {Y} f
 = (ϵ : ℕ) → Σ (δˣ , δʸ) ꞉ ℕ × ℕ ,
   ((x₁ x₂ : (ℕ → X)) (y₁ y₂ : (ℕ → Y))
 → (x₁ ∼ⁿ x₂) δˣ → (y₁ ∼ⁿ y₂) δʸ → (f x₁ y₁ ∼ⁿ f x₂ y₂) ϵ)

seq-f-ucontinuous¹²-comp
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ }
 → (f : (ℕ → Z) → (ℕ → W))
 → (g : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous¹ f → seq-f-ucontinuous² g
 → seq-f-ucontinuous² λ x y → f (g x y)
seq-f-ucontinuous¹²-comp {_} {_} {_} {_} {X} {Y} {Z} {W}
 f g ϕᶠ ϕᵍ ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = pr₁ (ϕᵍ (pr₁ (ϕᶠ ϵ)))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ) → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f (g x₁ y₁) ∼ⁿ f (g x₂ y₂)) ϵ
  γ x₁ x₂ y₁ y₂ x∼ y∼
    = pr₂ (ϕᶠ ϵ) (g x₁ y₁) (g x₂ y₂)
        (pr₂ (ϕᵍ (pr₁ (ϕᶠ ϵ))) x₁ x₂ y₁ y₂ x∼ y∼)

seq-f-ucontinuousᴺ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
                   → 𝓤 ⊔ 𝓥  ̇
seq-f-ucontinuousᴺ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ (d , δ) ꞉ ℕ × ℕ ,
   ((x₁ x₂ : (ℕ → (ℕ → X)))
 → ((n : ℕ) → n < d → (x₁ n ∼ⁿ x₂ n) δ) → (f x₁ ∼ⁿ f x₂) ϵ)

\end{code}
