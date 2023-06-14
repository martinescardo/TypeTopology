{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import MLTT.Two-Properties

module TWA.Thesis.Chapter5.Prelude where

_≡_ = Id

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → Y) → (ℕ → X) → (ℕ → Y)
map f α n = f (α n)

map2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
     → (X → Y → Z) → (ℕ → X) → (ℕ → Y) → (ℕ → Z)
map2 f α β n = f (α n) (β n)

_^⟨succ_⟩ : (X : 𝓤 ̇ ) → ℕ → 𝓤 ̇ 
_^⟨succ_⟩ X 0 = X
_^⟨succ_⟩ X (succ n) = X × X ^⟨succ n ⟩

vec-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
        → (X → Y) → X ^⟨succ n ⟩ → Y ^⟨succ n ⟩
vec-map {𝓤} {𝓥} {X} {Y} {0} f v = f v
vec-map {𝓤} {𝓥} {X} {Y} {succ n} f (v , vs) = f v , vec-map f vs

head : {X : 𝓤 ̇ } → (ℕ → X) → X
head α = α 0

tail : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X)
tail α = α ∘ succ

_∶∶_ : {X : 𝓤 ̇ } → X → (ℕ → X) → (ℕ → X)
(h ∶∶ α) 0 = h
(h ∶∶ α) (succ n) = α n

head-tail-sim : {X : 𝓤 ̇ } → (α : ℕ → X) → α ∼ (head α ∶∶ tail α)
head-tail-sim α 0 = refl
head-tail-sim α (succ _) = refl

<ₙ : (ℕ → 𝓤 ̇ ) → ℕ → 𝓤 ̇
<ₙ P n = ∀ k → k < n → P k

<ₙ-succ : {P : ℕ → 𝓤 ̇ } (n : ℕ) → <ₙ P n → P n → <ₙ P (succ n)
<ₙ-succ 0 f Pn 0 k<n = Pn
<ₙ-succ {𝓤} {P} (succ n) f Pn k k<n
 = Cases (<-split k (succ n) k<n)
     (λ k<sn → f k k<sn)
     (λ t → transport P (t ⁻¹) Pn)

_≈_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇ 
(α ≈ β) = <ₙ (λ k → α k ≡ β k)

min𝟚-abcd : {a b c d : 𝟚} → a ≡ c → b ≡ d → min𝟚 a b ≡ min𝟚 c d
min𝟚-abcd {a} {b} {.a} {.b} refl refl = refl

×-≡ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → {x₁ x₂ : X} {y₁ y₂ : Y}
    → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
×-≡ {𝓤} {X} {𝓥} {Y} {x₁} {.x₁} {y₁} {.y₁} refl refl = refl
