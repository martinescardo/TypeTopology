[⇐ Index](../html/TWA.Thesis.index.html)

# Uniform continuity of sequence functions

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑) hiding (max)
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.FunExt
open import UF.Miscelanea
open import UF.Equiv

module TWA.Thesis.Chapter6.SequenceContinuity (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe

open import MLTT.Two-Properties

seq-f-ucontinuous¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → X) → (ℕ → Y))
                   → 𝓤 ⊔ 𝓥 ̇
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

map-ucontinuous' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
                 → (f : X → Y) → seq-f-ucontinuous¹ (map f)
map-ucontinuous' f ε = ε , λ α β α∼ⁿβ k k<ε → ap f (α∼ⁿβ k k<ε)

zipWith-ucontinuous' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → (f : X → X → Y)
                     → seq-f-ucontinuous² (zipWith f)
zipWith-ucontinuous' f ε
 = (ε , ε)
 , (λ α₁ α₂ β₁ β₂ α∼ β∼ k k<ϵ
    → ap (λ - → f - (β₁ k)) (α∼ k k<ϵ)
    ∙ ap (f (α₂ k)) (β∼ k k<ϵ))

seq-f-ucontinuous²-left : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                        → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                        → seq-f-ucontinuous² f
                        → (β : ℕ → Y)
                        → seq-f-ucontinuous¹ (λ α → f α β)
seq-f-ucontinuous²-left f ϕ β ε
 = pr₁ (pr₁ (ϕ ε))
 , λ α₁ α₂ α∼ → pr₂ (ϕ ε) α₁ α₂ β β α∼ (λ _ _ → refl)

seq-f-ucontinuous²-right : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                         → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
                         → seq-f-ucontinuous² f
                         → (α : ℕ → X)
                         → seq-f-ucontinuous¹ (f α)
seq-f-ucontinuous²-right f ϕ α ε
 = pr₂ (pr₁ (ϕ ε))
 , λ β₁ β₂ → pr₂ (ϕ ε) α α β₁ β₂ (λ _ _ → refl)

seq-f-ucontinuous²-both : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → (f : (ℕ → X) → (ℕ → X) → (ℕ → Y))
                        → seq-f-ucontinuous² f
                        → seq-f-ucontinuous¹ (λ α → f α α)
seq-f-ucontinuous²-both f ϕ ε
 = δ
 , λ α β α∼ᵐβ → pr₂ (ϕ ε) α β α β
     (λ i i<m → α∼ᵐβ i
       (<-≤-trans i δ₁ δ i<m (max-≤-upper-bound  δ₁ δ₂)))
     (λ i i<m → α∼ᵐβ i
       (<-≤-trans i δ₂ δ i<m (max-≤-upper-bound' δ₂ δ₁)))
 where
  δ₁ δ₂ δ : ℕ
  δ₁ = pr₁ (pr₁ (ϕ ε))
  δ₂ = pr₂ (pr₁ (ϕ ε))
  δ  = max δ₁ δ₂

seq-f-ucontinuous²-comp
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ } {T : 𝓤' ̇ }
 → (f : (ℕ → X) → (ℕ → W) → (ℕ → T))
 → (g : (ℕ → Y) → (ℕ → Z) → (ℕ → W))
 → seq-f-ucontinuous² f
 → seq-f-ucontinuous² g
 → (z : ℕ → Z) → seq-f-ucontinuous² λ x y → f x (g y z)
seq-f-ucontinuous²-comp
 {_} {_} {_} {_} {_} {X} {Y} {Z} {W} {T} f g ϕᶠ ϕᵍ z ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = (pr₁ (pr₁ (ϕᶠ ϵ))) , pr₁ (pr₁ (ϕᵍ (pr₂ (pr₁ (ϕᶠ ϵ)))))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ)
    → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f x₁ (g y₁ z) ∼ⁿ f x₂ (g y₂ z)) ϵ
  γ x₁ x₂ y₁ y₂ x₁∼x₂ y₁∼y₂
   = pr₂ (ϕᶠ ϵ) x₁ x₂ (g y₁ z) (g y₂ z)
       x₁∼x₂
       (pr₂ (ϕᵍ (pr₂ (pr₁ (ϕᶠ ϵ)))) y₁ y₂ z z
       y₁∼y₂
       (λ _ _ → refl))
 
seq-f-ucontinuous¹²-comp
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ }
 → (f : (ℕ → Z) → (ℕ → W))
 → (g : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous¹ f
 → seq-f-ucontinuous² g
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

seq-f-ucontinuous²¹-comp-left
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {W : 𝓣 ̇ }
 → (f : (ℕ → W) → (ℕ → Y) → (ℕ → Z))
 → (g : (ℕ → X) → (ℕ → W))
 → seq-f-ucontinuous² f
 → seq-f-ucontinuous¹ g
 → seq-f-ucontinuous² (λ x y → f (g x) y)
seq-f-ucontinuous²¹-comp-left {_} {_} {_} {_} {X} {Y} {Z} {W}
 f g ϕᶠ ϕᵍ ϵ = δ , γ
 where
  δ : ℕ × ℕ
  δ = pr₁ (ϕᵍ (pr₁ (pr₁ (ϕᶠ ϵ)))) , (pr₂ (pr₁ (ϕᶠ ϵ)))
  γ : (x₁ x₂ : ℕ → X) (y₁ y₂ : ℕ → Y)
    → (x₁ ∼ⁿ x₂) (pr₁ δ) → (y₁ ∼ⁿ y₂) (pr₂ δ)
    → (f (g x₁) y₁ ∼ⁿ f (g x₂) y₂) ϵ
  γ x₁ x₂ y₁ y₂ x∼ y∼
    = pr₂ (ϕᶠ ϵ) (g x₁) (g x₂) y₁ y₂
        (pr₂ (ϕᵍ (pr₁ (pr₁ (ϕᶠ ϵ)))) x₁ x₂ x∼) y∼

seq-f-ucontinuousᴺ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → (f : (ℕ → (ℕ → X)) → (ℕ → Y))
                   → 𝓤 ⊔ 𝓥  ̇
seq-f-ucontinuousᴺ {𝓤} {𝓥} {X} f
 = (ϵ : ℕ) → Σ (d , δ) ꞉ ℕ × ℕ ,
   ((x₁ x₂ : (ℕ → (ℕ → X)))
 → ((n : ℕ) → n < d → (x₁ n ∼ⁿ x₂ n) δ) → (f x₁ ∼ⁿ f x₂) ϵ)

seq-f-ucontinuous¹-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y)
 → (f : (ℕ → X) → (ℕ → Y))
 → seq-f-ucontinuous¹ f
 → f-ucontinuous (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ) f
seq-f-ucontinuous¹-to-closeness dˣ dʸ f ϕ ε
 = pr₁ (ϕ ε)
 , λ α β Cαβ → ∼ⁿ-to-C dʸ (f α) (f β) ε
                (pr₂ (ϕ ε) α β (C-to-∼ⁿ dˣ α β (pr₁ (ϕ ε)) Cαβ))

seq-f-ucontinuous²-to-closeness
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
 → (dˣ : is-discrete X) (dʸ : is-discrete Y) (dᶻ : is-discrete Z)
 → (f : (ℕ → X) → (ℕ → Y) → (ℕ → Z))
 → seq-f-ucontinuous² f
 → f-ucontinuous (×-ClosenessSpace (ℕ→D-ClosenessSpace dˣ)
                                   (ℕ→D-ClosenessSpace dʸ))
                 (ℕ→D-ClosenessSpace dᶻ) (uncurry f)
seq-f-ucontinuous²-to-closeness dˣ dʸ dᶻ f ϕ ε
 = δ 
 , λ (α₁ , α₂) (β₁ , β₂) Cαβ
 → ∼ⁿ-to-C dᶻ (f α₁ α₂) (f β₁ β₂) ε
     (pr₂ (ϕ ε) α₁ β₁ α₂ β₂
       (λ i i<δα → C-to-∼ⁿ dˣ α₁ β₁ δ
         (×-C-left (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           α₁ β₁ α₂ β₂ δ Cαβ)
         i (<-≤-trans i δα δ i<δα
              (max-≤-upper-bound δα δβ)))
       (λ i i<δβ → C-to-∼ⁿ dʸ α₂ β₂ δ
         (×-C-right (ℕ→D-ClosenessSpace dˣ) (ℕ→D-ClosenessSpace dʸ)
           α₁ β₁ α₂ β₂ δ Cαβ)
         i (<-≤-trans i δβ δ i<δβ
             (max-≤-upper-bound' δβ δα))))
 where
  δα δβ δ : ℕ
  δα = pr₁ (pr₁ (ϕ ε))
  δβ = pr₂ (pr₁ (ϕ ε))
  δ  = max δα δβ
```

[⇐ Index](../html/TWA.Thesis.index.html)
