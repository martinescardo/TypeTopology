[⇐ Index](../html/TWA.Thesis.index.html)

# Sequences

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import UF.DiscreteAndSeparated
open import NotionsOfDecidability.Complemented

module TWA.Thesis.Chapter2.Sequences where

repeat : {X : 𝓤 ̇ } → X → ℕ → X
repeat α _ = α

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

_∷_ : {T : ℕ → 𝓤 ̇ } → T 0 → Π (T ∘ succ) → Π T
(h ∷ α) 0 = h
(h ∷ α) (succ n) = α n

_∼ⁿ_ : {X : ℕ → 𝓤 ̇ } → Π X → Π X → ℕ → 𝓤 ̇
(α ∼ⁿ β) n = (i : ℕ) → i < n → α i ＝ β i

∼ⁿ-sym : {X : ℕ → 𝓤 ̇ } (α β : Π X) (n : ℕ)
       → (α ∼ⁿ β) n
       → (β ∼ⁿ α) n
∼ⁿ-sym α β n f i i<n = f i i<n ⁻¹

bounded-decidable-Π : {X : ℕ → 𝓤 ̇ }
                    → is-complemented X
                    → (n : ℕ)
                    → is-decidable (Π i ꞉ ℕ , (i < n → X i))
bounded-decidable-Π d 0 = inl (λ _ ())
bounded-decidable-Π {𝓤} {X} d (succ n)
 = Cases (bounded-decidable-Π d n) γ₁ (inr ∘ γ₂)
 where
  γ₁ : ((i : ℕ) → (i < n → X i))
     → is-decidable ((i : ℕ) → (i < succ n → X i))
  γ₁ f = Cases (d n) (inl ∘ γ₁₁) (inr ∘ γ₁₂)
   where
    γ₁₁ : X n → (i : ℕ) → i < succ n → X i
    γ₁₁ Xn i i<sn
     = Cases (<-split i n i<sn) (f i) (λ e → transport X (e ⁻¹) Xn)
    γ₁₂ : ¬ X n → ¬ ((i : ℕ) → i < succ n → X i)
    γ₁₂ g f = g (f n (<-succ n))
  γ₂ : ¬ ((i : ℕ) → i < n → X i) → ¬ ((i : ℕ) → i < succ n → X i)
  γ₂ g f = g (λ i i<n → f i (<-trans i n (succ n) i<n (<-succ n)))

bounded-decidable-Σ : {X : ℕ → 𝓤 ̇ } → is-complemented X
                    → (n : ℕ)
                    → is-decidable (Σ i ꞉ ℕ , ((i < n) × X i))
bounded-decidable-Σ d 0 = inr (λ (i , i<0 , _) → i<0)
bounded-decidable-Σ {𝓤} {X} d (succ n)
 = Cases (bounded-decidable-Σ d n)
    (λ (i , i<n , Xi)
     → inl (i , <-trans i n (succ n) i<n (<-succ n) , Xi))
    (λ ¬Σi<n → Cases (d n)
      (λ Xn → inl (n , <-succ n , Xn))
      (λ ¬Xn → inr (λ (i , i<sn , Xi) → Cases (<-split i n i<sn)
        (λ i<n → ¬Σi<n (i , i<n , Xi))
        (λ i＝n → ¬Xn (transport X i＝n Xi)))))

∼ⁿ-decidable
 : {X : ℕ → 𝓤 ̇ }
 → ((n : ℕ) → is-discrete (X n))
 → (α β : Π X) → (n : ℕ) → is-decidable ((α ∼ⁿ β) n)
∼ⁿ-decidable ds α β = bounded-decidable-Π (λ n → ds n (α n) (β n))
```

[⇐ Index](../html/TWA.Thesis.index.html)
