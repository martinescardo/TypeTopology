Martin Escardo

Brouwer ordinal codes.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.Brouwer where

open import MLTT.Spartan

data B : 𝓤₀ ̇ where
 Z : B
 S : B → B
 L : (ℕ → B) → B

data _≈_ : B → B → 𝓤₀ ̇ where
 Z≈ : Z ≈ Z

 S≈ : {b c : B}
    → b ≈ c
    → S b ≈ S c

 L≈ : (ϕ ψ : ℕ → B)
    → (∀ n → ϕ n ≈ ψ n)
    → L ϕ ≈ L ψ

infix 0 _≈_

≈-refl : (b : B)
       → b ≈ b
≈-refl Z     = Z≈
≈-refl (S b) = S≈ (≈-refl b)
≈-refl (L ϕ) = L≈ ϕ ϕ (λ n → ≈-refl (ϕ n))

≈-sym : {b c : B}
      → b ≈ c
      → c ≈ b
≈-sym Z≈         = Z≈
≈-sym (S≈ h)     = S≈ (≈-sym h)
≈-sym (L≈ ϕ ψ h) = L≈ ψ ϕ (λ n → ≈-sym (h n))

≈-trans : {b c d : B}
        → b ≈ c
        → c ≈ d
        → b ≈ d
≈-trans Z≈         Z≈         = Z≈
≈-trans (S≈ h)     (S≈ l)     = S≈ (≈-trans h l)
≈-trans (L≈ ϕ ψ h) (L≈ ψ θ l) = L≈ ϕ θ (λ n → ≈-trans (h n) (l n))

\end{code}
