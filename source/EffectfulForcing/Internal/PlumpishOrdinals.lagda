--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.PlumpishOrdinals where

open import MLTT.Spartan

\end{code}

We abstract the properties of ordinals we require for proving Hancock's
conjecture in the following record type.

\begin{code}

record PlumpishOrdinals : (𝓤 ⁺) ̇ where
 field
  -- Type of ordinals
  O : 𝓤 ̇

  -- Constructors of ordinals
  Zₒ : O
  Sₒ : O → O
  Lₒ : (ℕ → O) → O

  -- Orderings of ordinals
  _⊑_ : O → O → 𝓤 ̇
  _⊏_ : O → O → 𝓤 ̇

  Z-⊑ : (o : O) → Zₒ ⊑ o
  S-inflationary : (o : O) → o ⊏ Sₒ o
  L-upper-bound : (ϕ : ℕ → O) (n : ℕ) → ϕ n ⊑ Lₒ ϕ
  L-least-upper-bound : (ϕ : ℕ → O) (ψ : O) → (∀ n → ϕ n ⊑ ψ) → Lₒ ϕ ⊑ ψ

  ⊑-refl : (o : O) → o ⊑ o
  ⊑-trans : (o₁ o₂ o₃ : O) → o₁ ⊑ o₂ → o₂ ⊑ o₃ → o₁ ⊑ o₃

  ⊏-trans : (o₁ o₂ o₃ : O) → o₁ ⊏ o₂ → o₂ ⊏ o₃ → o₁ ⊏ o₃

  ⊏-implies-⊑ : (o₁ o₂ : O) → o₁ ⊏ o₂ → o₁ ⊑ o₂
  ⊑-and-⊏-implies-⊏ : (o₁ o₂ o₃ : O) → o₁ ⊑ o₂ → o₂ ⊏ o₃ → o₁ ⊏ o₃

\end{code}
