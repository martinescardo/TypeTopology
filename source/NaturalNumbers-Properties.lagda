Natural numbers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module NaturalNumbers-Properties where

open import Universes
open import NaturalNumbers
open import Negation
open import Id
open import Empty
open import Unit
open import Unit-Properties

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-lc = ap pred

positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙

  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f

zero-not-positive : (x : ℕ) → 0 ≢ succ x
zero-not-positive x p = positive-not-zero x (p ⁻¹)

succ-no-fp : (n : ℕ) → n ≢ succ n
succ-no-fp zero     p = positive-not-zero 0 (p ⁻¹)
succ-no-fp (succ n) p = succ-no-fp n (succ-lc p)

ℕ-cases : {P : ℕ → 𝓦 ̇ } (n : ℕ)
        → (n ≡ zero → P n) → ((m : ℕ) → n ≡ succ m → P n) → P n
ℕ-cases {𝓦} {P} zero c₀ cₛ     = c₀ refl
ℕ-cases {𝓦} {P} (succ n) c₀ cₛ = cₛ n refl

\end{code}
