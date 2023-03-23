Natural numbers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module Naturals.Properties where

open import MLTT.Universes
open import MLTT.NaturalNumbers
open import MLTT.Negation
open import MLTT.Id
open import MLTT.Empty
open import MLTT.Unit
open import MLTT.Unit-Properties

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {i j : ℕ} → succ i ＝ succ j → i ＝ j
succ-lc = ap pred

positive-not-zero : (x : ℕ) → succ x ≠ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙

  g : succ x ＝ 0 → 𝟙 ＝ 𝟘
  g = ap f

zero-not-positive : (x : ℕ) → 0 ≠ succ x
zero-not-positive x p = positive-not-zero x (p ⁻¹)

succ-no-fp : (n : ℕ) → n ≠ succ n
succ-no-fp zero     p = positive-not-zero 0 (p ⁻¹)
succ-no-fp (succ n) p = succ-no-fp n (succ-lc p)

ℕ-cases : {P : ℕ → 𝓦 ̇ } (n : ℕ)
        → (n ＝ zero → P n) → ((m : ℕ) → n ＝ succ m → P n) → P n
ℕ-cases {𝓦} {P} zero c₀ cₛ     = c₀ refl
ℕ-cases {𝓦} {P} (succ n) c₀ cₛ = cₛ n refl

\end{code}

Added 12/05/2022 by Andrew Sneap.

\begin{code}

succ-pred : (x : ℕ) → succ (pred (succ x)) ＝ succ x
succ-pred x = refl

succ-pred' : (x : ℕ) → ¬ (x ＝ 0) → succ (pred x) ＝ x
succ-pred' zero     nz = 𝟘-elim (nz refl)
succ-pred' (succ n) _ = refl

pred-succ : (x : ℕ) → pred (succ x) ＝ x
pred-succ x = refl

\end{code}
