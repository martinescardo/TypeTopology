Natural numbers properties

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.Properties where

open import MLTT.Spartan
open import MLTT.Unit-Properties

pred : ℕ → ℕ
pred 0        = 0
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
succ-no-fp 0        p = positive-not-zero 0 (p ⁻¹)
succ-no-fp (succ n) p = succ-no-fp n (succ-lc p)

ℕ-cases : {P : ℕ → 𝓦 ̇ } (n : ℕ)
        → (n ＝ 0 → P n) → ((m : ℕ) → n ＝ succ m → P n) → P n
ℕ-cases 0        c₀ cₛ = c₀ refl
ℕ-cases (succ n) c₀ cₛ = cₛ n refl

double : ℕ → ℕ
double 0        = 0
double (succ n) = succ (succ (double n))

sdouble : ℕ → ℕ
sdouble = succ ∘ double

double-lc : {m n : ℕ} → double m ＝ double n → m ＝ n
double-lc {0}      {0}      p = refl
double-lc {succ m} {succ n} p = ap succ IH
 where
  IH : m ＝ n
  IH = double-lc {m} {n} (succ-lc (succ-lc p))

sdouble-lc : {m n : ℕ} → sdouble m ＝ sdouble n → m ＝ n
sdouble-lc = double-lc ∘ succ-lc

power2 : ℕ → ℕ
power2 0        = 1
power2 (succ n) = double (power2 n)

\end{code}

Added 12/05/2022 by Andrew Sneap.

\begin{code}

succ-pred : (x : ℕ) → succ (pred (succ x)) ＝ succ x
succ-pred x = refl

succ-pred' : (x : ℕ) → ¬ (x ＝ 0) → succ (pred x) ＝ x
succ-pred' 0        ν = 𝟘-elim (ν refl)
succ-pred' (succ n) _ = refl

pred-succ : (x : ℕ) → pred (succ x) ＝ x
pred-succ x = refl

\end{code}

End of addition.
