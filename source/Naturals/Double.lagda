Double function on natural nuumbers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.Double where

open import MLTT.Spartan hiding (_+_)
open import MLTT.Unit-Properties
open import Naturals.Properties

double : ℕ → ℕ
double 0        = 0
double (succ n) = succ (succ (double n))

sdouble : ℕ → ℕ
sdouble = succ ∘ double

double-is-not-sdouble : {m n : ℕ} → double m ≠ sdouble n
double-is-not-sdouble {0}      {0}      = zero-not-positive 0
double-is-not-sdouble {0}      {succ n} = zero-not-positive
                                           (succ (succ (double n)))
double-is-not-sdouble {succ m} {succ n} = λ p → double-is-not-sdouble
                                                 (succ-lc (succ-lc p))

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

Added 26 September 2025 by Fredrik Nordvall Forsberg.

\begin{code}

open import Naturals.Properties
open import Naturals.Order
open import Notation.Order

double-reflects-≤ : {x y : ℕ} → double x ≤ double y → x ≤ y
double-reflects-≤ {zero} {y} _ = ⋆
double-reflects-≤ {succ x} {succ y} p = double-reflects-≤ {x} {y} p

double-reflects-< : {x y : ℕ} → double x < double y → x < y
double-reflects-< {zero} {succ y} _ = ⋆
double-reflects-< {succ x} {succ y} p = double-reflects-< {x} {y} p

\end{code}

Added 26 September 2025 by Fredrik Nordvall Forsberg.

\begin{code}

open import Naturals.Addition

double-is-self-addition : (n : ℕ) → double n ＝ n + n
double-is-self-addition zero = refl
double-is-self-addition (succ n) =
 ap succ (succ (double n) ＝⟨ ap succ (double-is-self-addition n) ⟩
          succ (n + n)    ＝⟨ succ-left n n ⁻¹ ⟩
          succ n + n      ∎)

\end{code}
