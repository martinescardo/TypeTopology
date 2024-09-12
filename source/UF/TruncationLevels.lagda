Martin Escardo 11th September 2024

Experimental file for use with hlevels.

The type ℕ₋₂ of integers from -2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.TruncationLevels where

open import MLTT.Spartan hiding (_+_)
open import Naturals.Order
open import Notation.Order
open import Notation.Decimal

data ℕ₋₂ : 𝓤₀ ̇ where
 −2   : ℕ₋₂
 succ : ℕ₋₂ → ℕ₋₂

−1 : ℕ₋₂
−1 = succ −2

\end{code}

Input "−2" in the emacs mode as "\minus 2" (and not as "-2").  And
similarly for "−1". The two different unicode minus symbols look the
same (good), but they are not the same (also good).

The following allows us to write e.g. 3 as an element of ℕ₋₂.

\begin{code}

ℕ-to-ℕ₋₂ : (n : ℕ) {{_ : No-Constraint}} → ℕ₋₂
ℕ-to-ℕ₋₂ 0             = succ (succ −2)
ℕ-to-ℕ₋₂ (succ n) {{c}} = succ (ℕ-to-ℕ₋₂ n {{c}})

instance
 Decimal-ℕ-to-ℕ₋₂ : Decimal ℕ₋₂
 Decimal-ℕ-to-ℕ₋₂ = make-decimal-with-no-constraint ℕ-to-ℕ₋₂

\end{code}

Examples.

\begin{code}

_ : ℕ₋₂
_ = 3

_ : succ (succ −2) ＝ 0
_ = refl

_ : succ −2 ＝ −1
_ = refl

\end{code}

Addition of a natural number to a number ≥ -2.

\begin{code}

_+_ : ℕ₋₂ → ℕ → ℕ₋₂
n + 0        = n
n + (succ m) = succ (n + m)

\end{code}

More examples.

\begin{code}

_ : ℕ₋₂
_ = −2 + 1

private
 abstract
  the-answer-to-life-the-universe-and-everything : ℕ
  the-answer-to-life-the-universe-and-everything = 42

_ : ℕ₋₂
_ = −2 + the-answer-to-life-the-universe-and-everything

module _ (n : ℕ) where

 _ : ℕ₋₂
 _ = −2 + n

\end{code}

Basic definitions and facts.

\begin{code}

_≤ℕ₋₂_ : ℕ₋₂ → ℕ₋₂ → 𝓤₀ ̇
−2     ≤ℕ₋₂ n      = 𝟙
succ m ≤ℕ₋₂ −2     = 𝟘
succ m ≤ℕ₋₂ succ n = m ≤ℕ₋₂ n

instance
 Order-ℕ₋₂-ℕ₋₂ : Order ℕ₋₂ ℕ₋₂
 _≤_ {{Order-ℕ₋₂-ℕ₋₂}} = _≤ℕ₋₂_

\end{code}
