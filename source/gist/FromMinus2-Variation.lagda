Martin Escardo 11th September 2024

Experimental file for use with hlevels.

The type ℕ₋₂ of integers from -2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.FromMinus2-Variation where

open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order

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

from-ℕ : ℕ → ℕ₋₂
from-ℕ 0        = succ (succ −2)
from-ℕ (succ n) = succ (from-ℕ n)

{-# BUILTIN FROMNAT from-ℕ #-}

private
 example₀ : ℕ₋₂
 example₀ = 3

 example₁ : succ (succ −2) ＝ 0
 example₁ = refl

 example₂ : succ −2 ＝ −1
 example₂ = refl

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
