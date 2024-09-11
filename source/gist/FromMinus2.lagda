Martin Escardo 11th September 2024

Experimental file for use with hlevels.

The type ℕ₋₂ of integers from -2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.FromMinus2 where

open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order

record ℕ₋₂ : 𝓤₀ ̇ where
 constructor
  minus2
 field
  plus2 : ℕ

open ℕ₋₂ public

suc : ℕ₋₂ → ℕ₋₂
suc (minus2 n) = minus2 (succ n)

pattern −2       = minus2 0
pattern −1       = minus2 1
pattern minus1 n = minus2 (succ n)

\end{code}

Type "−2" as "\minus 2" (and not as "-2").
Type "−1" as "\minus 1" (and not as "-1").

The following allows us to write e.g. 3 as an element of ℕ₋₂.

\begin{code}

from-ℕ : ℕ → ℕ₋₂
from-ℕ n = suc (suc (minus2 n))

{-# BUILTIN FROMNAT from-ℕ #-}

private
 example : ℕ₋₂
 example = 3

 another-example : suc (suc −2) ＝ 0
 another-example = refl

\end{code}

Basic definitions and facts.

\begin{code}

_≤ℕ₋₂_ : ℕ₋₂ → ℕ₋₂ → 𝓤₀ ̇
minus2 m ≤ℕ₋₂ minus2 n = m ≤ n

instance
 Order-ℕ₋₂-ℕ₋₂ : Order ℕ₋₂ ℕ₋₂
 _≤_ {{Order-ℕ₋₂-ℕ₋₂}} = _≤ℕ₋₂_

subtract-and-add-2-is-identity : (n : ℕ) → plus2 (minus2 n)＝ n
subtract-and-add-2-is-identity n = refl

add-and-subtract-2-is-identity : (n : ℕ₋₂) → minus2 (plus2 n) ＝ n
add-and-subtract-2-is-identity n = refl

\end{code}
