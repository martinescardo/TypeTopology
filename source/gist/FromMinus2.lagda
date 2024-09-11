Martin Escardo 11th September 2024

Experimental file for use with hlevels.

The type ℕ₋₂ of integers from -2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.FromMinus2 where

open import MLTT.Spartan
open import Naturals.Order

record ℕ₋₂ : 𝓤₀ ̇ where
 constructor
  minus2
 field
  plus2 : ℕ

open ℕ₋₂ public

\end{code}

If we try to define

    {-# BUILTIN FROMNAT minus2 #-}

we get te error message

    "The argument to BUILTIN FROMNAT must be a defined name
    when scope checking the declaration
      {-# BUILTIN FROMNAT _−2 #-}".

So we instead do

\begin{code}

from-ℕ : ℕ → ℕ₋₂
from-ℕ = minus2

{-# BUILTIN FROMNAT from-ℕ #-}

\end{code}

and this works.

\begin{code}

suc : ℕ₋₂ → ℕ₋₂
suc (minus2 n) = minus2 (succ n)

pattern minus1 n = minus2 (succ n)
pattern −2       = minus2 0
pattern −1       = minus2 1

\end{code}

Type "−2" as "\minus 2" (and not as "-2").
Type "−1" as "\minus 1" (and not as "-1").

Basic definitions and facts.

\begin{code}

_≤ℕ₋₂_ : ℕ₋₂ → ℕ₋₂ → 𝓤₀ ̇
minus2 m ≤ℕ₋₂ minus2 n = m ≤ℕ n

subtract-and-add-2-is-identity : (n : ℕ) → plus2 (minus2 n)＝ n
subtract-and-add-2-is-identity n = refl

add-and-subtract-2-is-identity : (n : ℕ₋₂) → minus2 (plus2 n) ＝ n
add-and-subtract-2-is-identity n = refl

\end{code}
