Martin Escardo 11th September 2024

Experimental file for use with hlevels.

The type ℕ₋₂ of integers from -2.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.FromMinus2 where

open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order

\end{code}

We define ℕ₋₂ by a constructor

 pred² : ℕ → ℕ₋₂

where we think of pred² n as the predecessor of the predecessor of n,
and a field

 suc² : ℕ₋₂ → ℕ

where we think of suc² n as the successor of the successor of n.

\begin{code}

record ℕ₋₂ : 𝓤₀ ̇ where
 constructor
  pred²
 field
  suc² : ℕ

open ℕ₋₂ public

\end{code}

We check that the constructor and field have the types we claimed
above and that indeed they are mutually inverse definitionally.

\begin{code}

_ : ℕ → ℕ₋₂
_ = pred²

_ : ℕ₋₂ → ℕ
_ = suc²

\end{code}

These two functions are mutually inverse, definitionally (one
direction is the so-called η-law).

\begin{code}

suc²-is-left-inverse-of-pred² : (n : ℕ) → suc² (pred² n)＝ n
suc²-is-left-inverse-of-pred² n = refl

suc²-is-right-inverse-of-pred² : (n : ℕ₋₂) → pred² (suc² n) ＝ n
suc²-is-right-inverse-of-pred² n = refl

\end{code}

Notice that while the functions suc² and and pred² are "coercions"
from a type to another type, the successor function suc defined below
is an endomap of ℕ₋₂.

\begin{code}

suc : ℕ₋₂ → ℕ₋₂
suc (pred² n) = pred² (succ n)

\end{code}

The following allows us to use the patterns −2, −1, and pred n in
definitions by pattern matching. They can also be used as values and
functions respectively.

\begin{code}

pattern −2     = pred² 0
pattern −1     = pred² 1
pattern pred n = pred² (succ n)

\end{code}

Input "−2" in the emacs mode as "\minus 2" (and not as "-2").  And
similarly for "−1". The two different unicode minus symbols look the
same (good), but they are not the same (also good).

Notice that the these constants have the following types:

\begin{code}

_ : ℕ₋₂
_ = −2

_ : ℕ₋₂
_ = −1

_ : ℕ → ℕ₋₂
_ = pred

\end{code}

The following allows us to write e.g. 3 as an element of ℕ₋₂.

\begin{code}

from-ℕ : ℕ → ℕ₋₂
from-ℕ n = suc (suc (pred² n))

{-# BUILTIN FROMNAT from-ℕ #-}

private
 example₀ : ℕ₋₂
 example₀ = 3

 example₁ : suc (suc −2) ＝ 0
 example₁ = refl

 example₂ : suc −2 ＝ −1
 example₂ = refl

 example₃ : suc 0 ＝ 1
 example₃ = refl

\end{code}

Basic definitions and facts.

\begin{code}

_≤ℕ₋₂_ : ℕ₋₂ → ℕ₋₂ → 𝓤₀ ̇
pred² m ≤ℕ₋₂ pred² n = m ≤ n

instance
 Order-ℕ₋₂-ℕ₋₂ : Order ℕ₋₂ ℕ₋₂
 _≤_ {{Order-ℕ₋₂-ℕ₋₂}} = _≤ℕ₋₂_


\end{code}
