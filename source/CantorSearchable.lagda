Martin Escardo 2011.

The Cantor space is the type (ℕ → 𝟚). We show it is searchable, under
the assumptions discussed in CountableTychonoff.

This module is a set of corollaries of the module CountableTychonoff
and other modules.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module CantorSearchable (fe : ∀ {U V} → FunExt U V) where

open import SearchableTypes
open import CountableTychonoff (fe)
open import OmniscientTypes
open import ExhaustibleTypes

cantor-searchable : searchable (ℕ → 𝟚)
cantor-searchable = countable-Tychonoff (λ i → 𝟚-searchable)

cantor-omniscient : omniscient (ℕ → 𝟚)
cantor-omniscient = searchable-implies-omniscient cantor-searchable

cantor-exhaustible : exhaustible (ℕ → 𝟚)
cantor-exhaustible = searchable-implies-exhaustible cantor-searchable

\end{code}

The characteristic function of the universal quantifier
of the Cantor space:

\begin{code}

open import SpartanMLTT
open import ExhaustibleTypes

A : ((ℕ → 𝟚) → 𝟚) → 𝟚
A = pr₁(exhaustible-implies-exhaustible' cantor-exhaustible)

\end{code}

Discreteness of ((ℕ → 𝟚) → ℕ):

\begin{code}

open import DiscreteAndSeparated

discrete-Cantor→ℕ : discrete((ℕ → 𝟚) → ℕ)
discrete-Cantor→ℕ = omniscient-discrete-discrete' fe cantor-omniscient ℕ-discrete

\end{code}

The characteristic function of equality on ((ℕ → 𝟚) → ℕ):

\begin{code}

open import DecidableAndDetachable

equal : ((ℕ → 𝟚) → ℕ) → ((ℕ → 𝟚) → ℕ) → 𝟚

equal f  = pr₁(characteristic-function(discrete-Cantor→ℕ f))

\end{code}

Experiments: Evaluate the following to normal form (give ₀, ₁, ₁, ₀ quickly):

\begin{code}

number : 𝟚 → ℕ
number ₀ = 0
number ₁ = 1

test0 : 𝟚
test0 = A(λ α → min𝟚(α 17)(α 180))

test1 : 𝟚
test1 = A(λ α → ₁)

test2 : 𝟚
test2 = equal (λ α → number(α 17)) (λ α → number(α 100))

test3 : 𝟚
test3 = equal (λ α → number(α 100)) (λ α → number(α 100))

test4 : 𝟚
test4 = equal (λ α → number(α 1000)) (λ α → number(α 1000))

test5 : 𝟚
test5 = equal (λ α → number(α 1001)) (λ α → number(α 1000))

\end{code}
