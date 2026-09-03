Martin Escardo 2011.

The Cantor space is the type (ℕ → 𝟚). We show it is compact, under
the assumptions discussed in CountableTychonoff.

This module is a set of corollaries of the module Unsafe.CountableTychonoff
and other modules.

\begin{code}

{-# OPTIONS --without-K #-}

open import UF.FunExt

module Unsafe.CantorCompact (fe : FunExt) where

open import MLTT.Spartan
open import MLTT.Two-Properties

open import TypeTopology.CompactTypes

open import Unsafe.CountableTychonoff fe

cantor-compact∙ : is-compact∙ (ℕ → 𝟚)
cantor-compact∙ = countable-Tychonoff (λ i → 𝟚-is-compact∙)

cantor-compact : is-compact (ℕ → 𝟚)
cantor-compact = compact∙-types-are-compact cantor-compact∙

cantor-wcompact : is-wcompact (ℕ → 𝟚)
cantor-wcompact = compact-gives-wcompact cantor-compact∙

\end{code}

The characteristic function of the universal quantifier
of the Cantor space:

\begin{code}

A : ((ℕ → 𝟚) → 𝟚) → 𝟚
A = pr₁ (wcompact-types-are-wcompact' cantor-wcompact)

\end{code}

Discreteness of ((ℕ → 𝟚) → ℕ):

\begin{code}

open import UF.DiscreteAndSeparated

Cantor→ℕ-is-discrete : is-discrete ((ℕ → 𝟚) → ℕ)
Cantor→ℕ-is-discrete = discrete-to-power-compact-is-discrete' (fe 𝓤₀ 𝓤₀)
                        cantor-compact
                        ℕ-is-discrete

\end{code}

The characteristic function of equality on ((ℕ → 𝟚) → ℕ):

\begin{code}

open import NotionsOfDecidability.Complemented

equal : ((ℕ → 𝟚) → ℕ) → ((ℕ → 𝟚) → ℕ) → 𝟚

equal f  = pr₁ (characteristic-function (Cantor→ℕ-is-discrete f))

\end{code}

Experiments: Evaluate the following to normal form (give ₀, ₁, ₁, ₀ quickly):

\begin{code}

number : 𝟚 → ℕ
number ₀ = 0
number ₁ = 1

test0 : 𝟚
test0 = A (λ α → min𝟚 (α 17) (α 180))

test1 : 𝟚
test1 = A (λ α → ₁)

test2 : 𝟚
test2 = equal (λ α → number (α 17)) (λ α → number (α 100))

test3 : 𝟚
test3 = equal (λ α → number (α 100)) (λ α → number (α 100))

test4 : 𝟚
test4 = equal (λ α → number (α 1000)) (λ α → number (α 1000))

test5 : 𝟚
test5 = equal (λ α → number (α 1001)) (λ α → number (α 1000))

\end{code}
