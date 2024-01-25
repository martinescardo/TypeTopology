Martin Escardo 2011.

We now iterate the proof of the fact that binary products preserve
compactness, to get that countable (dependent) products preserve
compactness. The function countable-Tychonoff requires explicit
indication of termination.

\begin{code}

{-# OPTIONS --without-K #-}

open import UF.FunExt

module Unsafe.CountableTychonoff (fe : FunExt) where

open import MLTT.Spartan
open import Naturals.Sequence fe
open import TypeTopology.CompactTypes

binary-Tychonoff' : {X : ℕ → 𝓤 ̇ }
                  → is-compact∙ (X 0)
                  → is-compact∙ ((n : ℕ) → X (succ n))
                  → is-compact∙ ((n : ℕ) → X n)

binary-Tychonoff' ε δ = retractions-preserve-compactness
                         cons-has-section'
                         (binary-Tychonoff ε δ)
\end{code}

The following needs disabling of termination checking. It terminates
on the assumption that functions are continuous, but doesn't use their
moduli of continuity. Put another way, we get an infinite proof, so to
speak, but whenever it is applied to compute a ground value, a finite
portion of the proof is used, because of continuity.

We emphasize that although continuity is used at the meta-level to
justify termination, the result is not anti-classical. In fact,
classically, all sets are compact! This module just enlarges the
constructive universe a bit, using Brouwerian ideas, but being
compatible with Bishop in the sense of not contradicting classical
mathematics.

Because the proof of termination is not constructive, if you are a
strict constructivist maybe you won't be convinced that this
proof-program always terminates (when used to define a value of ground
type). However, you will have a hard time exhibiting a
counter-example: the assumption of existence of a non-continuous
function allows you to constructively prove LPO! (With the termination
checker enabled.) (I plan to actually write down this proof in Agda.)


\begin{code}

{-# TERMINATING #-}
countable-Tychonoff : {X : ℕ → 𝓤 ̇ }
                    → ((n : ℕ) → is-compact∙ (X n))
                    → is-compact∙ ((n : ℕ) → X n)
countable-Tychonoff {X} ε = binary-Tychonoff' (head ε) (countable-Tychonoff (tail ε))

\end{code}

A corollary is that the Cantor space is compact. See the module
CantorCompact.
