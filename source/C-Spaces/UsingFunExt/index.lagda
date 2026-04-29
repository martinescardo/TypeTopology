Chuangjie Xu 2015 (ported to TypeTopology in 2026)

Without extending the probe axioms, the development of C-spaces depends on
function extensionality, which is not derivable in spartan MLTT.

This module serves as the entry point to the branch of the C-space development
that assumes full function extensionality as an explicit parameter, making each
use of that assumption visible in the Agda code.

This branch is closest to the mathematical presentation of C-spaces, but it
does not preserve computational content: since no computable instance of
function extensionality is available, closed Agda terms extracted from the
model need not normalize in a computationally meaningful way. In particular,
moduli of uniform continuity obtained from the interpretation of System
T-definable functions cannot in general be expected to normalize to numerals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.UsingFunExt.index where

\end{code}

The first group of imports develops the category of C-spaces and its basic
structure.

\begin{code}

import C-Spaces.UsingFunExt.Space
import C-Spaces.UsingFunExt.CartesianClosedness
import C-Spaces.UsingFunExt.Coproduct
import C-Spaces.UsingFunExt.LocalCartesianClosedness
import C-Spaces.UsingFunExt.DiscreteSpace
import C-Spaces.UsingFunExt.IndiscreteSpace
import C-Spaces.UsingFunExt.CwF

\end{code}

The next group of imports constructs the Fan functional, which continuously
computes least moduli of uniform continuity.

\begin{code}

import C-Spaces.UsingFunExt.YonedaLemma
import C-Spaces.UsingFunExt.Fan

\end{code}

The following module compares the full type hierarchy with the Kleene-Kreisel
hierarchy under the assumption of uniform continuity.

\begin{code}

import C-Spaces.UsingFunExt.Hierarchy

\end{code}

The next group of imports validates the uniform-continuity principle in several
type-theoretic and arithmetic settings via C-spaces.

\begin{code}

import C-Spaces.UsingFunExt.TdefinableFunctionsAreUC
import C-Spaces.UsingFunExt.UCinT
import C-Spaces.UsingFunExt.UCinHAOmega
import C-Spaces.UsingFunExt.ValidatingUCviaLCCC

\end{code}

Finally, the computation experiment records a simple example in which the
mathematically correct extracted modulus does not normalize to a numeral as a
closed Agda term.

\begin{code}

import C-Spaces.UsingFunExt.ComputationExperiments

\end{code}
