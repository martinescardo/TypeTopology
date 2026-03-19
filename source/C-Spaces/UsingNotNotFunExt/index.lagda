Chuangjie Xu 2025 (ported to TypeTopology in 2026)

By adding a suitable probe axiom, the double negation of function
extensionality becomes sufficient for developing the theory of C-spaces.

This module serves as the entry point to the branch of the C-space development
that assumes `¬¬ FunExt` as an explicit parameter, making each use of that
assumption visible in the Agda code.

Although the double negation of function extensionality is not derivable
in Spartan MLTT, it occurs only under negation. Assuming it therefore does not
compromise the computational content of the development. In particular, moduli
of uniform continuity extracted from the interpretation of System-T–definable
functions in C-spaces can still normalize to numerals as closed Agda terms.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.UsingNotNotFunExt.index where

\end{code}

The first group of imports develops the category of C-spaces and its basic
structure.

\begin{code}

import C-Spaces.UsingNotNotFunExt.Space
import C-Spaces.UsingNotNotFunExt.CartesianClosedness
import C-Spaces.UsingNotNotFunExt.DiscreteSpace

\end{code}

The next group of imports constructs the Fan functional, which continuously
computes least moduli of uniform continuity.

\begin{code}

import C-Spaces.UsingNotNotFunExt.YonedaLemma
import C-Spaces.UsingNotNotFunExt.Fan

\end{code}

The following module validates the uniform-continuity principle in System T.

\begin{code}

import C-Spaces.UsingNotNotFunExt.UCinT

\end{code}

Finally, the computation experiment records explicit examples in which the
extracted moduli do normalize to numerals as closed Agda terms.

\begin{code}

import C-Spaces.UsingNotNotFunExt.ComputationExperiments

\end{code}
