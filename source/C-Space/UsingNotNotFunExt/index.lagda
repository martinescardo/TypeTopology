Chuangjie Xu 2025

By adding a suitable probe axiom, the double negation of function
extensionality becomes sufficient for developing the theory of C-spaces.
In this module we take this principle as an explicit parameter, making
every use of it fully visible.

Although the double negation of function extensionality is not derivable
in spartan MLTT, it appears only under a negation. Postulating it therefore
does not compromise the computational content of our development. As a
result, we can extract moduli of uniform continuity for System-T–definable
functions from their interpretation in C-spaces, and these moduli normalize
to numerals.

\begin{code}

{-# OPTIONS --without-K #-}

module C-Space.UsingNotNotFunExt.index where

\end{code}

The category of C-spaces and continuous maps

\begin{code}

import C-Space.UsingNotNotFunExt.Space
import C-Space.UsingNotNotFunExt.CartesianClosedness
import C-Space.UsingNotNotFunExt.DiscreteSpace

\end{code}

It has a Fan functional that continuously computes the least moduli
of uniform continuity.

\begin{code}

import C-Space.UsingNotNotFunExt.YonedaLemma
import C-Space.UsingNotNotFunExt.Fan

\end{code}

Validate the uniform-continuity principle in System T

\begin{code}

import C-Space.UsingNotNotFunExt.UCinT

\end{code}

Postulate the double negation of function extensionality and then experiment
with computing moduli of uniform continuity for System-T–definable functions

\begin{code}

import C-Space.UsingNotNotFunExt.ComputationExperiments

\end{code}
