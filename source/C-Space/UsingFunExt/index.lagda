Chuangjie Xu 2025

Without extending the probe axioms, the development of C-spaces depends on
function extensionality, which is not derivable in spartan MLTT.

Accordingly, in this module we take function extensionality as an explicit
parameter and make every use of it visible. Since no computable instance of
function extensionality is available, the model does not yield computational
content. In particular, moduli of uniform continuity for System T–definable
functions cannot be extracted from their interpretation in C-spaces.

\begin{code}

{-# OPTIONS --without-K #-}

module C-Space.UsingFunExt.index where

\end{code}

The category of C-spaces and continuous maps

\begin{code}

import C-Space.UsingFunExt.Space
import C-Space.UsingFunExt.CartesianClosedness
import C-Space.UsingFunExt.Coproduct
import C-Space.UsingFunExt.LocalCartesianClosedness
import C-Space.UsingFunExt.DiscreteSpace
import C-Space.UsingFunExt.IndiscreteSpace

\end{code}

It has a Fan functional that continuously computes the least moduli
of uniform continuity.

\begin{code}

import C-Space.UsingFunExt.YonedaLemma
import C-Space.UsingFunExt.Fan

\end{code}

If the uniform-continuity principle holds for types, then the full type and
Kleene-Kreisel hierarchies agree.

\begin{code}

import C-Space.UsingFunExt.Hierarchy

\end{code}

Validate the uniform-continuity principle in various theories via C-spaces

\begin{code}

import C-Space.UsingFunExt.TdefinableFunctionsAreUC
import C-Space.UsingFunExt.UCinT
import C-Space.UsingFunExt.UCinHAo
import C-Space.UsingFunExt.ValidatingUCviaLCCC

\end{code}

Postulate function extensionality and then experiment with computing the
modulus of uniform continuity for a simple System-T–definable function that
fails to normalize

\begin{code}

import C-Space.UsingFunExt.ComputationExperiments

\end{code}
