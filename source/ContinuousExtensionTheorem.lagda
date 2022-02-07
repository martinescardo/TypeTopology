\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import UF-Subsingletons
open import UF-FunExt
open import UF-PropTrunc

open import MetricSpaceAltDef
open import MetricSpaceRationals

module ContinuousExtensionTheorem
 (fe : Fun-Ext)
 (pe : Prop-Ext)
 (pt : propositional-truncations-exist)
  where

open PropositionalTruncation pt

open import DedekindReals pe pt fe
open import MetricSpaceDedekindReals pt fe pe

\end{code}

The goal is to solve the following proof from Simmons Introduction to Topology and Modern Analysis:

Let X be a metric space, let Y be a complete metric space, and A be a dense subspace of X.
If f is a uniformly continuous mapping of A into Y, then f can be extended uniquely to a uniformly continuous mapping g of X into Y.

In order to prove this, it is first necessary to introduce the definitions in the proof.

\begin{code}



\end{code}
