Chuangjie Xu 2025

This module serves as a small entry point to the C-space development.
The constructions were originally developed in the PhD thesis of Chuangjie Xu (2015),
and were subsequently revised and ported to the TypeTopology project in 2025.

\begin{code}

{-# OPTIONS --without-K #-}

module gist.C-Space.index where

-- Definition and properties of uniform continuity
import gist.C-Space.UniformContinuity

-- An equivalent formulation of the coverage axiom
import gist.C-Space.Coverage

-- Development assuming full function extensionality (FunExt)
--   This variant often yields simpler constructions and proofs.
--   Since FunExt is not derivable in spartan MLTT, its use prevents
--   extraction of computational content from the development.
import gist.C-Space.UsingFunExt.index

-- Development assuming the double negation of function extensionality (¬¬FunExt)
--   Since FunExt is used under a double negation, postulating it preserves
--   the computational content of the development.
import gist.C-Space.UsingNotNotFunExt.index

\end{code}
