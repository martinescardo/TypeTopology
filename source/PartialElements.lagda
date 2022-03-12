Martin Escardo 10th January 2018.

The following modules study the type of partial elements of a type (or
lifting).

Cf. my former student Cory Knapp's PhD thesis and our CSL'2017 paper
https://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf
But there are also new results and observations here, as well as
different approaches.

We apply the results to characterize injective types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PartialElements where

import Lifting
import LiftingEmbeddingDirectly
import LiftingIdentityViaSIP
import LiftingEmbeddingViaSIP
import LiftingUnivalentPrecategory
import LiftingMonad
import LiftingMonadVariation
import LiftingAlgebras
import LiftingSize
import LiftingMiscelanea
import LiftingMiscelanea-PropExt-FunExt

\end{code}
