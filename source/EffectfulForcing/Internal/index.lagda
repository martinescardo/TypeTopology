Martin Escardo, Bruno da Rocha Paiva, Ayberk Tosun, and Vincent Rahli, June 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.index where

import EffectfulForcing.Internal.FurtherThoughts
import EffectfulForcing.Internal.SystemT
import EffectfulForcing.Internal.Internal
import EffectfulForcing.Internal.Subst
import EffectfulForcing.Internal.LambdaWithoutOracle         -- By Vincent Rahli (2023)
import EffectfulForcing.Internal.Correctness                 -- By Bruno da Rocha Paiva,
                                                             -- Martin Escardo,
                                                             -- Vincent Rahli, and
                                                             -- Ayberk Tosun (2023)

\end{code}

 * The file InternalWithoutOracle gives a Church-encoded dialogue tree
   of system T into itself without an oracle.

 * The file LambdaWithoutOracle constructs dialogue trees and prove
   their correctness without using an oracle. We intend to use this to
   achieve the above TODO.

\begin{code}

import EffectfulForcing.Internal.FurtherThoughts

\end{code}

The above file contains some work in progress
