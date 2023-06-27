Martin Escardo, Bruno da Rocha Paiva, Ayberk Tosun, and Vincent Rahli

The following imports are ordered chronologically. Please don't sort
them in alphabetical order.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.index where

import EffectfulForcing.Internal.InternalWithoutOracle       -- By Bruno da Rocha Paiva,
                                                             -- Martin Escardo,
                                                             -- Vincent Rahli, and
                                                             -- Ayberk Tosun (2023)
import EffectfulForcing.Internal.LambdaWithoutOracle         -- By Vincent Rahli (2023)

\end{code}

 * The file InternalWithoutOracle gives a Church-encoded dialogue tree
   of system T into itself without an oracle.

 * The file LambdaWithoutOracle constructs dialogue trees and prove
   their correctness without using an oracle. We intend to use this to
   achieve the above TODO.
