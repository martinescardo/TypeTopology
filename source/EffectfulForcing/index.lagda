Martin Escardo 2012

This is a version of the Agda code of the MFPS paper
https://doi.org/10.1016/j.entcs.2013.09.010 with a number of
extensions.

The following imports are ordered chronologically. Please don't sort
them in alphabetical order.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.index where

import EffectfulForcing.MFPS-XXIX
import EffectfulForcing.Combinators
import EffectfulForcing.CombinatoryT
import EffectfulForcing.Continuity
import EffectfulForcing.Dialogue
import EffectfulForcing.SystemT
import EffectfulForcing.LambdaCalculusVersionOfMFPS
import EffectfulForcing.Internal
import EffectfulForcing.WithoutOracle       -- By Vincent Rahli
import EffectfulForcing.Dialogue-to-Brouwer -- By Martin Escardo and Paulo Oliva

\end{code}
