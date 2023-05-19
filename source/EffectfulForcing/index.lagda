Martin Escardo

This is a version of the Agda code of the MFPS paper
https://doi.org/10.1016/j.entcs.2013.09.010 with a number of
extensions.

The following imports are ordered chronologically. Please don't sort
them in alphabetical order.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.index where

import EffectfulForcing.Combinators
import EffectfulForcing.CombinatoryT
import EffectfulForcing.Continuity
import EffectfulForcing.Dialogue
import EffectfulForcing.MFPS-XXIX                   -- (2012)
import EffectfulForcing.SystemT
import EffectfulForcing.LambdaCalculusVersionOfMFPS -- (2013)
import EffectfulForcing.Internal                    -- (2013)
import EffectfulForcing.WithoutOracle               -- By Vincent Rahli (2015)
import EffectfulForcing.Dialogue-to-Brouwer         -- By Martin Escardo and
                                                    --    Paulo Oliva (2017)

\end{code}
