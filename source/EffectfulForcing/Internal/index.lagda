Martin Escardo, Bruno da Rocha Paiva, Ayberk Tosun, and Vincent Rahli, June 2023

The main theorem is that for every system T closed term t : (ι → ι) → ι
there is a system T term which Church-encodes a dialogue tree of the
standard interpretation ⟦ t ⟧ of t (defined in the file System T).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.index where

import EffectfulForcing.Internal.SystemT
import EffectfulForcing.Internal.Internal
import EffectfulForcing.Internal.Subst
import EffectfulForcing.Internal.External
import EffectfulForcing.Internal.Correctness
import EffectfulForcing.Internal.FurtherThoughts
import EffectfulForcing.Internal.InternalModCont    -- by Ayberk Tosun
import EffectfulForcing.Internal.InternalModUniCont -- by Ayberk Tosun

\end{code}

 1. The file Internal gives Church-encoded dialogue trees of system T
    terms t : (ι → ι) → ι.

 2. The file External gives a semantics in terms of inductive dialogue
    trees and formulates and proves the correctness of the produced
    dialogue trees.

 3. The file Correctness proves the correctness of (1) using the
    composition of the logical relation defined in (2) with a second
    logical relation defined for that purpose.

 4. The file FurtherThoughts contains some work in progress.

 5. The file `InternalModCont` contains the proof of correctness of the internal
    modulus of continuity operator.

 6. The file `InternalModUniCont` contains the proof of correctness of the
    internal modulus of _uniform_ continuity operator.
