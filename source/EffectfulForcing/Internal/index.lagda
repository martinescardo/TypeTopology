Martin Escardo, Bruno da Rocha Paiva, Ayberk Tosun, and Vincent Rahli, June 2023

The main theorem is that for every system T closed term t : (ι → ι) → ι
there is a system T term which Church-encodes a dialogue tree of the
standard interpretation ⟦ t ⟧ of t (defined in the file System T).

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.index where

import EffectfulForcing.Internal.SystemT
import EffectfulForcing.Internal.Internal
import EffectfulForcing.Internal.Subst
import EffectfulForcing.Internal.External
import EffectfulForcing.Internal.Correctness
import EffectfulForcing.Internal.FurtherThoughts

\end{code}

 1. The file Internal gives a Church-encoded dialogue tree of system T.

 2. The file External gives a semantics in terms of inductive dialogue
    trees and proves the correctness of the dialogue trees.

 3. The file Correctness proves the correctness (1) using the
    composition of the logical relation defined in (2) with second
    logical relation.

 4. The file FurtherThoughts contains some work in progress.
