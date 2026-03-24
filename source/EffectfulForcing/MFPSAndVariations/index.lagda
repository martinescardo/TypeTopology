Martin Escardo

This is a version of the Agda code of the MFPS paper
https://doi.org/10.1016/j.entcs.2013.09.010 with a number of
extensions.

The following imports are ordered chronologically. Please don't sort
them in alphabetical order.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.MFPSAndVariations.index where

import EffectfulForcing.MFPSAndVariations.Combinators
import EffectfulForcing.MFPSAndVariations.CombinatoryT
import EffectfulForcing.MFPSAndVariations.Continuity
import EffectfulForcing.MFPSAndVariations.ContinuityProperties        -- added by Ayberk Tosun
import EffectfulForcing.MFPSAndVariations.Dialogue
import EffectfulForcing.MFPSAndVariations.MFPS-XXIX                   -- (2012)
import EffectfulForcing.MFPSAndVariations.SystemT
import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS -- (2013)
import EffectfulForcing.MFPSAndVariations.Church                      -- (2013)
import EffectfulForcing.MFPSAndVariations.Internal                    -- (2013)
import EffectfulForcing.MFPSAndVariations.WithoutOracle               -- By Vincent Rahli (2015)
import EffectfulForcing.MFPSAndVariations.Dialogue-to-Brouwer         -- By Martin Escardo
                                                                      -- and Paulo Oliva (2017)

\end{code}

 * The file combinators defines S, K, iteration over the natural
   numbers and primitive recursion.

 * The file CombinatoryT defines a combinatory version of Gödel's system T.

   Additionally it defines its "standard set-theoretical interpretation": the
   ground type is interpreted as the set of natural numbers, and functions types
   are interpreted as the set of all functions.

   Moreover, a version of (combinatory) system T with an oracle Ω is defined,
   with a standard semantics, together with its relation to the system without
   oracles.

 * The file Continuity defines the Baire type and a notion of
   continuity for functions from it to the type of natural numbers, and
   the Cantor type and a notion of uniform continuity

   It also includes simple, but useful, lemmas and constructions.

 * The file Dialogue defines dialogue trees, which are a fundamental
   ingredient for the MFPS paper coded in the file MFPS-XXIX.

   It is better to read the paper to know about this before reading
   the Agda code, but, in very brief summary, the following is included:


     1. Conversion from dialogue trees to functions.

     2. The fact that functions (ℕ → ℕ) → ℕ that come from dialogue trees are
        continuous.

     3. And that their restrictions to (ℕ → 𝟐) are uniformly continuous.

     4. The definition of a monad (in Kleisli extension form) of dialogue trees.

     5. And, crucially, the contruction of a "generic" sequence of
        natural number, with its specification (the function
        generic-diagram).

 * The file MFPS-XXIX is implements the MFPS'2013 paper, which shows
   that all PCF definable functions (ℕ → ℕ) → ℕ are continuous, and
   their restriction to (ℕ → 𝟐) are uniformly continuous, using a
   dialogue tree interpretation of (combinatory) system T.

 * The file system T defines the λ-calculus version of system T,
   including a version with oracles.

 * The file Internal takes a different approach. Instead of defining a
   semantics of system T, it defines a translation from system T to
   system T that implements an internalization of the dialogue
   semantics. For that purpose, it uses Church encoding of dialogue
   trees wuthin system T.

   However, it doesn't formulate or prove the correctness of this
   translation.

   But it repeats the examples given in the file MFPS-XXIX, which give
   the same numerical results.

   TODO. Formulate and prove the correctness, in a new file called
   InternalCorrectness.

 * The file WithoutOracle, written by Vincent Rahli in 2015, shows
   that it is not necessary to consider an extension of (combinatory)
   system T with oracles to reach the same conclusions.

 * The file Dialogue-to-Brouwer, written by Martin Escardo and Paulo
   Oliva, shows how to translate dialogue trees for functions (ℕ → ℕ) → ℕ
   to Brouwer trees, including a formulation and proof of correctness
   of the translation.
