Tom de Jong, 4 June 2019.
Updated 23 December 2021.
Updated 12 June 2022.

Overview module for the theory of (pointed) directed complete posets.

The modules are roughly clustered by theme and we include a brief description of
their contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module DomainTheory where

{- The basic modules -}

-- Basic definitions of directed complete posets and Scott continuous maps
import Dcpo
-- Exponentials of (pointed) dcpos
import DcpoExponential
-- Least fixed points of Scott continuous maps
import DcpoLeastFixedPoint
-- Various general definitions and facts on directed complete posets and Scott
-- continuous maps, e.g. embedding-projection pairs, locally small dcpos, etc.
import DcpoMiscelanea
-- Definitions and properties of pointed dcpos and strict Scott continuous maps
import DcpoPointed
-- Definitions and basic properties of the way-below relation, including
-- compactness
import DcpoWayBelow

{- Directed bilimits in the category of dcpos and embedding-projections pairs -}

import DcpoBilimits
-- Specializing to bilimits of ℕ-indexed diagrams
import DcpoBilimitsSequential
-- Scott's famous D∞ that is isomorphic to its own function space
import DcpoDinfinity

{- The theory and a discussion of continuous and algebraic dcpos and the related
   notions of small (compact) bases -}
import DcpoBases
import DcpoContinuous
import DcpoContinuousDiscussion
-- The Ind-completion is used to discuss the notion of (structurally/pseudo-)
-- continuous dcpos
import DcpoIndCompletion

{- Using step functions we show that sup-complete dcpos with small compact bases
   are closed under exponentials -}
import DcpoStepFunctions
import DcpoSupComplete

{- The type Ω of truth values and the powerset are examples of pointed algebraic
   dcpos with small compact bases -}
import DcpoOmega
import DcpoPowerset

{- Further examples are given by the free pointed dcpo on a set/poset,
   constructed using the lifting monad -}
import DcpoLifting
-- The free pointed dcpo on a set is algebraic and has a small compact basis
import DcpoLiftingAlgebraic
-- The free pointed dcpo on a poset
import DcpoLiftingGeneralized

{- The (rounded) ideal completion also yields continuous/algebraic dcpos with
   small (compact) bases -}
import IdealCompletion
import IdealCompletion-Properties
-- Through the ideal completion, every continuous dcpo with a small basis is a
-- continuous retract of an algebraic dcpo with a small compact basis.
import IdealCompletion-Retracts
-- Taking the ideal completion of the dyadics yields a nice example of a
-- continuous dcpo (with a small basis) that cannot be algebraic as it has no
-- compact elements at all.
import DyadicIdealCompletion

{- An application of the theory: the Scott model of PCF -}
-- Denotational semantics of the K, S and ifZero combinators of PCF
import DcpoPCFCombinators
-- The Scott model of PCF
import ScottModelOfPCF

\end{code}
