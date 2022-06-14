Tom de Jong, 4 June 2019
Updated 23 December 2021
Updated 12 and 14 June 2022

Index for the formalization of domain theory, briefly describing the contents of
each directory, ordered alphabetically by directory name.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module DomainTheory.index where

{- Basics -}

-- Basic definitions of directed complete posets and Scott continuous maps
import DomainTheory.Basics.Dcpo
-- Exponentials of (pointed) dcpos
import DomainTheory.Basics.Exponential
-- Least fixed points of Scott continuous maps
import DomainTheory.Basics.LeastFixedPoint
-- Various general definitions and facts on directed complete posets and Scott
-- continuous maps, e.g. embedding-projection pairs, locally small dcpos, etc.
import DomainTheory.Basics.Miscelanea
-- Definitions and properties of pointed dcpos and strict Scott continuous maps
import DomainTheory.Basics.Pointed
-- Useful facts about sup-complete dcpos, e.g. the directification of families
import DomainTheory.Basics.SupComplete
-- -- Definitions and basic properties of the way-below relation, including
-- compactness
import DomainTheory.Basics.WayBelow

{- BasesAndContinuity -}

-- The theory of small (compact) bases
import DomainTheory.BasesAndContinuity.Bases
-- The theory of continuous/algebraic dcpos
import DomainTheory.BasesAndContinuity.Continuity
-- A discussion on possible definitions of continuous dcpo
import DomainTheory.BasesAndContinuity.ContinuityDiscussion
-- The Ind-completion is used to discuss the notion of (structurally/pseudo-)
-- continuous dcpos
import DomainTheory.BasesAndContinuity.IndCompletion
-- Using step functions we show that sup-complete dcpos with small compact bases
-- are closed under exponentials
import DomainTheory.BasesAndContinuity.StepFunctions

{- Bilimits -}

-- Bilimits of directed diagrams
import DomainTheory.Bilimits.Directed
-- Specializing to bilimits of ℕ-indexed diagrams
import DomainTheory.Bilimits.Sequential
-- Scott's famous D∞ that is isomorphic to its own function space
import DomainTheory.Bilimits.Dinfinity

{- Examples -}

-- The ideal completion of the dyadics is a nice example of a continuous dcpo
-- (with a small basis) that cannot be algebraic as it has no compact elements
-- at all.
import DomainTheory.Examples.IdlDyadics
-- The type Ω of propositions is an examples of a pointed algebraic dcpo with
-- the booleans giving a small compact basis
import DomainTheory.Examples.Omega
-- The powerset is an examples of a pointed algebraic dcpo with lists giving a
-- small compact basis (through Kuratowski finite subsets)
import DomainTheory.Examples.Powerset

{- IdealCompletion -}

-- Construction of the rounded ideal completion of an abstract basis
import DomainTheory.IdealCompletion.IdealCompletion
-- Properties of the ideal completion, e.g. it has a small compact basis
import DomainTheory.IdealCompletion.Properties
-- Through the ideal completion, every continuous dcpo with a small basis is a
-- continuous retract of an algebraic dcpo with a small compact basis
import DomainTheory.IdealCompletion.Retracts

{- Lifting -}

-- Freely adding a least element to a dcpo
import DomainTheory.Lifting.LiftingDcpo
-- The lifting is the free pointed dcpo on a set
import DomainTheory.Lifting.LiftingSet
-- The lifting of a set is algebraic with a small compact basis
import DomainTheory.Lifting.LiftingSetAlgebraic

{- ScottModelOfPCF -}

-- Denotational semantics of the K, S and ifZero combinators of PCF
import DomainTheory.ScottModelOfPCF.PCFCombinators
-- The Scott model of the typed programming language PCF
import DomainTheory.ScottModelOfPCF.ScottModelOfPCF

\end{code}
