
   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.6.0.1.

   Martin Escardo, 2010--
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

   A module dependency graph (updated manually from time to time) is
   available at https://www.cs.bham.ac.uk/~mhe/agda-new/dependency-graph.pdf

   Check our lecture notes (https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html)
   if you want to learn HoTT/UF and Agda:

   Click at the imported module names to navigate to them.

(There are some somewhat obsolete comments at the end of this file,
explaining part of what we do in this development. See instead the
comments in the various modules.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SafeModulesIndex where

\end{code}

Main modules and module clusters:

\begin{code}

import Compactness
import TotalSeparatedness
import InjectiveTypes-article
import TheTopologyOfTheUniverse
import RicesTheoremForTheUniverse
import Ordinals
import LawvereFPT
import PartialElements
import UF
import Types2019
import PCFModules -- by Tom de Jong
\end{code}

The last module (univalent foundations) has been developed, on demand,
for use in the preceding modules (and the modules below, too). The
modules UF-Yoneda and UF-IdEmbedding contain new results.

All modules in alphabetical order:

\begin{code}

import ADecidableQuantificationOverTheNaturals
import AlternativePlus
import ArithmeticViaEquivalence
import BasicDiscontinuityTaboo
import BinaryNaturals
import CantorSchroederBernstein
import Codistance
import Compactness
import CompactTypes
import CoNaturalsArithmetic
import CoNaturalsExercise
import CoNaturals
import ConvergentSequenceCompact
import ConvergentSequenceInfCompact
import DecidabilityOfNonContinuity
import DecidableAndDetachable
import DiscreteAndSeparated
import Dominance
import DummettDisjunction
import Empty
import ExtendedSumCompact
import Fin
import FailureOfTotalSeparatedness
import GeneralNotation
import GenericConvergentSequence
import HiggsInvolutionTheorem
import Id
import InfCompact
import InjectiveTypes-article
import InjectiveTypes
import LawvereFPT
import LeftOvers
import LexicographicCompactness
import LexicographicOrder
import LiftingAlgebras
import LiftingEmbeddingDirectly
import LiftingEmbeddingViaSIP
import LiftingIdentityViaSIP
import Lifting
import LiftingMonad
import LiftingMonadVariation
import LiftingSize
import LiftingUnivalentPrecategory
import LPO
import Lumsdaine
import NaturalNumbers
import NaturalNumbers-Properties
import NaturalsAddition
import NaturalsOrder
import Negation
import NonCollapsibleFamily
import One
import One-Properties
import OrdinalArithmetic
import OrdinalCodes
import OrdinalNotationInterpretation
import OrdinalNotions
import OrdinalOfOrdinals
import OrdinalOfTruthValues
import OrdinalsClosure
import Ordinals
import OrdinalsShulmanTaboo
import OrdinalsType
import OrdinalsWellOrderArithmetic
import PartialElements
import Pi
import Plus
import PlusOneLC
import Plus-Properties
import PropInfTychonoff
import PropTychonoff
import RicesTheoremForTheUniverse
import RootsTruncation
import Sequence
import Sigma
import SimpleTypes
import SliceAlgebras
import SliceEmbedding
import SliceIdentityViaSIP
import Slice
import SliceMonad
import SpartanMLTT
import SquashedCantor
import SquashedSum
import Swap
import TheTopologyOfTheUniverse
import TotallySeparated
import Two
import Two-Prop-Density
import Two-Properties
import UF
import UF-Base
import UF-Choice
import UF-Classifiers
import UF-Embeddings
import UF-EquivalenceExamples
import UF-Equiv-FunExt
import UF-Equiv
import UF-ExcludedMiddle
import UF-Factorial
import UF-FunExt-from-Naive-FunExt-alternate
import UF-FunExt-from-Naive-FunExt
import UF-FunExt
import UF-hlevels
import UF-IdEmbedding
import UF-ImageAndSurjection
import UF-Knapp-UA
import UF-KrausLemma
import UF-LeftCancellable
import UF-Miscelanea
import UF-PropIndexedPiSigma
import UF-PropTrunc
import UF-Quotient
import UF-Retracts-FunExt
import UF-Retracts
import UF-Size
import UF-StructureIdentityPrinciple
import UF-SubsetIdentity
import UF-Subsingletons-FunExt
import UF-Subsingletons
import UF-UA-FunExt
import UF-Univalence
import UF-UniverseEmbedding
import UF-Yoneda
import UnivalenceFromScratch
import Universes
import WeaklyCompactTypes
import W
import WLPO

\end{code}





Old blurb. I want to completely rewrite this eventually, and update
it, as it is very old. However, the linked files already have
up-to-date information within them.


   September 2017. This version removes the module CurryHoward, so
   that we use the symbols Σ and + rather than ∃ and ∨. This is to be
   compatible with univalent logic. We also make our development more
   compatible with the philosophy of univalent mathematics and try to
   streamline it a bit. The original version remains at
   http://www.cs.bham.ac.uk/~mhe/agda/ for the record and to avoid
   broken incoming links.

   December 2017. This version includes many new things, including a
   characterization of the injective types, which relies on the fact
   that the identity-type former Id_X : X → (X → U) is an embedding in
   the sense of univalent mathematics.

   January 2018. This again includes many new things, including
   𝟚-compactness, totally separated reflection, and how the notion of
   𝟚-compactness interacts with discreteness, total separatedess and
   function types. We apply these results to simple types.

   April 2018. The univalence foundations library was monolotic
   before. Now it it has been modularized. We extended the
   Yoneda-Lemma file with new results.

   29 June 2018. The work on compact ordinals is essentially
   complete. Some routine bells and whistles are missing.

   20 July 2018. Completed the proof that the compact ordinals are
   retracts of the Cantor space and hence totally separated. This
   required work on several modules, and in particular the new module
   SquashedCantor.

You can navigate this set of files by clicking at words or
symbols to get to their definitions.

The module dependency graph: http://www.cs.bham.ac.uk/~mhe/agda-new/manual.pdf

The following module investigates the notion of compact set. A
set X is compact iff

   (p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁

The compactness of ℕ is a contructive taboo, known as LPO, which is an
undecided proposition in our type theory. Nevertheless, we can show
that the function type LPO→ℕ is compact:

\begin{code}

import LPO

\end{code}

See also:

\begin{code}

import WLPO

\end{code}

An example of an compact set is ℕ∞, which intuitively (and under
classical logic) is ℕ ∪ { ∞ }, defined in the following module:

\begin{code}

import GenericConvergentSequence

\end{code}

But it is more direct to show that ℕ∞ is compact, and get
compactness as a corollary:

\begin{code}

import CompactTypes
import ConvergentSequenceCompact

\end{code}

An interesting consequence of the compactness of ℕ∞ is that the
following property, an instance of WLPO, holds constructively:

  (p : ℕ∞ → 𝟚) → ((n : ℕ) → p(under n) ≡ ₁) + ¬((n : ℕ) → p(under n) ≡ ₁).

where

  under : ℕ → ℕ∞

is the embedding. (The name for the embedding comes from the fact that
in published papers we used an underlined symbol n to denote the copy
of n : ℕ in ℕ∞.)

\begin{code}

import ADecidableQuantificationOverTheNaturals

\end{code}

This is used to show that the non-continuity of a function ℕ∞ → ℕ is
decidable:

\begin{code}

import DecidabilityOfNonContinuity

\end{code}

Another example of compact set is the type of univalent
propositions (proved in the above module Compact).

Given countably many compact sets, one can take the disjoint sum
with a limit point at infinity, and this is again a compact
sets. This construction is called the squashed sum of the countable
family compact sets. It can be transfinitely iterated to produce
increasingly complex compact ordinals.

\begin{code}

import SquashedSum
import OrdinalNotationInterpretation
import LexicographicCompactness
import ConvergentSequenceInfCompact

\end{code}

As a side remark, the following module characterizes ℕ∞ as the
final coalgebra of the functor 1+(-), and is followed by an
illustrative example:

\begin{code}

import CoNaturals
import CoNaturalsExercise

\end{code}

The following module discusses in what sense ℕ∞ is the generic
convergent sequence, and proves that the universe U of types is
indiscrete, with a certain Rice's Theorem for the universe U as a
corollary:

\begin{code}

import TheTopologyOfTheUniverse
import RicesTheoremForTheUniverse

\end{code}

The following two rogue modules depart from our main philosophy of
working strictly within ML type theory with the propositional
axiom of extensionality. They disable the termination checker, for
the reasons explained in the first module. But to make our point,
we also include runnable experiments in the second module:

\begin{code}

-- import CountableTychonoff --unsafe (see above)
-- import CantorCompact      --unsafe (see above)`

\end{code}

The following modules return to the well-behavedness paradigm.
The first one shows that a basic form of discontinuity is a
taboo. This, in fact, is used to formulate and prove Rice's
Theorem mentioned above:

\begin{code}

import BasicDiscontinuityTaboo

\end{code}

The following shows that universes are injective, and more generally
that the injective types are the retracts of exponential powers of
universes:

\begin{code}

import InjectiveTypes

\end{code}

This uses properties of products indexed by univalent propositions,
first that it is isomorphic to any of its factors:

\begin{code}

import UF-PropIndexedPiSigma

\end{code}

And, more subtly, that a product of compact sets indexed by a
univalent proposition is itself compact:

\begin{code}

import PropTychonoff

\end{code}

And finally that the map Id {X} : X → (X → U) is an embedding in the
sense of univalent mathematics, where Id is the identity type former:

\begin{code}

import UF-IdEmbedding

\end{code}

The following generalizes the squashed sum, with a simple construction
and proof, using the injectivity of the universe and the Prop-Tychonoff theorem:

\begin{code}

import ExtendedSumCompact

\end{code}

The following modules define 𝟚-compactness and study its interaction
with discreteness and total separatedness, with applications to simple
types. We get properties that resemble those of the model of
Kleene-Kreisel continuous functionals of simple types, with some new
results.

\begin{code}

import TotallySeparated
import CompactTypes
import SimpleTypes
import FailureOfTotalSeparatedness

\end{code}
