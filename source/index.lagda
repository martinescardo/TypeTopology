
   Various new theorems in univalent mathematics written in Agda
   -------------------------------------------------------------

   Martin Escardo and collaborators
   2010--2022--∞, continuously evolving.
   https://www.cs.bham.ac.uk/~mhe/
   https://github.com/martinescardo/TypeTopology

   The main new results are about compact types, totally separated
   types, compact ordinals and injective types, but there are many
   other things (see the clickable index below).

   * Our main use of this development is as a personal blackboard or
     notepad for our research. In particular, some modules have better
     and better results or approaches, as time progresses, with the
     significant steps kept, and with failed ideas and calculations
     eventually erased.

   * We offer this page as a preliminary announcement of results to be
     submitted for publication, of the kind we would get when we visit
     a mathematician's office.

   * We have also used this development for learning other people's
     results, and so some previously known constructions and theorems
     are included (sometimes with embellishments).

   * The required material on HoTT/UF has been developed on demand
     over the years to fullfil the needs of the above as they arise,
     and hence is somewhat chaotic. It will continue to expand as the
     need arises. Its form is the result of evolution rather than
     intelligent design (paraphrasing Linus Torvalds).

     Our lecture notes develop HoTT/UF in Agda in a more principled
     way, and offers better approaches to some constructions and
     simpler proofs of some (previously) difficult theorems.
     (https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)

     Our philosophy, here and in the lecture notes, is to work with a
     minimal Martin-Löf type theory, and use principles from HoTT/UF
     (existence of propositional truncations, function extensionality,
     propositional extensionality, univalence, propositional resizing)
     and classical mathematics (excluded middle, choice, LPO, WLPO) as
     explicit assumptions for the theorems, or for the modules, that
     require them. As a consequence, we are able to tell very
     precisely which assumptions of HoTT/UF and classical mathematics,
     if any, we have used for each construction, theorem or set of
     results. We also work, deliberately, with a minimal subset of
     Agda.

   * There is also a module that links some "unsafe" modules that use
     type theory beyond MLTT and HoTT/UF, which cannot be included in
     this safe-modules index: The system with type-in-type is
     inconsistent (as is well known), countable Tychonoff, and
     compactness of the Cantor type using countable Tychonoff.
     (https://www.cs.bham.ac.uk/~mhe/TypeTopology/UnsafeModulesIndex.html)

   * In our last count, this development has 95000 lines, including
     comments and blank lines.

   * A module dependency graph is available, updated manually from
     time to time.
     (https://www.cs.bham.ac.uk/~mhe/TypeTopology/dependency-graph.pdf)

   * There are some somewhat obsolete comments at the end of this
     file, explaining part of what we do in this development. See
     instead the comments in the various modules.

   * This has been tested with 2.6.2.1.

Click at the imported module names to navigate to them:

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module index where

\end{code}

Some of the main modules and module clusters:

\begin{code}

import Compactness
import TotalSeparatedness
import InjectiveTypes-article
import TheTopologyOfTheUniverse
import RicesTheoremForTheUniverse
import Ordinals
import LawvereFPT
import PartialElements
import Types2019
import MGS           -- Modular version of https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes
import PCFModules    -- By Tom de Jong
import Dyadics       -- By Tom de Jong
import CircleModules -- By Tom de Jong

\end{code}

The UF module (univalent foundations) has been developed, on demand,
for use in the preceding modules (and the modules below, too). The
modules UF-Yoneda and UF-IdEmbedding contain new results.

All modules in alphabetical order:

\begin{code}

import ADecidableQuantificationOverTheNaturals -- Proved by Martin Escardo, formalized by Chuangjie Xu.
import AlternativePlus
import ArithmeticViaEquivalence
import BanachFixedPointTheorem -- By Todd Waugh Ambridge
import BasicDiscontinuityTaboo
import BinaryNaturals
import BuraliForti
import CanonicalMapNotation
import CantorSchroederBernstein
import CantorSchroederBernstein-TheoryLabLunch
import CantorSearch
import Closeness              -- By Todd Waugh Ambridge and Martin Escardo
import Compactness
import CompactTypes
import CoNaturalsArithmetic
import CoNaturalsExercise
import CoNaturals
import ConvergentSequenceCompact
import ConvergentSequenceHasInf
-- import CubicalBinarySystem -- works with Agda 2.6.2 only and need the Cubical Library. By Martin Escardo and Alex Rice
import DcpoDinfinity                   -- By Tom de Jong
import DecidabilityOfNonContinuity
import DecidableAndDetachable
import Dedekind
import Density
import DisconnectedTypes
import DiscreteAndSeparated
import Dyadic
import DyadicOrder
import Dyadics
import Dominance
import DummettDisjunction
import Empty
import Escardo-Simpson-LICS2001        -- By Todd Waugh Ambridge
import ExtendedSumCompact
import Fin
import Fin-Properties
import FiniteHistoryDependentGames     -- By Martin Escardo and Paulo Oliva
import Finiteness-Universe-Invariance
import FailureOfTotalSeparatedness
import Frame-version1
import Frame                           -- By Ayberk Tosun
import InitialFrame                    -- By Ayberk Tosun
import CompactRegular                  -- By Ayberk Tosun
import GaloisConnection                -- By Ayberk Tosun
import AdjointFunctorTheoremForFrames  -- By Ayberk Tosun
import HeytingImplication              -- By Ayberk Tosun
import PatchLocale                     -- By Ayberk Tosun
import FreeGroup                       -- By Marc Bezem, Thierry Coquand, Dybjer, and Martin Escardo.
import FreeGroupOfLargeLocallySmallSet -- By Marc Bezem, Thierry Coquand, Dybjer, and Martin Escardo.
import FreeJoinSemiLattice             -- By Tom de Jong
import FreeSupLattice                  -- By Tom de Jong
import GeneralNotation
import GenericConvergentSequence
import HiggsInvolutionTheorem
import Id
import InfProperty
import InitialBinarySystem    -- More work than needed!
import InitialBinarySystem2   -- No need to work with subtype of normal elements.
import InjectiveTypes-article
import InjectiveTypes
import JoinSemiLattices                -- By Tom de Jong
import LawvereFPT
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
import List
import LPO
import Lumsdaine
import MGS-TypeTopology-Interface
import NaturalNumbers
import NaturalNumbers-Properties
import NaturalsAddition
import NaturalsOrder
import Negation
import NonCollapsibleFamily
import NonSpartanMLTTTypes
import SigmaDiscreteAndTotallySeparated
import SRTclosure
import OrdinalArithmetic
import OrdinalArithmetic-Properties
import OrdinalCodes
import OrdinalNotationInterpretation
import OrdinalNotationInterpretation0
import OrdinalNotationInterpretation1
import OrdinalNotationInterpretation2
import OrdinalNotions
import OrdinalOfOrdinals
import OrdinalOfOrdinalsSuprema        -- By Tom de Jong
import OrdinalOfTruthValues
import OrdinalTaboos                   -- By Tom de Jong
import Ordinals
import OrdinalsClosure
import Ordinals
import OrdinalsFreeGroup
import OrdinalsType
import OrdinalsType-Injectivity
import OrdinalsWellOrderArithmetic
import OrdinalsWellOrderTransport
import P2
import PairFun
import PartialElements
import Pi
import Plus
import PlusOneLC
import Plus-Properties
import PropInfTychonoff
import PropTychonoff
import QuasiDecidable
import FreeGroupOfLargeLocallySmallSet
import RicesTheoremForTheUniverse
import RootsTruncation
import Sequence
import SemiDecidable                   -- By Tom de Jong
import Sigma
import SimpleTypes
import SliceAlgebras
import SliceEmbedding
import SliceIdentityViaSIP
import Slice
import SliceMonad
import SpartanMLTT
import SpartanMLTT-List
import SquashedCantor
import SquashedSum
import OrderNotation
import Swap
import sigma-sup-lattice
import sigma-frame
import TheTopologyOfTheUniverse
import TotallySeparated
import ToppedOrdinalArithmetic
import ToppedOrdinalsType
import Two
import Two-Properties
import UnivalenceFromScratch
import Unit
import Unit-Properties
import Universes
import WeaklyCompactTypes
import WellOrderingTaboo -- By Tom de Jong, based on a theorem by Andrew Swan
import W
import W-Properties
import WLPO
import UF-Base
import UF-Choice
import UF-Classifiers
import UF-Classifiers-Old
import UF-Connected
import UF-Embeddings
import UF-EquivalenceExamples
import UF-Equiv-FunExt
import UF-Equiv
import UF-ExcludedMiddle
import UF-Factorial
import UF-FunExt-from-Naive-FunExt -- By Cory Knapp
import UF-FunExt-Properties
import UF-Lower-FunExt
import UF-FunExt
import UF-hlevels
import UF-IdEmbedding
import UF-ImageAndSurjection
import UF-ImageAndSurjection-F
import UF-Knapp-UA
import UF-KrausLemma
import UF-LeftCancellable
import UF-Miscelanea
import UF-Powerset
import UF-Powerset-Fin                 -- By Tom de Jong
import UF-PropIndexedPiSigma
import UF-PropTrunc
import UF-PropTrunc-F
import UF-Quotient                     -- By Tom de Jong
import UF-Large-Quotient
import UF-Quotient-F
import UF-Quotient-Replacement         -- By Tom de Jong
import UF-Retracts-FunExt
import UF-Retracts
import UF-Section-Embedding
import UF-Size
import UF-StructureIdentityPrinciple  -- Old, probably delete.
import UF-SIP                         -- New, better, version.
import UF-SIP-Examples
import UF-SIP-IntervalObject
import UF-Subsingletons-FunExt
import UF-Subsingletons
import UF-Subsingleton-Combinators
import UF-UA-FunExt
import UF-Univalence
import UF-UniverseEmbedding
import UF-Yoneda

\end{code}

Everything again to make sure we didn't forget anything above.

\begin{code}

import everything-safe

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

The module dependency graph: http://www.cs.bham.ac.uk/~mhe/TypeTopology/manual.pdf

The following module investigates the notion of compact set. A
set X is compact iff

   (p : X → 𝟚) → (Σ x ꞉ X , p x ≡ ₀) + Π x ꞉ X , p x ≡ ₁

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

  (p : ℕ∞ → 𝟚) → ((n : ℕ) → p (under n) ≡ ₁) + ¬ ((n : ℕ) → p (under n) ≡ ₁).

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
import ConvergentSequenceHasInf

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
