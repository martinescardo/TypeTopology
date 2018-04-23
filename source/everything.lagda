   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Martin Escardo, 2010--
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

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
   before. Now it it has been modularized.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

You can navigate this set of files by clicking at words or
symbols to get to their definitions.

The module dependency graph: http://www.cs.bham.ac.uk/~mhe/agda-new/manual.pdf

The following module investigates the notion of omniscience set. A
set X is omniscient iff

   (p : X → 𝟚) → (Σ \(x : X) → p x ≡ ₀) + Π \(x : X) → p x ≡ ₁

\begin{code}

import OmniscientTypes

\end{code}

The omniscience of ℕ is a contructive taboo, known as LPO, which is an
undecided proposition in our type theory. Nevertheless, we can show
that the function type LPO→ℕ is omniscient:

\begin{code}

import LPO

\end{code}

See also:

\begin{code}

import WLPO

\end{code}

An example of an omniscient set is ℕ∞, which intuitively (and under
classical logic) is ℕ ∪ { ∞ }, defined in the following module:

\begin{code}

import GenericConvergentSequence 

\end{code}

But it is more direct to show that ℕ∞ is searchable, and get
omniscience as a corollary:

\begin{code}

import SearchableTypes
import ConvergentSequenceSearchable 

\end{code}

An interesting consequence of the omniscience of ℕ∞ is that the
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

Another example of searchable set is the type of univalent
propositions (proved in the above module Searchable).

Given countably many searchable sets, one can take the disjoint sum
with a limit point at infinity, and this is again a searchable
sets. This construction is called the squashed sum of the countable
family searchable sets. It can be transfinitely iterated to produce
increasingly complex searchable ordinals.

\begin{code}

import SquashedSum
import SearchableOrdinals
import LexicographicSearch
import ConvergentSequenceInfSearchable

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

import CountableTychonoff 
import CantorSearchable 

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

import UF-InjectiveTypes

\end{code}

This uses properties of products indexed by univalent propositions,
first that it is isomorphic to any of its factors:

\begin{code}

import UF-PropIndexedPiSigma

\end{code}

And, more subtly, that a product of searchable sets indexed by a
univalent proposition is itself searchable:

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

import ExtendedSumSearchable

\end{code}

The following modules define 𝟚-compactness and study its interaction
with discreteness and total separatedness, with applications to simple
types. We get properties that resemble those of the model of
Kleene-Kreisel continuous functionals of simple types, with some new
results.

\begin{code}

import TotallySeparated
import 2CompactTypes
import SimpleTypes
import FailureOfTotalSeparatedness 

\end{code}

All modules, to check compilation.

\begin{code}

import 2CompactTypes
import ADecidableQuantificationOverTheNaturals
import ArithmeticViaEquivalence
import BasicDiscontinuityTaboo
import BinaryNaturals
import CantorSearchable
import CoNaturalsExercise
import CoNaturals
import ConvergentSequenceInfSearchable
import ConvergentSequenceSearchable
import CountableTychonoff
import DecidabilityOfNonContinuity
import DecidableAndDetachable
import DiscreteAndSeparated
import Dominance
import DummettDisjunction
import ExhaustibleTypes
import ExtendedSumSearchable
import FailureOfTotalSeparatedness
import GenericConvergentSequence
import HiggsInvolutionTheorem
import InfSearchable
import LeftOvers
import LexicographicOrder
import LexicographicSearch
import LPO
import NaturalsAddition
import NonCollapsibleFamily
import OmniscientTypes
import OrdinalCodes
import PlusOneLC
import PropTychonoff
import RicesTheoremForTheUniverse
import SearchableOrdinals
import SearchableTypes
import Sequence
import SimpleTypes
import SpartanMLTT
import SquashedSum
import TheTopologyOfTheUniverse
import TotallySeparated
import UF-Base
import UF-Choice
import UF-Embedding
import UF-EquivalenceExamples
import UF-Equiv-FunExt
import UF-Equiv
import UF-FunExt
import UF-Historic
import UF-IdEmbedding
import UF-ImageAndSurjection
import UF-InjectiveTypes
import UF-KrausLemma
import UF-LeftCancellable
import UF-PropIndexedPiSigma
import UF-PropTrunc
import UF-Retracts-FunExt
import UF-Retracts
import UF-SetExamples
import UF-Subsingletons-Equiv
import UF-Subsingletons-FunExt
import UF-Subsingletons
import UF-Subsingletons-Retracts
import UF-Two-Prop-Density
import UF-UA-FunExt
import UF-Univalence
import UF-Yoneda
import UnivalenceFromScratch
import WLPO

\end{code}
