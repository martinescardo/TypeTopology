Martin Escardo, 1st January 2022

Almost all modules. We comment out the unsafe one, the ones that
depend on the cubical library, and the ones that cause circularity
when this is imported from index.lagda and AllModulesIndex.

This is automatically generated, with the modules mentioned above
excluded manually.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module everything-safe where

import MLTT.index
import AdjointFunctorTheoremForFrames
-- import AllModulesIndex
import ArithmeticViaEquivalence
import BanachFixedPointTheorem
import BinaryNaturals
import Notation.CanonicalMap
-- import CantorCompact
import CantorSchroederBernstein
import CantorSchroederBernstein-TheoryLabLunch
import Closeness
import CompactRegular
-- import CountableTychonoff
-- import CubicalBinarySystem
import DomainTheory.index
import DecidableAndDetachable
import Dedekind
import Dominance
import DummettDisjunction
import Escardo-Simpson-LICS2001
-- import everything
-- import everything-safe
import Games.index
import Finiteness-Universe-Invariance
import Fin
import Fin-Properties
import Frame
import Frame-version1
import FreeGroup
import FreeGroupOfLargeLocallySmallSet
import FreeJoinSemiLattice
import FreeSupLattice
import GaloisConnection
import Notation.General
import Groups
import HeytingImplication
import HiggsInvolutionTheorem
-- import index
import InitialBinarySystem2
import InitialBinarySystem
import InitialFrame
import JoinSemiLattices
import LawvereFPT
import LexicographicOrder
import Lifting.index
import Lumsdaine
import NaturalsAddition
import NaturalsOrder
import NonCollapsibleFamily
import Nucleus
import Notation.Order
import Ordinals
import P2
import PairFun
import PatchLocale
import PCF
import PlusOneLC
import Poset
import QuasiDecidable
import RootsTruncation
import SemiDecidable
import Sequence
import sigma-frame
import sigma-sup-lattice
import SliceAlgebras
import SliceEmbedding
import SliceIdentityViaSIP
import Slice
import SliceMonad
import SpartanMLTT-List
import SRTclosure
import Swap
-- import Type-in-Type-False
import Types2019
import UF.Base
import UF.Choice
import UF.Classifiers
import UF.Classifiers-Old
import UF.Connected
import UF.Embeddings
import UF.EquivalenceExamples
import UF.Equiv-FunExt
import UF.Equiv
import UF.ExcludedMiddle
import UF.Factorial
import UF.FunExt-from-Naive-FunExt
import UF.FunExt
import UF.FunExt-Properties
import UF.hlevels
import UF.IdEmbedding
import UF.ImageAndSurjection-F
import UF.ImageAndSurjection
import UF.Knapp-UA
import UF.KrausLemma
import UF.Large-Quotient
import UF.LeftCancellable
import UF.Lower-FunExt
import UF.Miscelanea
import UF.Powerset-Fin
import UF.Powerset
import UF.PropIndexedPiSigma
import UF.PropTrunc-F
import UF.PropTrunc
import UF.Quotient-F
import UF.Quotient
import UF.Quotient-Replacement
import UF.Retracts-FunExt
import UF.Retracts
import UF.Section-Embedding
import UF.SIP-Examples
import UF.SIP-IntervalObject
import UF.SIP
import UF.Size
import UF.StructureIdentityPrinciple
import UF.Subsingleton-Combinators
import UF.Subsingletons-FunExt
import UF.Subsingletons
import UF.UA-FunExt
import UF.Univalence
import UF.UniverseEmbedding
import UF.Yoneda
import UnivalenceFromScratch
-- import UnsafeModulesIndex

\end{code}
