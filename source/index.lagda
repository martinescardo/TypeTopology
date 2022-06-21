
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
     (https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/)

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

   * In our last count, this development has 97000 lines, including
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

import MLTT.index
import UF.index
import Notation.index
import TypeTopology.index
import Ordinals.index
import Groups.index
import CantorSchroederBernstein.index
import LawvereFPT
import Types2019
import MGS.index          -- Modular version of https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes
import DomainTheory.index -- By Tom de Jong (started with Martin Escardo)
import Dyadics.index      -- By Tom de Jong
import Circle.index       -- By Tom de Jong
\end{code}

The UF module (univalent foundations) has been developed, on demand,
for use in the preceding modules (and the modules below, too). The
modules UF.Yoneda and UF-IdEmbedding contain new results.

All modules in alphabetical order:

\begin{code}

import ArithmeticViaEquivalence
import BanachFixedPointTheorem -- By Todd Waugh Ambridge
import Taboos.index
import BinaryNaturals
import Closeness              -- By Todd Waugh Ambridge and Martin Escardo
-- import CubicalBinarySystem -- works with Agda 2.6.2 only and need the Cubical Library. By Martin Escardo and Alex Rice
import DecidableAndDetachable
import Dedekind
import Dominance
import DummettDisjunction
import Escardo-Simpson-LICS2001        -- By Todd Waugh Ambridge
import Fin
import Fin-Properties
import Games.index                     -- By Martin Escardo and Paulo Oliva
import Finiteness-Universe-Invariance
import Frame-version1
import Locales.index                   -- By Ayberk Tosun
import FreeJoinSemiLattice             -- By Tom de Jong
import FreeSupLattice                  -- By Tom de Jong
import HiggsInvolutionTheorem
import InitialBinarySystem    -- More work than needed!
import InitialBinarySystem2   -- No need to work with subtype of normal elements.
import InjectiveTypes.index
import JoinSemiLattices                -- By Tom de Jong
import LawvereFPT
import LexicographicOrder
import Lifting.index
import List
import Lumsdaine
import NaturalsAddition
import NaturalsOrder
import NonCollapsibleFamily
import NonSpartanMLTTTypes

import SRTclosure
import Ordinals
import P2
import PairFun
import PlusOneLC
import QuasiDecidable
import RootsTruncation
import Sequence
import SemiDecidable                   -- By Tom de Jong
import sigma-sup-lattice
import sigma-frame
import UnivalenceFromScratch
import Swap

\end{code}
