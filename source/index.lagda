   [T y p e T o p o l o g y](https://github.com/martinescardo/TypeTopology)

   2010--2026--∞, continuously evolving.

   **Various new theorems in constructive univalent mathematics written in Agda**

   [Martin Escardo](https://www.cs.bham.ac.uk/~mhe/) and [collaborators](https://github.com/martinescardo/TypeTopology#current-typetopology-contributors-in-alphabetical-order-of-first-name).

   Tested with [Agda](https://agda.readthedocs.io/) 2.8.0 and 2.9.0.
   This HTML rendering was automatically generated from commit to-be-filled-automatically.

   * Our main use of this development is as a personal blackboard or
     notepad for our research and that of collaborators. In
     particular, some modules have better and better results or
     approaches, as time progresses, with the significant steps kept,
     and with failed ideas and calculations eventually erased.

   * The purpose of TypeTopology is to explain mathematics to people,
     and not only to computers. The name TypeTopology was chosen both
     because of the well-known [connection of topology with constructive
     mathematics](https://doi.org/10.1093/oso/9780198537359.003.0005) and because homotopy theory is a branch of topology.

   * We offer this page as a preliminary announcement of results to be
     [submitted for publication](https://github.com/martinescardo/TypeTopology#academic-publications-and-preprints-resulting-from-typetopology), of the kind we would get when we visit
     a mathematician's office.

   * We have also used this development for learning other people's
     results, and so some previously known constructions and theorems
     are included (sometimes with embellishments).

   * The required material on HoTT/UF has been developed on demand
     over the years to fulfill the needs of the above as they arise,
     and hence its organization reflects that history rather than a
     plan. It will continue to expand and improve as the need arises.

     Our [MGS lecture notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/) develop HoTT/UF in Agda in a more
     principled way, and offer better approaches to some
     constructions and simpler proofs of some (previously) difficult
     theorems. The directory [MGS](https://www.cs.bham.ac.uk/~mhe/TypeTopology/MGS.index.html) of this development has a
     modular version of the notes, with the prose deliberately left
     out.

     Our philosophy, here and in the lecture notes, is to work with a
     minimal Martin-Löf type theory, and use principles from HoTT/UF
     (existence of propositional truncations, function extensionality,
     propositional extensionality, univalence, propositional resizing,
     etc.)  and classical mathematics (excluded middle, choice, LPO,
     WLPO) as explicit assumptions for the theorems, or for the
     modules, that require them. As a consequence, we are able to tell
     very precisely which assumptions of HoTT/UF and classical
     mathematics, if any, we have used for each construction, theorem
     or set of results. We also work, deliberately, with a minimal
     subset of Agda. See below for more about the philosophy.

   * There is also a [module that links some "unsafe" modules](https://www.cs.bham.ac.uk/~mhe/TypeTopology/AllModulesIndex.html) that use
     type theory beyond MLTT and HoTT/UF, which cannot be included in
     this safe-modules index, such as the inconsistency of
     type-in-type, countable Tychonoff, and the compactness of the
     Cantor type from countable Tychonoff.

     That module also explains the [options used in TypeTopology](https://github.com/martinescardo/TypeTopology/blob/master/typetopology.agda-lib) to
     control safety and, to the extent this is currently possible, to
     fix which type theory is used. The safe modules are also checked
     with [Mikan](https://codeberg.org/1lab/mikan), with the options listed in [typetopology.mikan-lib](https://github.com/martinescardo/TypeTopology/blob/master/typetopology.mikan-lib), as a
     double check.

   * In our last count, on 2026-11-12, this development has 1015 Agda
     files with 306K lines of code, including comments and blank
     lines.

**Philosophy of the repository**

   * We adopt the univalent point of view, even in modules which don't
     assume the univalence axiom. In particular, we take seriously the
     distinction between types that are singletons (contractible),
     propositions, sets, 1-groupoids etc., even when the univalence
     axiom, or its typical consequences such as function
     extensionality and propositional extensionality, are not needed
     to reason about them.

   * We work in a minimal version of intensional Martin-Löf Type
     Theory, with very few exceptions, which we refer to as Spartan
     MLTT. This is compatible with the UniMath approach.

   * We adopt the Agda flag exact-split, so that Agda definitions by
     pattern matching are definitional equalities, to stay as close as
     Agda can check to the above MLTT.

   * We work in a minimal subset of Agda to implement Spartan MLTT and
     work with it. In particular, we restrict ourselves to safe
     features, with flags such as --safe --no-sized-types --no-guardedness
     and [more](https://github.com/martinescardo/TypeTopology/blob/master/typetopology.agda-lib).

   * Most of the time we prefer to use Σ types rather than records,
     although records are not forbidden, as they are equivalent to
     iterated Σ types. The reason for this is that UF has a number of
     constructions and theorems for Σ types that we often need to
     apply.

   * Some functions, theorems, and definitions need HoTT/UF
     axioms. They are always given explicitly as assumptions.
     Postulates are not allowed in this development.

   * The development is mostly constructive.

     A few theorems have non-constructive, explicit assumptions, such
     as excluded middle, or choice or global choice. One example is
     Cantor-Schröder-Bernstein for arbitrary (homotopy) types, which
     was published in the Journal of Homotopy and Related Structures
     (written in mathematical vernacular as advanced in the HoTT book
     and originally proposed by Peter Aczel). We also have Zorn's
     Lemma, the Well-Ordering Principle and more.

   * We work without propositional resizing, which Voevodsky and UniMath
     assume.

     But there are some theorems whose hypotheses or conclusions
     involve propositional resizing.

   * The general idea is that any theorem here should be valid in any
     ∞-topos, but some theorems will be valid only in special ∞-toposes,
     such as boolean toposes or other kinds of toposes.

   * In particular, we deliberately avoid Cubical Agda features,
     because at present it is not known whether (some) cubical type
     theory has an interpretation in any ∞-topos.

     However, by fulfilling the HoTT hypotheses with Cubical Agda
     implementations, we should be able to run the constructions and
     proofs given here, so that we get constructivity in the
     computational sense, as opposed to constructivity just in the
     sense of validity in any (∞-)topos.

   * Although our philosophy is based on HoTT/UF and ∞-toposes, it
     should be emphasized that much of what we do here also holds in
     the setoid model. In particular, this model validates function
     extensionality, the existence of propositional truncations and
     the existence of quotients, and some higher inductive types.

   * The files within most of the modules have extensive discussions
     in prose.

**The modules, by subject**

   The following imports only the `--safe` modules. See [AllModulesIndex](https://www.cs.bham.ac.uk/~mhe/TypeTopology/AllModulesIndex.html)
   for the list of all modules, and the [TypeTopology module descriptions](https://github.com/martinescardo/TypeTopologyModuleDescriptions/)
   for a fuller description of each directory.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module index where

\end{code}

**Foundations**

\begin{code}

import MLTT.index                  -- [Martin-Löf type theory](https://github.com/martinescardo/TypeTopologyModuleDescriptions#mltt).
import W.index                     -- [W-types](https://github.com/martinescardo/TypeTopologyModuleDescriptions#w).
import Notation.index              -- [General notation and conventions](https://github.com/martinescardo/TypeTopologyModuleDescriptions#notation).
import UF.index                    -- [Univalent foundations](https://github.com/martinescardo/TypeTopologyModuleDescriptions#uf).
import Quotient.index              -- [Set quotients](https://github.com/martinescardo/TypeTopologyModuleDescriptions#quotient).
import Relations.index             -- [Relations, Church-Rosser property, etc](https://github.com/martinescardo/TypeTopologyModuleDescriptions#relations).
import Fin.index                   -- [Notions of finiteness](https://github.com/martinescardo/TypeTopologyModuleDescriptions#fin).
import NotionsOfDecidability.index -- [Various notions of decidability](https://github.com/martinescardo/TypeTopologyModuleDescriptions#notionsofdecidability).
import Taboos.index                -- [Excluded middle, LPO, WLPO, LLPO, etc](https://github.com/martinescardo/TypeTopologyModuleDescriptions#taboos).

\end{code}

**Topology, domain theory and computation**

\begin{code}

import TypeTopology.index     -- [The intrinsic topology of types](https://github.com/martinescardo/TypeTopologyModuleDescriptions#typetopology).
import EffectfulForcing.index -- [Dialogue trees and effectful forcing](https://github.com/martinescardo/TypeTopologyModuleDescriptions#effectfulforcing).
import ContinuityAxiom.index  -- [A continuity axiom contradicts Curry-Howard](https://github.com/martinescardo/TypeTopologyModuleDescriptions#continuityaxiom).
import C-Spaces.index         -- [C-spaces as a continuous model of type theory](https://github.com/martinescardo/TypeTopologyModuleDescriptions#c-spaces).
import InductiveBars.index    -- [Bars, Brouwer's thesis and bar recursion](https://github.com/martinescardo/TypeTopologyModuleDescriptions#inductivebars).
import InjectiveTypes.index   -- [Injective types](https://github.com/martinescardo/TypeTopologyModuleDescriptions#injectivetypes).
import Lifting.index          -- [The lifting monad of partial elements](https://github.com/martinescardo/TypeTopologyModuleDescriptions#lifting).
import Dominance.index        -- [Dominances in the sense of Rosolini](https://github.com/martinescardo/TypeTopologyModuleDescriptions#dominance).
import DomainTheory.index     -- [Domain theory](https://github.com/martinescardo/TypeTopologyModuleDescriptions#domaintheory).
import PCF.index              -- [PCF and its Scott model](https://github.com/martinescardo/TypeTopologyModuleDescriptions#pcf).
import TWA.index              -- [Exact real search](https://github.com/martinescardo/TypeTopologyModuleDescriptions#twa).
import Locales.index          -- [Point-free topology](https://github.com/martinescardo/TypeTopologyModuleDescriptions#locales).

\end{code}

**Numbers**

\begin{code}

import Naturals.index         -- [Natural numbers](https://github.com/martinescardo/TypeTopologyModuleDescriptions#naturals).
import Integers.index         -- [Integers](https://github.com/martinescardo/TypeTopologyModuleDescriptions#integers).
import Rationals.index        -- [Rational numbers](https://github.com/martinescardo/TypeTopologyModuleDescriptions#rationals).
import Dyadics.index          -- [Dyadic rationals](https://github.com/martinescardo/TypeTopologyModuleDescriptions#dyadics).
import DyadicsInductive.index -- [Dyadic rationals, defined inductively](https://github.com/martinescardo/TypeTopologyModuleDescriptions#dyadicsinductive).
import BinarySystems.index    -- [Dyadic rationals via binary systems](https://github.com/martinescardo/TypeTopologyModuleDescriptions#binarysystems).
import DedekindReals.index    -- [Real numbers, in their Dedekind incarnation](https://github.com/martinescardo/TypeTopologyModuleDescriptions#dedekindreals).
import CoNaturals.index       -- [Conatural numbers](https://github.com/martinescardo/TypeTopologyModuleDescriptions#conaturals).

\end{code}

**Algebra**

\begin{code}

import Groups.index                            -- [UF-based group theory](https://github.com/martinescardo/TypeTopologyModuleDescriptions#groups).
import EGroups.index                           -- [Setoid-based group theory](https://github.com/martinescardo/TypeTopologyModuleDescriptions#egroups).
import Field.index                             -- [Fields](https://github.com/martinescardo/TypeTopologyModuleDescriptions#field).
import CrossedModules.index                    -- [Crossed modules](https://github.com/martinescardo/TypeTopologyModuleDescriptions#crossedmodules).
import AlgebraicStructuresForcingSethood.index -- [Structures that force sethood](https://github.com/martinescardo/TypeTopologyModuleDescriptions#algebraicstructuresforcingsethood).

\end{code}

**Order, ordinals and cardinals**

\begin{code}

import OrderedTypes.index             -- [Posets, lattices, frames, etc](https://github.com/martinescardo/TypeTopologyModuleDescriptions#orderedtypes).
import Ordinals.index                 -- [Ordinals and their arithmetic](https://github.com/martinescardo/TypeTopologyModuleDescriptions#ordinals).
import Iterative.index                -- [Iterative multisets, sets and ordinals](https://github.com/martinescardo/TypeTopologyModuleDescriptions#iterative).
import Cardinals.index                -- [Cardinals](https://github.com/martinescardo/TypeTopologyModuleDescriptions#cardinals).
import CantorSchroederBernstein.index -- [Schröder-Bernstein for arbitrary types](https://github.com/martinescardo/TypeTopologyModuleDescriptions#cantorschroederbernstein).

\end{code}

**Apartness and metric spaces**

\begin{code}

import Apartness.index    -- [Apartness relations](https://github.com/martinescardo/TypeTopologyModuleDescriptions#apartness).
import MetricSpaces.index -- [Metric spaces, without mentioning the reals](https://github.com/martinescardo/TypeTopologyModuleDescriptions#metricspaces).

\end{code}

**Homotopy type theory**

\begin{code}

import SyntheticHomotopyTheory.index -- [The circle and ℝP∞](https://github.com/martinescardo/TypeTopologyModuleDescriptions#synthetichomotopytheory).
import Modal.index                   -- [Reflective subuniverses and modalities](https://github.com/martinescardo/TypeTopologyModuleDescriptions#modal).
import Slice.index                   -- [The slice of a universe over a type](https://github.com/martinescardo/TypeTopologyModuleDescriptions#slice).
import Coslice.index                 -- [The coslice of a universe under a type](https://github.com/martinescardo/TypeTopologyModuleDescriptions#coslice).
import ReflexiveGraphs.index         -- [Reflexive graph lenses, after Sterling](https://github.com/martinescardo/TypeTopologyModuleDescriptions#reflexivegraphs).
import PathSequences.index           -- [A calculus of sequences of paths](https://github.com/martinescardo/TypeTopologyModuleDescriptions#pathsequences).

\end{code}

**Category theory**

\begin{code}

import WildCategories.index -- [Wild higher categories](https://github.com/martinescardo/TypeTopologyModuleDescriptions#wildcategories).
import Categories.index     -- [Category theory in univalent foundations](https://github.com/martinescardo/TypeTopologyModuleDescriptions#categories).
import Duploids.index       -- [Duploids, after Munch-Maccagnoni](https://github.com/martinescardo/TypeTopologyModuleDescriptions#duploids).

\end{code}

**Monads and games**

\begin{code}

import MonadOnTypes.index                   -- [Wild monads on types](https://github.com/martinescardo/TypeTopologyModuleDescriptions#monadontypes).
import RelativeMonadOnStructuredTypes.index -- [Relative monads](https://github.com/martinescardo/TypeTopologyModuleDescriptions#relativemonadonstructuredtypes).
import DiscreteGraphicMonoids.index         -- [Graphic monoids, after Lawvere](https://github.com/martinescardo/TypeTopologyModuleDescriptions#discretegraphicmonoids).
import Games.index                          -- [Games via selection functions](https://github.com/martinescardo/TypeTopologyModuleDescriptions#games).

\end{code}

**Miscellany**

\begin{code}

import Higgs.index      -- [Higgs' involution theorem and its consequences](https://github.com/martinescardo/TypeTopologyModuleDescriptions#higgs).
import Factorial.index  -- [Automorphism types and their combinatorics](https://github.com/martinescardo/TypeTopologyModuleDescriptions#factorial).
import Various.index    -- [Miscellaneous results of interest](https://github.com/martinescardo/TypeTopologyModuleDescriptions#various).
import gist.index       -- [Examples, discussions and experiments](https://github.com/martinescardo/TypeTopologyModuleDescriptions#gist).
import MGS.index        -- [A modular version](https://github.com/martinescardo/TypeTopologyModuleDescriptions#mgs) of our [HoTT/UF lecture notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/).
import deprecated.index -- [Superseded modules, kept for reference](https://github.com/martinescardo/TypeTopologyModuleDescriptions#deprecated).

\end{code}

This file is accessible from both

(1) https://www.cs.bham.ac.uk/~mhe/TypeTopology
(2) https://martinescardo.github.io/TypeTopology

We have that currently (1) redirects to (2), but in the future we may
choose a different redirection from (1), so please use (1) when citing
the html rendering of this repository.
