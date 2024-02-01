   TypeTopology

   Various new theorems in univalent mathematics written in Agda
   -------------------------------------------------------------

   Martin Escardo and collaborators,
   2010--2024--∞, continuously evolving.
   https://www.cs.bham.ac.uk/~mhe/
   https://github.com/martinescardo/TypeTopology

   Tested with Agda 2.6.4

   * Our main use of this development is as a personal blackboard or
     notepad for our research and that of collaborators. In
     particular, some modules have better and better results or
     approaches, as time progresses, with the significant steps kept,
     and with failed ideas and calculations eventually erased.

   * We offer this page as a preliminary announcement of results to be
     submitted for publication, of the kind we would get when we visit
     a mathematician's office.

   * We have also used this development for learning other people's
     results, and so some previously known constructions and theorems
     are included (sometimes with embellishments).

   * The required material on HoTT/UF has been developed on demand
     over the years to fulfill the needs of the above as they arise,
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
     Agda. See below for more about the philosophy.

   * There is also a module that links some "unsafe" modules that use
     type theory beyond MLTT and HoTT/UF, which cannot be included in
     this safe-modules index: The system with type-in-type is
     inconsistent (as is well known), countable Tychonoff, and
     compactness of the Cantor type using countable Tychonoff.

     (https://www.cs.bham.ac.uk/~mhe/TypeTopology/AllModulesIndex.html)

   * In our last count, on 24th October 2023, this development has
     650 files and 180k lines of code, including comments and blank
     lines. But we don't update the count frequently.

Philosophy of the repository
----------------------------

   * We adopt the univalent point of view, even in modules which don't
     assume the univalence axiom. In particular, we take seriously the
     distinction between types that are singletons (contractible),
     propositions, sets, 1-groupoids etc., even when the univalence
     axiom, or its typical consequences such as function
     extensionality and propositional extensionality, are not needed
     to reason about them.

   * We work in a minimal version of intensional Martin Löf Type
     Theory, with very few exceptions, which we refer to as Spartan
     MLTT. This is compatible with the UniMath approach.

   * We adopt the Agda flag exact-split, so that Agda definitions by
     pattern matching are definitional equalities, to stay as close as
     Agda can check to the above MLTT.

   * We work in a minimal subset of Agda to implement Spartan MLTT and
     work with it. In particular, we restrict ourselves to safe
     features (with the flags --safe --no-sized-types --no-guardedness).

   * Some functions, and theorems, and definitions need HoTT/UF
     axioms. They are always given explicitly as
     assumptions. Postulates are not allowed in this development.

   * The development is mostly constructive. A few theorems have
     non-constructive, explicit assumptions, such as excluded middle,
     or choice and global choice. One example is
     Cantor-Schröder-Bernstein for arbitrary (homotopy) types, which
     was published in the Journal of Homotopy and Related Structures
     (written in mathematical vernacular as advanced in the HoTT book
     and originally proposed by Peter Aczel).

   * We don't assume propositional resizing as Voevodsky and UniMath
     do. But there are some theorems whose hypotheses or conclusions
     involve propositional resizing (as an axiom, rather than as a
     rule of the type theory as unimath does).

   * The general idea is that any theorem here should be valid in any
     ∞-topos.

   * In particular, we don't use Cubical Agda features, deliberately,
     because at present it is not known whether (some) cubical type
     theory has an interpretation in any ∞ topos.

   * However, by fulfilling the HoTT hypotheses with Cubical-Agda
     implementations, we should be able to run the constructions and
     proofs given here, so that we get constructivity in the
     computational sense (as opposed to constructivity in the sense of
     validity in any (∞-)topos).

Click at the imported module names to navigate to them:

\begin{code}

{-# OPTIONS --safe --without-K #-}

module index where

import BinarySystems.index
import CantorSchroederBernstein.index
import Categories.index
import Circle.index
import CoNaturals.index
import ContinuityAxiom.index
import Coslice.index
import CrossedModules.index
import DedekindReals.index
import DomainTheory.index
import Dominance.index
import Duploids.index
import Dyadics.index
import DyadicsInductive.index
import EffectfulForcing.index
import Factorial.index
import Field.index
import Fin.index
import Games.index
import Groups.index
import InjectiveTypes.index
import Integers.index
import Iterative.index
import Lifting.index
import Locales.index
import MGS.index
import MLTT.index
import MetricSpaces.index
import Modal.index
import Naturals.index
import Notation.index
import NotionsOfDecidability.index
import Ordinals.index
import PathSequences.index
import PCF.index
import OrderedTypes.index
import Quotient.index
import Relations.index
import Rationals.index
import Slice.index
import TWA.index
import Taboos.index
import TypeTopology.index
import UF.index
import Various.index
import W.index
import WildCategories.index

\end{code}

TODO. Explain what each of the above does here.

The above includes only the --safe modules. A list of all modules is here:

https://www.cs.bham.ac.uk/~mhe/TypeTopology/AllModulesIndex.html
