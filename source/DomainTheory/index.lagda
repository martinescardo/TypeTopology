Tom de Jong, 4 June 2019
Updated 23 December 2021
Updated 12 and 14 June 2022
Updated 30 October 2023 (by Ayberk Tosun)
Updated 6 November 2023 (by Ayberk Tosun)
Updated 31 May 2024 (by Tom de Jong)
Updated 23 June 2024 (by Tom de Jong)
Updated 3 and 8 July 2024 (by Tom de Jong)

Index for the formalization of domain theory, briefly describing the contents of
each directory, ordered almost¹ alphabetically by directory name.
(¹ Basics is first.)

Several additional domain-theoretic formalization targets are listed at the end.

─────────────────────────────────────────────────────────────────────
This accompanies the PhD thesis
  Domain Theory in Constructive and Predicative Univalent Foundations
  Tom de Jong
  School of Computer Science, University of Birmingham
  https://etheses.bham.ac.uk/id/eprint/13401/

  Updated versions:
  https://arxiv.org/abs/2301.12405
  https://tdejong.com/writings/phd-thesis.pdf

  Submitted: 30 September 2022
  Defended:  20 December  2022
  Accepted:   1 February  2023
─────────────────────────────────────────────────────────────────────

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DomainTheory.index where

{- Basics

1. Basic definitions of directed complete posets and Scott continuous maps
2. Exponentials of (pointed) dcpos
3. Least fixed points of Scott continuous maps
4. Various general definitions and facts on directed complete posets and Scott
   continuous maps, e.g. embedding-projection pairs, locally small dcpos, etc.
5. Definitions and properties of pointed dcpos and strict Scott continuous maps
6. Useful facts about sup-complete dcpos, e.g. the directification of families
7. Definitions and basic properties of the way-below relation, including
   compactness

(B1)─(B4) These files are due to Brendan Hart and were ported to TypeTopology by
          Martín Escardó, cf. PCF.Lambda.index.lagda.
-}

import DomainTheory.Basics.Dcpo            -- (1)
import DomainTheory.Basics.Exponential     -- (2)
import DomainTheory.Basics.LeastFixedPoint -- (3)
import DomainTheory.Basics.Miscelanea      -- (4)
import DomainTheory.Basics.Pointed         -- (5)
import DomainTheory.Basics.SupComplete     -- (6)
import DomainTheory.Basics.WayBelow        -- (7)

import DomainTheory.Basics.Curry               -- (B1)
import DomainTheory.Basics.FunctionComposition -- (B2)
import DomainTheory.Basics.Products            -- (B3)
import DomainTheory.Basics.ProductsContinuity  -- (B4)


{- BasesAndContinuity

1. The theory of small (compact) bases
2. With univalence and set replacement, the type of small compact bases has
   split support (j.w.w. Ayberk Tosun; added 4 & 5 October 2023)
3. The theory of continuous/algebraic dcpos
4. A discussion on possible definitions of continuous dcpo
5. Continuous/algebraic dcpos in an impredicative setting (Simcha van Collem;
   added October 2023)
6. The Ind-completion is used to discuss the notion of (structurally/pseudo-)
   continuous dcpos
7. Using step functions we show that sup-complete dcpos with small compact
   bases are closed under exponentials
8. Definition of the notion of a Scott domain (by Ayberk Tosun)
-}

import DomainTheory.BasesAndContinuity.Bases                   -- (1)
import DomainTheory.BasesAndContinuity.CompactBasis            -- (2)
import DomainTheory.BasesAndContinuity.Continuity              -- (3)
import DomainTheory.BasesAndContinuity.ContinuityDiscussion    -- (4)
import DomainTheory.BasesAndContinuity.ContinuityImpredicative -- (5)
import DomainTheory.BasesAndContinuity.IndCompletion           -- (6)
import DomainTheory.BasesAndContinuity.StepFunctions           -- (7)
import DomainTheory.BasesAndContinuity.ScottDomain             -- (8)

{- Bilimits

1. Bilimits of directed diagrams
2. Specializing to bilimits of ℕ-indexed diagrams
3. Scott's famous D∞ that is isomorphic to its own function space
-}

import DomainTheory.Bilimits.Directed   -- (1)
import DomainTheory.Bilimits.Sequential -- (2)
import DomainTheory.Bilimits.Dinfinity  -- (3)

{- Examples

1. The extended partial Dedekind reals as a pointed dcpo.
   [Added 9 January 2026]
2. The ideal completion of the dyadics is a nice example of a continuous dcpo
   (with a small basis) that cannot be algebraic as it has no compact elements
   at all.
3. The lifting of a large proposition P is an algebraic dcpo that has a small
   (compact) basis if and only if P is suitably small.
4. The type Ω of propositions is an example of a pointed algebraic dcpo with
   the booleans giving a small compact basis
5. The large poset of small ordinals is an example of an algebraic dcpo with no
   small compact basis
   [Added 31 May 2024]
6. The powerset is an examples of a pointed algebraic dcpo with lists giving a
   small compact basis (through Kuratowski finite subsets)
-}

import DomainTheory.Examples.ExtendedPartialDedekindReals -- (1)
import DomainTheory.Examples.IdlDyadics                   -- (2)
import DomainTheory.Examples.LiftingLargeProposition      -- (3)
import DomainTheory.Examples.Omega                        -- (4)
import DomainTheory.Examples.Ordinals                     -- (5)
import DomainTheory.Examples.Powerset                     -- (6)

{- IdealCompletion

1. Construction of the rounded ideal completion of an abstract basis
2. Properties of the ideal completion, e.g. it has a small compact basis
3. Through the ideal completion, every continuous dcpo with a small basis is a
   continuous retract of an algebraic dcpo with a small compact basis
-}

import DomainTheory.IdealCompletion.IdealCompletion -- (1)
import DomainTheory.IdealCompletion.Properties      -- (2)
import DomainTheory.IdealCompletion.Retracts        -- (3)

{- Lifting

1. Freely adding a least element to a dcpo
2. The lifting is the free pointed dcpo on a set
3. The lifting of a set is algebraic with a small compact basis
-}

import DomainTheory.Lifting.LiftingDcpo         -- (1)
import DomainTheory.Lifting.LiftingSet          -- (2)
import DomainTheory.Lifting.LiftingSetAlgebraic -- (3)

{- ScottModelOfPCF

0. Combinatory version of PCF
1. Denotational semantics of the K, S and ifZero combinators of PCF
2. The Scott model of the typed programming language PCF
-}

import DomainTheory.ScottModelOfPCF.PCF             -- (0)
import DomainTheory.ScottModelOfPCF.PCFCombinators  -- (1)
import DomainTheory.ScottModelOfPCF.ScottModelOfPCF -- (2)

{- Taboos (added 23 June 2024)

1. If the flat poset with carrier 𝟙 + ℕ is ω-complete/directed complete, then
   LPO holds.
-}

import DomainTheory.Taboos.ClassicalLiftingOfNaturalNumbers

{- Topology (by Ayberk Tosun)

0. The definition of the Scott topology of a dcpo
1. Some properties of the Scott topology of a dcpo

-}

import DomainTheory.Topology.ScottTopology           -- (0)
import DomainTheory.Topology.ScottTopologyProperties -- (1)

{-
  In the locale theory development, some results on the pointfree topology of
  domains have been proved by Ayberk Tosun. Most importantly, the fact that the
  Scott locale of a Scott domain is a spectral locale has been proved, which was
  previously listed as an additional formalization target in the list at the
  bottom of this module.

  Such results on the pointfree topology of domains can be found in the
  directory `Locales/ScottLocale`. The proof of spectrality is in the module
  `Locales.ScottLocale.ScottLocalesOfScottDomains`.
-}

{- Index files for papers -}

import DomainTheory.Continuous-and-algebraic-domains
import DomainTheory.Part-I
import DomainTheory.Part-II

\end{code}

Additional formalization targets
────────────────────────────────

The Formalization chapter in the aforementioned PhD thesis
(https://arxiv.org/abs/2301.12405) details a few things (in the form of specific
lemmas) that have been left unformalized.

We present a succinct list of domain-theoretic formalization targets here:

1. Complete the formalization that bounded complete (continuous) dcpos with a
   small basis are closed under exponentials. It follows from the case of
   algebraic domains through a lemma that is left unformalized.
   See DomainTheory.BasesAndContinuity.StepFunctions for details.

2. Formalize the untyped λ-calculus and its interpretation in Scott's D∞.
   See DomainTheory.Bilimits.Dinfinity for the construction of D∞.

3. Formalize the results in reverse mathematics and delta-complete posets.
   See Chapter 6 of the PhD thesis for details.

Item 2 should be a fun challenge for a student with an interest in
(domain-theoretic semantics of) programming languages.
