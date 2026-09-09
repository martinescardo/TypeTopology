Martin Escardo, 9th September 2026.

This file follows the definitions, lemmas, propositions, theorems,
examples and remarks of the paper

   Martín Hötzel Escardó
   Compact totally separated types
   https://www.cs.bham.ac.uk/~mhe/papers/compact-totally-separated.pdf

in the same order and with the same numbering, including the
mathematical discussions in its prose, so that a reader of the paper
can walk this file alongside it. The name of each entry is the number
the item has in the paper, and the comment after it is the LaTeX label
of that item.

Claims that the paper makes in running prose, outside proofs, appear
here too, under names beginning with Prose. Each of them is named in
the LaTeX source by \claim{name}, placed where the claim is made, and
the names are written out in order to the file main.claims when the
paper is typeset, so that the two lists can be compared. Claims about
models rather than about the theory, such as the ones about the
effective topos, are recorded as comments, since they are not
formalizable here.

We include all HoTT/UF assumptions as module parameters. They do not
include function extensionality because it follows from
univalence. However, the TypeTopology repository is careful to
minimize the number of assumptions for each result, and readers
interested in such foundational issues can follow the definitions
given here to find out exactly what assumptions each result uses.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.Size
open import UF.Univalence

module TypeTopology.CompactTotallySeparatedTypesArticle
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import MLTT.Spartan

open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open PropositionalTruncation pt

open import Apartness.Definition
      using (module Apartness ;
             is-tight ;
             is-irreflexive ;
             tight-types-are-¬¬-separated' ;
             tight-types-are-sets')
open Apartness pt      using (is-apartness ; apartness-is-irreflexive')

open import Notation.CanonicalMap
open import Rationals.Type      using (ℚ)
open import DedekindReals.Type fe' pe' pt
      using (ℝ ; ℝ-is-set ; canonical-map-ℚ-to-ℝ)
open import DedekindReals.Order fe' pe' pt using (ℚ-to-ℝ-is-embedding)
open import CoNaturals.UniversalProperty fe
      using (PRED-is-the-homotopy-final-coalgebra ; is-homomorphism)
open import NotionsOfDecidability.Complemented
open import Taboos.LPO
open import Taboos.MarkovsPrinciple
open import Taboos.WLPO
open import TypeTopology.DecidabilityOfNonContinuity fe₀
      using (continuous ;
             noncontinuous-map-gives-WLPO ;
             WLPO-gives-noncontinous-map ;
             ¬WLPO-iff-all-maps-are-¬¬-continuous ;
             MP-and-¬WLPO-give-that-all-functions-are-continuous)
open import TypeTopology.Density
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Hedberg
open import UF.ImageAndSurjection pt
open import UF.NotNotStablePropositions
open import UF.Powerset-MultiUniverse hiding (𝕋)
open import Quotient.FromSetReplacement pt fe' pe'
      using (set-quotients-from-set-replacement)
open import Quotient.GivesSetReplacement
      using (set-replacement-from-set-quotients-and-prop-trunc)
open import Quotient.Type using (set-quotients-exist)
open import UF.PairFun
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open import TypeTopology.FailureOfTotalSeparatedness fe₀
open import TypeTopology.GenericConvergentSequence
open import TypeTopology.SigmaDiscrete
open import TypeTopology.SimpleTypes fe pt
open import TypeTopology.TotallySeparated
open totally-separated-reflection fe pt
open total-separatedness-via-apartness pt
open import TypeTopology.CompactTypes
open CompactTypesPT pt
open import Fin.Topology using (Fin-Compact)
open import Fin.Type using (Fin)
open import MLTT.Plus-Properties using (+disjoint)
open import CantorSchroederBernstein.CSB-WLPO
      using (Π-compact-types-are-Π-Compact)
open import SyntheticHomotopyTheory.Circle.Construction pt (ua 𝓤₀)
      using (Tℤ ; loops-at-base-equivalent-to-ℤ)
 renaming (base to base-of-Tℤ)
open import TypeTopology.DisconnectedTypes
open import TypeTopology.ExtendedSumCompact fe
open import TypeTopology.ExtensionTotallySeparated
open import TypeTopology.GenericConvergentSequenceCompactness fe₀
open import TypeTopology.MicroTychonoff
open import TypeTopology.WeaklyCompactTypes fe pt
open import InjectiveTypes.Blackboard fe

open import Ordinals.Arithmetic fe
open import Ordinals.CompactnessOfSuprema ua pt
open import Ordinals.Closure fe
open import Ordinals.ConvergentSequence ua using (ω+𝟙-is-⊴-ℕ∞)
open import Ordinals.Equivalence
open import Ordinals.Injectivity
open ordinals-injectivity fe
open topped-ordinals-injectivity fe using () renaming (_↗_ to _↗ᵀ_)
open import Ordinals.LexicographicOrder
open import Ordinals.Maps using (is-simulation)
open import Ordinals.Notions hiding (is-irreflexive)
open import Ordinals.OrdinalOfOrdinals ua hiding (_≾_)
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open suprema pt sr
open import Ordinals.OrdinalOfTruthValues fe 𝓤₀ (pe 𝓤₀)
open import Ordinals.ShulmanTaboo fe (pe 𝓤₀)
      using (shulmans-taboo)
 renaming (_≺_ to _≺ˢ_)
open import Ordinals.Taboos
      using (Every-Discrete-Ordinal-Is-Trichotomous ;
             EM-if-Every-Discrete-Ordinal-Is-Trichotomous)
open import Ordinals.ToppedAdditionProperties ua
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.TotallySeparated
open import Ordinals.TrichotomousArithmetic fe
open import Ordinals.TrichotomousType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderArithmetic
open import TypeTopology.SquashedSum fe
open import TypeTopology.SquashedCantor fe
      using (Cantor ; 𝔻 ; 𝔻-Cantor-≃-Cantor)

open import Ordinals.BrouwerCodes
open import Ordinals.BrouwerCodesInterpretations ua pt sr
open import Ordinals.InfProperty
open import TypeTopology.LimitPoints
open import TypeTopology.MicroInfTychonoff fe
open import TypeTopology.SigmaTotallySeparated
      using (Σ-indexed-by-ℕ∞-is-totally-separated-if-family-at-∞-is-prop)

import Ordinals.BrouwerCodesDiscreteAndCompactInterpretations
import Ordinals.BrouwerCodesIntoInductiveRecursiveCodes
import Ordinals.FailureOfTotalSeparatedness
import Ordinals.FailureOfTrichotomy
import Ordinals.InductiveRecursiveCodesInterpretations
import Ordinals.LimitPoints

module BDC = Ordinals.BrouwerCodesDiscreteAndCompactInterpretations fe
module IRC = Ordinals.InductiveRecursiveCodesInterpretations fe
module OLP = Ordinals.LimitPoints fe
module BtoE = Ordinals.BrouwerCodesIntoInductiveRecursiveCodes fe
module FTS = Ordinals.FailureOfTotalSeparatedness ua pt sr
module FTr = Ordinals.FailureOfTrichotomy ua pt sr

\end{code}

Section 2. Preliminaries

Labels: Section 2 = sec:foundations.

\begin{code}

-- def:decidable
Definition-2-1 : (X : 𝓤 ̇ ) → 𝓤 ̇
Definition-2-1 X = is-decidable X

-- def:logical-equivalence
Definition-2-2 : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
Definition-2-2 = _↔_

-- def:singleton
Definition-2-3 : 𝓤 ̇ → 𝓤 ̇
Definition-2-3 = is-singleton

-- def:singleton, unique existence
Definition-2-3' : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Definition-2-3' = ∃!

-- def:h-isolated
Definition-2-4 : {X : 𝓤 ̇ } → X → 𝓤 ̇
Definition-2-4 = is-h-isolated

-- def:h-isolated, sets
Definition-2-4' : 𝓤 ̇ → 𝓤 ̇
Definition-2-4' = is-set

-- thm:hedberg
Theorem-2-5 : {X : 𝓤 ̇ } (x : X)
            → ((y : X) → collapsible (x ＝ y))
            → (y : X) → is-prop (x ＝ y)
Theorem-2-5 = local-hedberg

-- def:Omega
Definition-2-6 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-6 = Ω

-- def:base-fiber
Definition-2-7 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
Definition-2-7 = fiber

-- def:equivalence
Definition-2-8 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Definition-2-8 = is-vv-equiv

-- def:surjection
Definition-2-9 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Definition-2-9 = is-surjection

-- def:embedding
Definition-2-10 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Definition-2-10 = is-embedding

-- claim embeddings-and-left-cancellability
Prose-embeddings-and-left-cancellability
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → is-embedding f
 → left-cancellable f
Prose-embeddings-and-left-cancellability = embeddings-are-lc

Prose-embeddings-and-left-cancellability'
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → left-cancellable f
 → is-set Y
 → is-embedding f
Prose-embeddings-and-left-cancellability' = lc-maps-into-sets-are-embeddings

\end{code}

The claim about the topological topos is about a model rather than
about the theory, and so is not formalizable here.

\begin{code}

-- claim rationals-embed-into-reals
Prose-rationals-embed-into-reals : is-embedding (canonical-map ℚ ℝ)
Prose-rationals-embed-into-reals = ℚ-to-ℝ-is-embedding

Prose-rationals-embed-into-reals' : is-set ℝ
Prose-rationals-embed-into-reals' = ℝ-is-set

-- def:complemented
Definition-2-11 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Definition-2-11 = is-complemented

-- def:subset
Definition-2-12 : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
Definition-2-12 {𝓤} {𝓥} = 𝓟 {𝓥} {𝓤}

-- def:image
Definition-2-13 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Definition-2-13 = image

-- def:small
Definition-2-14 : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
Definition-2-14 = is-small

Definition-2-14-locally : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
Definition-2-14-locally = is-locally-small

-- def:set-replacement
Definition-2-15 : 𝓤ω
Definition-2-15 = Set-Replacement pt

-- def:set-quotients
Definition-2-16 : 𝓤ω
Definition-2-16 = set-quotients-exist

-- claim set-replacement-and-quotients
Prose-set-replacement-and-quotients : Set-Replacement pt → set-quotients-exist
Prose-set-replacement-and-quotients = set-quotients-from-set-replacement

Prose-set-replacement-and-quotients' : set-quotients-exist → Set-Replacement pt
Prose-set-replacement-and-quotients' sq
 = set-replacement-from-set-quotients-and-prop-trunc sq pt

-- def:nn-separated
Definition-2-17 : 𝓤 ̇ → 𝓤 ̇
Definition-2-17 = is-¬¬-separated

-- lem:nn-separated-is-set
Lemma-2-18 : {X : 𝓤 ̇ } → is-¬¬-separated X → is-set X
Lemma-2-18 = ¬¬-separated-types-are-sets fe'

-- def:apartness
Definition-2-19 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Definition-2-19 = is-apartness

-- def:apartness, tightness
Definition-2-19' : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Definition-2-19' = is-tight

-- claim tight-apartness-gives-set
Prose-tight-apartness-gives-set
 : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
 → is-apartness _♯_
 → (x y : X) → x ♯ y → x ≠ y
Prose-tight-apartness-gives-set = apartness-is-irreflexive'

Prose-tight-apartness-gives-¬¬-separated
 : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
 → is-irreflexive _♯_
 → is-tight _♯_
 → is-¬¬-separated X
Prose-tight-apartness-gives-¬¬-separated = tight-types-are-¬¬-separated'

Prose-tight-apartness-gives-set'
 : {X : 𝓤 ̇ } (_♯_ : X → X → 𝓥 ̇ )
 → is-irreflexive _♯_
 → is-tight _♯_
 → is-set X
Prose-tight-apartness-gives-set' _♯_ = tight-types-are-sets' _♯_ (fe _ _)

\end{code}

What the paper calls extreme density is called density in
TypeTopology, and the names below keep the TypeTopology spelling.

\begin{code}

-- def:dense, item:dense-fiber
Definition-2-20 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Definition-2-20 = is-dense

-- def:dense, item:dense-image
Definition-2-20' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Definition-2-20' f = is-empty (complement-of-image f)

-- def:dense, the two conditions are equivalent
Definition-2-20-equivalence
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → is-dense f ↔ is-empty (complement-of-image f)
Definition-2-20-equivalence = density-characterization pt

-- def:dense, density is a proposition
Definition-2-20-is-prop
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-prop (is-dense f)
Definition-2-20-is-prop = being-dense-is-prop fe'

-- lem:dense-into-nn-separated-rc
Lemma-2-21 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ } {j : X → Y} {f g : Π Z}
           → is-dense j
           → ((y : Y) → is-¬¬-separated (Z y))
           → f ∘ j ∼ g ∘ j
           → f ∼ g
Lemma-2-21 = dense-maps-into-¬¬-separated-types-are-rc'

-- lem:dense-into-nn-separated-rc, the constant family
Lemma-2-21' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {j : X → Y} {f g : Y → Z}
            → is-dense j
            → is-¬¬-separated Z
            → f ∘ j ∼ g ∘ j
            → f ∼ g
Lemma-2-21' = dense-maps-into-¬¬-separated-types-are-rc

-- lem:two-to-Omega-dense
Lemma-2-22 : 𝟚 → Ω 𝓤
Lemma-2-22 = 𝟚-to-Ω

-- def:global-choice
Definition-2-23 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-23 = Global-Choice

-- claim global-choice-reformulation
Prose-global-choice-reformulation : Global-Choice 𝓤 → Global-Choice' 𝓤
Prose-global-choice-reformulation = Global-Choice-gives-Global-Choice'

Prose-global-choice-reformulation' : Global-Choice' 𝓤 → Global-Choice 𝓤
Prose-global-choice-reformulation' = Global-Choice'-gives-Global-Choice

-- def:excluded-middle
Definition-2-24 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-24 = EM

-- def:lpo-wlpo
Definition-2-25 : 𝓤₀ ̇
Definition-2-25 = LPO

Definition-2-25' : 𝓤₀ ̇
Definition-2-25' = WLPO

-- claim compactness-of-N-is-LPO
Prose-compactness-of-N-is-LPO : is-compact ℕ ↔ LPO
Prose-compactness-of-N-is-LPO = compact-ℕ-gives-LPO fe₀ ,
                                LPO-gives-compact-ℕ fe₀

-- claim EM-LPO-WLPO
Prose-EM-LPO-WLPO : EM 𝓤₀ → LPO
Prose-EM-LPO-WLPO em = LPO'-gives-LPO
                        (λ u → em (is-finite u) (being-finite-is-prop fe₀ u))

Prose-EM-LPO-WLPO' : LPO → WLPO
Prose-EM-LPO-WLPO' = LPO-gives-WLPO fe₀

Prose-EM-LPO-WLPO'' : MP 𝓤₀ → WLPO → LPO
Prose-EM-LPO-WLPO'' = MP-and-WLPO-give-LPO fe₀

\end{code}

The claim that the taboos are independent of the foundation, holding
under classical logic and failing in the topological and effective
toposes, is about models rather than about the theory, and so is not
formalizable here.

\begin{code}

-- rem:weak-topological-topos
Remark-2-26 : WLPO ↔ (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
Remark-2-26 = WLPO-gives-noncontinous-map , noncontinuous-map-gives-WLPO

-- claim noncontinuity-and-WLPO
Prose-noncontinuity-and-WLPO : (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f) → WLPO
Prose-noncontinuity-and-WLPO = noncontinuous-map-gives-WLPO

Prose-noncontinuity-and-WLPO' : WLPO → (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
Prose-noncontinuity-and-WLPO' = WLPO-gives-noncontinous-map

Prose-noncontinuity-and-WLPO'' : ¬ WLPO ↔ ((f : ℕ∞ → ℕ) → ¬¬ continuous f)
Prose-noncontinuity-and-WLPO'' = ¬WLPO-iff-all-maps-are-¬¬-continuous

Prose-noncontinuity-and-WLPO'''
 : MP 𝓤₀ → ¬ WLPO → (f : ℕ∞ → ℕ) → continuous f
Prose-noncontinuity-and-WLPO'''
 = MP-and-¬WLPO-give-that-all-functions-are-continuous

-- def:retract
Definition-2-27 : 𝓥 ̇ → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Definition-2-27 Y X = retract Y of X

-- def:sum-map
Definition-2-28 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
                → (f : X → Y)
                → ((x : X) → A x → B (f x))
                → Σ A → Σ B
Definition-2-28 = pair-fun

-- lem:sum-map (1), item:sum-map-equiv
Lemma-2-29-1 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
               (f : X → Y) (g : (x : X) → A x → B (f x))
             → is-vv-equiv f
             → ((x : X) → is-vv-equiv (g x))
             → is-vv-equiv (pair-fun {A = A} {B = B} f g)
Lemma-2-29-1 = pair-fun-is-vv-equiv

-- lem:sum-map (2), item:sum-map-embedding
Lemma-2-29-2 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
               (f : X → Y) (g : (x : X) → A x → B (f x))
             → is-embedding f
             → ((x : X) → is-embedding (g x))
             → is-embedding (pair-fun {A = A} {B = B} f g)
Lemma-2-29-2 = pair-fun-is-embedding

-- lem:sum-map (3), item:sum-map-dense
Lemma-2-29-3 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
               (f : X → Y) (g : (x : X) → A x → B (f x))
             → is-dense f
             → ((x : X) → is-dense (g x))
             → is-dense (pair-fun {A = A} {B = B} f g)
Lemma-2-29-3 = pair-fun-dense

-- lem:sum-map (4), item:sum-map-retraction
Lemma-2-29-4 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
             → ((x : X) → retract (A x) of (B x))
             → retract (Σ A) of (Σ B)
Lemma-2-29-4 = Σ-retract

\end{code}

Section 3. Discreteness and total separatedness

Labels: Section 3 = sec:discrete-tot-sep.

\begin{code}

-- ex:NInf
Example-3-1 : 𝓤₀ ̇
Example-3-1 = ℕ∞

Example-3-1' : retract ℕ∞ of (ℕ → 𝟚)
Example-3-1' = ℕ∞-retract-of-Cantor fe₀

Example-3-1'' : {X : 𝓤 ̇ } (κ : X → 𝟙 + X)
              → ∃! h ꞉ (X → ℕ∞), is-homomorphism κ h
Example-3-1'' = PRED-is-the-homotopy-final-coalgebra

-- def:isolated
Definition-3-2 : {X : 𝓤 ̇ } → X → 𝓤 ̇
Definition-3-2 = is-isolated

Definition-3-2' : 𝓤 ̇ → 𝓤 ̇
Definition-3-2' = is-discrete

-- ex:isolated (1), every proposition is discrete
Examples-3-3-1-props : {X : 𝓤 ̇ } → is-prop X → is-discrete X
Examples-3-3-1-props = props-are-discrete

-- ex:isolated (1), 𝟚 is discrete
Examples-3-3-1-𝟚 : is-discrete 𝟚
Examples-3-3-1-𝟚 = 𝟚-is-discrete

-- ex:isolated (2)
Examples-3-3-2 : is-discrete ℕ
Examples-3-3-2 = ℕ-is-discrete

-- ex:isolated (3), item:NInf-discrete-wlpo
Examples-3-3-3 : is-discrete ℕ∞ ↔ WLPO
Examples-3-3-3 = ℕ∞-discrete-gives-WLPO , WLPO-gives-ℕ∞-discrete fe

-- ex:isolated (4), the finite conaturals are isolated
Examples-3-3-4 : (n : ℕ) → is-isolated (ι n)
Examples-3-3-4 = finite-isolated fe₀

-- ex:isolated (5), the point at infinity
Examples-3-3-5 : is-isolated ∞ ↔ WLPO
Examples-3-3-5 = is-isolated-gives-is-isolated' ∞ ,
                 is-isolated'-gives-is-isolated ∞

-- ex:isolated (6), item:iota1-embedding-dense
Examples-3-3-6 : is-embedding ι𝟙 × is-dense ι𝟙
Examples-3-3-6 = ι𝟙-is-embedding fe₀ , ι𝟙-dense fe₀

-- lem:discrete-sets (1), item:discrete-types-are-sets
Lemma-3-4-1 : {X : 𝓤 ̇ } → is-discrete X → is-set X
Lemma-3-4-1 = discrete-types-are-sets

-- lem:discrete-sets (2), item:isolated-gives-h-isolated
Lemma-3-4-2 : {X : 𝓤 ̇ } (x : X) → is-isolated x → is-h-isolated x
Lemma-3-4-2 = isolated-points-are-h-isolated

-- lem:discrete-sets (3), item:being-isolated-is-prop
Lemma-3-4-3 : {X : 𝓤 ̇ } (x : X) → is-prop (is-isolated x)
Lemma-3-4-3 = being-isolated-is-prop fe

-- lem:discrete-sets (3), item:being-isolated-is-prop, discreteness too
Lemma-3-4-3' : {X : 𝓤 ̇ } → is-prop (is-discrete X)
Lemma-3-4-3' = being-discrete-is-prop fe

-- rem:isolated-vs-h-isolated
Remark-3-5 : is-set ℕ∞
Remark-3-5 = ℕ∞-is-set fe₀

-- prop:discrete-closure (1), item:discrete-plus
Proposition-3-6-1-inl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (x : X)
                      → is-isolated x → is-isolated (inl {𝓤} {𝓥} {X} {Y} x)
Proposition-3-6-1-inl = inl-is-isolated

Proposition-3-6-1-inr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y)
                      → is-isolated y → is-isolated (inr {𝓤} {𝓥} {X} {Y} y)
Proposition-3-6-1-inr = inr-is-isolated

Proposition-3-6-1-+ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → is-discrete X → is-discrete Y → is-discrete (X + Y)
Proposition-3-6-1-+ = +-is-discrete

-- prop:discrete-closure (2), item:discrete-retract
Proposition-3-6-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → retract Y of X → is-discrete X → is-discrete Y
Proposition-3-6-2 = retract-is-discrete

-- prop:discrete-closure (3), item:discrete-sigma
Proposition-3-6-3 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                  → is-discrete X
                  → ((x : X) → is-discrete (Y x))
                  → is-discrete (Σ Y)
Proposition-3-6-3 = Σ-is-discrete

-- prop:discrete-closure (4), item:discrete-sigma-isolated
Proposition-3-6-4 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                  → is-isolated x
                  → is-isolated y
                  → is-isolated {_} {Σ Y} (x , y)
Proposition-3-6-4 = Σ-isolated

Proposition-3-6-4' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                   → is-set X
                   → is-isolated {_} {Σ Y} (x , y)
                   → is-isolated y
Proposition-3-6-4' = Σ-isolated-right

Proposition-3-6-4'' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                    → is-isolated (x , y)
                    → is-isolated x
Proposition-3-6-4'' = ×-isolated-left

-- prop:discrete-closure (5), item:discrete-reflected
Proposition-3-6-5 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  → left-cancellable f
                  → (x : X) → is-isolated (f x) → is-isolated x
Proposition-3-6-5 = lc-maps-reflect-isolatedness

Proposition-3-6-5' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → is-equiv f
                   → (x : X) → is-isolated x → is-isolated (f x)
Proposition-3-6-5' = equivs-preserve-isolatedness

-- lem:discrete-exponential (1)
Lemma-3-7-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → has-two-distinct-points Y
            → is-discrete (X → Y)
            → is-decidable (is-empty X)
Lemma-3-7-1 = discrete-exponential-has-decidable-emptiness-of-exponent fe'

-- lem:discrete-exponential (2)
Lemma-3-7-2 : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
            → is-prop P
            → ((p : P) → is-isolated (f p))
            → is-embedding f
Lemma-3-7-2 = maps-of-props-into-isolated-points-are-embeddings

-- def:tot-sep
Definition-3-8 : 𝓤 ̇ → 𝓤 ̇
Definition-3-8 = is-totally-separated

-- lem:tot-sep-basic (1), item:disc-gives-ts
Lemma-3-9-1 : {X : 𝓤 ̇ } → is-discrete X → is-totally-separated X
Lemma-3-9-1 = discrete-types-are-totally-separated

-- lem:tot-sep-basic (2), item:ts-gives-nnsep
Lemma-3-9-2 : (X : 𝓤 ̇ ) → is-totally-separated X → is-¬¬-separated X
Lemma-3-9-2 = totally-separated-types-are-¬¬-separated

-- lem:tot-sep-basic (3), item:ts-is-set
Lemma-3-9-3 : (X : 𝓤 ̇ ) → is-totally-separated X → is-set X
Lemma-3-9-3 = totally-separated-types-are-sets fe'

-- lem:tot-sep-basic (3), item:ts-is-set, the propositionhood
Lemma-3-9-3' : (X : 𝓤 ̇ ) → is-prop (is-totally-separated X)
Lemma-3-9-3' {𝓤} = being-totally-separated-is-prop (fe 𝓤 𝓤)

\end{code}

The circle of Examples 3.10(1) is implemented as the type Tℤ of
ℤ-torsors of SyntheticHomotopyTheory.Circle.Construction.  Its loop
space at the base point is ℤ, so it is not a set, and hence not
totally separated by Lemma 3.9 above.

Labels: Examples 3.10(1) = ex:tot-sep-failures(item:circle-not-tot-sep),
Lemma 3.9 = lem:tot-sep-basic.

\begin{code}

-- ex:tot-sep-failures (1), item:circle-not-tot-sep
Examples-3-10-1 : ¬ is-set Tℤ
Examples-3-10-1 s = +disjoint (loops-are-a-proposition (inl ⋆) (inr (inl 0)))
 where
  loops-are-a-proposition = equiv-to-prop
                             (≃-sym loops-at-base-equivalent-to-ℤ)
                             (s {base-of-Tℤ} {base-of-Tℤ})

-- ex:tot-sep-failures (2), item:Omega-tot-sep-gives-EM
Examples-3-10-2 : is-totally-separated (Ω 𝓤) → EM 𝓤
Examples-3-10-2 {𝓤} = Ω-totally-separated-gives-EM (pe 𝓤) fe'

-- ex:tot-sep-failures (3), item:two-infinities-not-tot-sep
Examples-3-10-3 : is-totally-separated ℕ∞₂ → ¬¬ WLPO
Examples-3-10-3 = ℕ∞₂-is-not-totally-separated-in-general

-- ex:tot-sep-failures (3), the index type is totally separated
Examples-3-10-3-index : is-totally-separated ℕ∞
Examples-3-10-3-index = ℕ∞-is-totally-separated fe₀

-- ex:tot-sep-failures (3), the fibers are totally separated
Examples-3-10-3-fibers : (u : ℕ∞) → is-totally-separated (u ＝ ∞ → 𝟚)
Examples-3-10-3-fibers u = Π-is-totally-separated fe₀
                            (λ _ → 𝟚-is-totally-separated)

-- prop:tot-sep-equiv, item:ts-definition against item:ts-quasicomponent
Proposition-3-11-12 : {X : 𝓤 ̇ }
                    → is-totally-separated X ↔ is-totally-separated₁ X
Proposition-3-11-12 = totally-separated-gives-totally-separated₁ fe' ,
                      totally-separated₁-types-are-totally-separated

-- prop:tot-sep-equiv, item:ts-definition against item:ts-eval-embedding
Proposition-3-11-13 : {X : 𝓤 ̇ }
                    → is-totally-separated X ↔ is-totally-separated₂ X
Proposition-3-11-13 = totally-separated-gives-totally-separated₂ fe' ,
                      totally-separated₂-gives-totally-separated fe'

-- prop:tot-sep-equiv, item:ts-definition against item:ts-apartness-tight
Proposition-3-11-14 : {X : 𝓤 ̇ }
                    → is-totally-separated X ↔ is-totally-separated₃ X
Proposition-3-11-14 = totally-separated-gives-totally-separated₃ ,
                      totally-separated₃-gives-totally-separated

-- claim boolean-apartness
Prose-boolean-apartness : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
Prose-boolean-apartness = _♯₂_

Prose-boolean-apartness' : {X : 𝓤 ̇ } → is-apartness (_♯₂_ {𝓤} {X})
Prose-boolean-apartness' = ♯₂-is-apartness

-- prop:tot-sep-closure (1), item:tot-sep-retract
Proposition-3-12-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → retract Y of X
                   → is-totally-separated X
                   → is-totally-separated Y
Proposition-3-12-1 = retract-of-totally-separated

-- prop:tot-sep-closure (1), item:tot-sep-retract, equivalence
Proposition-3-12-1-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → X ≃ Y
                         → is-totally-separated X
                         → is-totally-separated Y
Proposition-3-12-1-equiv = equiv-to-totally-separated

-- prop:tot-sep-closure (2), item:tot-sep-product
Proposition-3-12-2 : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                     → is-totally-separated X
                     → is-totally-separated Y
                     → is-totally-separated (X × Y)
Proposition-3-12-2 = ×-totally-separated

-- prop:tot-sep-closure (3)
Proposition-3-12-3 : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                   → is-discrete X
                   → ((x : X) → is-totally-separated (Y x))
                   → is-totally-separated (Σ Y)
Proposition-3-12-3 = Σ-is-totally-separated-if-index-type-is-discrete

-- prop:tot-sep-closure (3), the + case
Proposition-3-12-3-+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                     → is-totally-separated X
                     → is-totally-separated Y
                     → is-totally-separated (X + Y)
Proposition-3-12-3-+ = +-totally-separated

-- prop:tot-sep-closure (4)
Proposition-3-12-4 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → ((x : X) → is-totally-separated (Y x))
                   → is-totally-separated (Π Y)
Proposition-3-12-4 = Π-is-totally-separated fe'

-- ex:tot-sep (2), item:simple-types
Examples-3-13-1 : 𝓤₀ ̇ → 𝓤₁ ̇
Examples-3-13-1 = simple-type

Examples-3-13-1' : {X : 𝓤₀ ̇ } → simple-type X → is-totally-separated X
Examples-3-13-1' = simple-types-are-totally-separated

Examples-3-13-1'' : {X : 𝓤₀ ̇ } → simple-type X → retract ℕ of X
Examples-3-13-1'' = ℕ-is-retract-of-any-simple-type

-- ex:tot-sep (2), item:simple-types, pointedness and the retract clause
Examples-3-13-1-pointed : {X : 𝓤₀ ̇ } → simple-type X → X
Examples-3-13-1-pointed = simple-types-pointed

Examples-3-13-1-r : {X A : 𝓤₀ ̇ }
                  → retract A of ℕ → simple-type X → retract A of X
Examples-3-13-1-r = simple-types-r

-- ex:tot-sep (3), item:cantor-not-discrete
Examples-3-13-2 : is-discrete (ℕ → 𝟚) → WLPO
Examples-3-13-2 = ℕ∞-discrete-gives-WLPO ∘ retract-is-discrete (ℕ∞-retract-of-Cantor fe₀)

-- lem:sigma-NInf-tot-sep
Lemma-3-14 : (A : ℕ∞ → 𝓥 ̇ )
           → ((u : ℕ∞) → is-totally-separated (A u))
           → is-prop (A ∞)
           → is-totally-separated (Σ A)
Lemma-3-14 = Σ-indexed-by-ℕ∞-is-totally-separated-if-family-at-∞-is-prop fe₀

-- thm:ts-reflection
Theorem-3-15 : 𝓤 ̇ → 𝓤 ̇
Theorem-3-15 = 𝕋

Theorem-3-15-ts : {X : 𝓤 ̇ } → is-totally-separated (𝕋 X)
Theorem-3-15-ts = 𝕋-is-totally-separated

-- thm:ts-reflection (1), item:ts-reflection-surjection
Theorem-3-15-1 : {X : 𝓤 ̇ } → is-surjection (ηᵀ {𝓤} {X})
Theorem-3-15-1 = ηᵀ-is-surjection

Theorem-3-15-1' : {X : 𝓤 ̇ } (P : 𝕋 X → 𝓦 ̇ )
                → ((x' : 𝕋 X) → is-prop (P x'))
                → ((x : X) → P (ηᵀ x))
                → (x' : 𝕋 X) → P x'
Theorem-3-15-1' = ηᵀ-induction

-- thm:ts-reflection (2), item:ts-reflection-universal
Theorem-3-15-2 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
               → is-totally-separated A
               → (f : X → A) → ∃! f̅ ꞉ (𝕋 X → A) , f̅ ∘ ηᵀ ＝ f
Theorem-3-15-2 = totally-separated-reflection

Theorem-3-15-2' : {X : 𝓤 ̇ } → (𝕋 X → 𝟚) ≃ (X → 𝟚)
Theorem-3-15-2' = totally-separated-reflection'' 𝟚-is-totally-separated

-- thm:ts-reflection (3), item:ts-reflection-kernel
Theorem-3-15-3 : {X : 𝓤 ̇ } {x y : X} → ηᵀ x ＝ ηᵀ y → x ＝₂ y
Theorem-3-15-3 = ηᵀ-relates-identified-points

Theorem-3-15-3' : {X : 𝓤 ̇ } {x y : X} → x ＝₂ y → ηᵀ x ＝ ηᵀ y
Theorem-3-15-3' = ηᵀ-identifies-related-points

\end{code}

Section 4. Compactness

Labels: Section 4 = sec:compact-types-theory.

\begin{code}

-- def:compact
Definition-4-1 : 𝓤 ̇ → 𝓤 ̇
Definition-4-1 = is-compact

Definition-4-1-∃ : 𝓤 ̇ → 𝓤 ̇
Definition-4-1-∃ = is-∃-compact

Definition-4-1-Π : 𝓤 ̇ → 𝓤 ̇
Definition-4-1-Π = is-Π-compact

-- lem:compact-formulations
Lemma-4-2 : {X : 𝓤 ̇ } → is-compact X → is-Compact X {𝓥}
Lemma-4-2 = compact-types-are-Compact

Lemma-4-2' : {X : 𝓤 ̇ } → is-Compact X {𝓤₀} → is-compact X
Lemma-4-2' = Compact-types-are-compact

-- lem:compact-decidable
Lemma-4-3 : (X : 𝓤 ̇ ) → is-compact X → is-decidable X
Lemma-4-3 = compact-types-are-decidable

Lemma-4-3' : (X : 𝓤 ̇ ) → is-prop X → is-decidable X → is-compact X
Lemma-4-3' = decidable-propositions-are-compact

-- prop:global-choice
Proposition-4-4 : ((X : 𝓤 ̇ ) → is-Compact X {𝓤}) → Global-Choice 𝓤
Proposition-4-4 = all-types-compact-gives-global-choice

-- prop:global-choice, the converse
Proposition-4-4' : Global-Choice 𝓤 → ((X : 𝓤 ̇ ) → is-Compact X {𝓤})
Proposition-4-4' = global-choice-gives-all-types-compact

-- claim global-choice-univalence
Prose-global-choice-univalence : Global-Choice (𝓤 ⁺) → is-univalent 𝓤 → 𝟘
Prose-global-choice-univalence = Global-Choice-is-inconsistent-with-univalence

-- ex:compact-basic (1), the finite types
Examples-4-5-1-Fin : ℕ → 𝓤₀ ̇
Examples-4-5-1-Fin = Fin

-- ex:compact-basic (1), they are compact
Examples-4-5-1 : {n : ℕ} → is-Compact (Fin n) {𝓤}
Examples-4-5-1 = Fin-Compact

-- ex:compact-basic (2), item:N-compact-lpo
Examples-4-5-2 : is-compact ℕ ↔ LPO
Examples-4-5-2 = compact-ℕ-gives-LPO fe₀ , LPO-gives-compact-ℕ fe₀

-- ex:compact-basic (3), item:N-exists-compact-lpo
Examples-4-5-3 : is-∃-compact ℕ ↔ LPO
Examples-4-5-3 = ∃-compact-ℕ-gives-LPO , LPO-gives-∃-compact-ℕ

-- ex:compact-basic (4), item:N-pi-compact
Examples-4-5-4 : is-Π-compact ℕ ↔ WLPO
Examples-4-5-4 = Π-compact-ℕ-gives-WLPO , WLPO-gives-Π-compact-ℕ

-- lem:compact-pt (1), item:compact-and-pointed, against
-- (2), item:universal-witness
Lemma-4-6-1 : {X : 𝓤 ̇ } → is-compact∙ X → is-compact X
Lemma-4-6-1 = compact∙-types-are-compact

Lemma-4-6-1' : {X : 𝓤 ̇ } → is-compact∙ X → X
Lemma-4-6-1' = compact∙-types-are-pointed

-- lem:compact-pt, item:compact-and-pointed from item:universal-witness
Lemma-4-6-2 : {X : 𝓤 ̇ } → is-compact X → X → is-compact∙ X
Lemma-4-6-2 = compact-pointed-types-are-compact∙

-- ex:compact-pt-basic (1)
Examples-4-7-1 : is-compact∙ 𝟚
Examples-4-7-1 = 𝟚-is-compact∙

-- ex:compact-pt-basic (2)
Examples-4-7-2 : is-compact∙ (Ω 𝓤)
Examples-4-7-2 {𝓤} = Ω-is-compact∙ (fe 𝓤 𝓤) (pe 𝓤)

-- ex:compact-pt-basic (3), item:NInf-compact
Examples-4-7-3 : is-compact∙ ℕ∞
Examples-4-7-3 = ℕ∞-compact∙

-- thm:compact-closure (1), item:compact-zero-one
Theorem-4-8-1-𝟘 : is-Compact (𝟘 {𝓤}) {𝓥}
Theorem-4-8-1-𝟘 = 𝟘-is-Compact

Theorem-4-8-1-𝟙 : is-Compact (𝟙 {𝓤}) {𝓥}
Theorem-4-8-1-𝟙 = 𝟙-is-Compact

-- thm:compact-closure (1), item:compact-zero-one, singletons
Theorem-4-8-1-singleton : {X : 𝓤 ̇ } → is-singleton X → is-Compact X {𝓥}
Theorem-4-8-1-singleton = singletons-are-Compact

-- thm:compact-closure (2), item:compact-plus
Theorem-4-8-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → is-Compact X {𝓦} → is-Compact Y {𝓦} → is-Compact (X + Y) {𝓦}
Theorem-4-8-2 = +-is-Compact

-- thm:compact-closure (3), item:compact-sigma
Theorem-4-8-3 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → is-Compact X {𝓥 ⊔ 𝓦}
               → ((x : X) → is-Compact (Y x) {𝓦})
               → is-Compact (Σ Y) {𝓦}
Theorem-4-8-3 = Σ-is-Compact

-- thm:compact-closure (4), item:compact-retract
Theorem-4-8-4 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → retract Y of X → is-Compact X {𝓦} → is-Compact Y {𝓦}
Theorem-4-8-4 = Compact-closed-under-retracts

-- thm:compact-closure (5), item:compact-surjection
Theorem-4-8-5 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → funext 𝓥 𝓤₀
               → is-surjection f
               → is-Compact X {𝓥}
               → is-Compact Y {𝓥}
Theorem-4-8-5 = surjection-Compact

Theorem-4-8-5' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-Compact X {𝓤 ⊔ 𝓥}
                → is-Compact (image f) {𝓤 ⊔ 𝓥}
Theorem-4-8-5' = image-Compact fe'

-- prop:compact-reflection
Proposition-4-9 : {X : 𝓤 ̇ } → is-Compact X {𝓤} → is-Compact (𝕋 X) {𝓤}
Proposition-4-9 = surjection-Compact ηᵀ fe' ηᵀ-is-surjection

-- cor:compact-pt-closure (1), item:pt-retract
Corollary-4-10-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → retract Y Of X → is-compact∙ X → is-compact∙ Y
Corollary-4-10-1 = retract-is-compact∙

Corollary-4-10-1' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → X ≃ Y → is-compact∙ X → is-compact∙ Y
Corollary-4-10-1' = compact∙-types-are-closed-under-equiv

-- cor:compact-pt-closure (2), item:pt-sigma
Corollary-4-10-2 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                 → is-compact∙ X
                 → ((x : X) → is-compact∙ (Y x))
                 → is-compact∙ (Σ Y)
Corollary-4-10-2 = Σ-is-compact∙

-- cor:compact-pt-closure (2), item:pt-sigma, products and coproducts
Corollary-4-10-2-× : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → is-compact∙ X → is-compact∙ Y → is-compact∙ (X × Y)
Corollary-4-10-2-× = ×-is-compact∙

Corollary-4-10-2-+ : {X₀ X₁ : 𝓤 ̇ }
                   → is-compact∙ X₀ → is-compact∙ X₁ → is-compact∙ (X₀ + X₁)
Corollary-4-10-2-+ = +-is-compact∙

-- cor:compact-pt-closure (3), item:pt-image
Corollary-4-10-3 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                 → is-surjection f → is-compact∙ X → is-compact∙ Y
Corollary-4-10-3 = codomain-of-surjection-is-compact∙ pt

Corollary-4-10-3' : {X Y : 𝓤₀ ̇ } (f : X → Y)
                  → is-compact∙ X → is-compact∙ (image f)
Corollary-4-10-3' = image-is-compact∙ pt

-- prop:compact-complemented (1), item:complemented-subtype-compact
Proposition-4-11-1 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                   → is-Compact X {𝓥 ⊔ 𝓦}
                   → is-complemented A
                   → ((x : X) → is-prop (A x))
                   → is-Compact (Σ x ꞉ X , A x) {𝓦}
Proposition-4-11-1 = complemented-subset-of-compact-type

-- prop:compact-complemented (2), item:decide-sum-or-product
Proposition-4-11-2 : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                   → is-compact X
                   → ((x : X) → A x + B x)
                   → (Σ x ꞉ X , A x) + (Π x ꞉ X , B x)
Proposition-4-11-2 = compact-gives-Σ+Π

-- prop:compact-complemented (3), item:complemented-choice
Proposition-4-11-3 : {X : 𝓤 ̇ } → is-Σ-Compact X {𝓥} → Complemented-choice X {𝓥}
Proposition-4-11-3 = Σ-Compactness-gives-Complemented-choice

\end{code}

Remark 4.12 records that the compactness of the Cantor type is
independent of our type theory, holding in the topological topos and
in the Kleene--Vesley topos and failing in the effective topos. This
is a statement about models rather than a theorem of our type theory,
so it has no entry. What it says about finite products is Theorem 4.8(3).

Labels: Remark 4.12 = rem:tychonoff-independence,
Theorem 4.8(3) = thm:compact-closure(item:compact-sigma).

\begin{code}

-- prop:weakly-compact-basic (1), item:weak-compact-are-props
Proposition-4-13-1 : {X : 𝓤 ̇ } → is-prop (is-∃-compact X)
Proposition-4-13-1 = ∃-compactness-is-prop

Proposition-4-13-1' : {X : 𝓤 ̇ } → is-prop (is-Π-compact X)
Proposition-4-13-1' = Π-compactness-is-prop

-- prop:weakly-compact-basic (2), item:compact-gives-exists-compact
Proposition-4-13-2 : {X : 𝓤 ̇ } → is-compact X → is-∃-compact X
Proposition-4-13-2 = compact-types-are-∃-compact

-- prop:weakly-compact-basic (3), item:exists-gives-pi-compact
Proposition-4-13-3 : {X : 𝓤 ̇ } → is-∃-compact X → is-Π-compact X
Proposition-4-13-3 = ∃-compact-types-are-Π-compact

-- prop:weakly-compact-basic (4), item:exists-compact-stability
Proposition-4-13-4
 : {X : 𝓤 ̇ }
 → is-∃-compact X
 → (p : X → 𝟚) → ¬¬ (∃ x ꞉ X , p x ＝ ₀) → ∃ x ꞉ X , p x ＝ ₀
Proposition-4-13-4 = ∃-compactness-gives-Markov

-- prop:weakly-compact-basic (5), item:pi-compact-isolated
Proposition-4-13-5 : {X : 𝓤 ̇ } → is-Π-compact' X → is-Π-compact X
Proposition-4-13-5 = Π-compact'-types-are-Π-compact

Proposition-4-13-5' : {X : 𝓤 ̇ } → is-Π-compact X → is-Π-compact' X
Proposition-4-13-5' = Π-compact-types-are-Π-compact'

-- prop:weakly-compact-basic (6), item:weakly-compact-reflection
Proposition-4-13-6 : (X : 𝓤 ̇ ) → is-∃-compact X ↔ is-∃-compact (𝕋 X)
Proposition-4-13-6 X = ∃-compact-types-are-∃-compact-𝕋 X ,
                       ∃-compact-𝕋-types-are-∃-compact X

Proposition-4-13-6' : (X : 𝓤 ̇ ) → is-Π-compact X ↔ is-Π-compact (𝕋 X)
Proposition-4-13-6' X = Π-compact-types-are-Π-compact-𝕋 X ,
                        Π-compact-𝕋-types-are-Π-compact X

-- prop:weakly-compact-closure (1), item:weak-compact-retracts
Proposition-4-14-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → is-surjection f → is-∃-compact X → is-∃-compact Y
Proposition-4-14-1 = codomain-of-surjection-is-∃-compact

Proposition-4-14-1' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-surjection f → is-Π-compact X → is-Π-compact Y
Proposition-4-14-1' = codomain-of-surjection-is-Π-compact

-- prop:weakly-compact-closure (2), item:weak-compact-sigma
Proposition-4-14-2 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → is-Π-compact X
                   → ((x : X) → is-Π-compact (Y x))
                   → is-Π-compact (Σ Y)
Proposition-4-14-2 = Π-compact-closed-under-Σ

-- prop:weakly-compact-closure (3), item:weak-compact-subtype
Proposition-4-14-3 : {X : 𝓤 ̇ } (A : X → 𝟚)
                   → is-∃-compact X → is-∃-compact (Σ x ꞉ X , A x ＝ ₀)
Proposition-4-14-3 = detachable-subset-∃-compact

Proposition-4-14-3' : {X : 𝓤 ̇ } (A : X → 𝟚)
                    → is-Π-compact X → is-Π-compact (Σ x ꞉ X , A x ＝ ₁)
Proposition-4-14-3' = complemented-subtype-is-Π-compact

-- prop:weakly-compact-props (1), item:exists-compact-prop-decidable
Proposition-4-15-1 : (X : 𝓤 ̇ ) → is-prop X → is-∃-compact X → is-decidable X
Proposition-4-15-1 = ∃-compact-propositions-are-decidable

Proposition-4-15-1' : (X : 𝓤 ̇ ) → is-prop X → is-decidable X → is-∃-compact X
Proposition-4-15-1' = decidable-propositions-are-∃-compact

-- prop:weakly-compact-props (2), item:exists-compact-support
Proposition-4-15-2 : {X : 𝓤 ̇ } → is-∃-compact X → is-decidable ∥ X ∥
Proposition-4-15-2 = ∃-compact-types-have-decidable-support

-- prop:weakly-compact-props (3), item:non-empty-exists-compact
Proposition-4-15-3 : {X : 𝓤 ̇ } → is-∃-compact X → ¬¬ X → ∥ X ∥
Proposition-4-15-3 = ∃-compact-non-empty-types-are-inhabited

-- prop:weakly-compact-props (4), item:pi-compact-negation
Proposition-4-15-4 : (X : 𝓤 ̇ ) → is-Π-compact X → is-decidable (¬ X)
Proposition-4-15-4 = negations-of-Π-compact-types-are-decidable

-- prop:exists-compact-pt, item:truncated-universal-witness
Proposition-4-16 : 𝓤 ̇ → 𝓤 ̇
Proposition-4-16 = is-∃-compact∙

-- prop:exists-compact-pt, item:exists-compact-inhabited against
-- item:truncated-universal-witness
Proposition-4-16-12 : {X : 𝓤 ̇ } → is-∃-compact∙ X → ∥ X ∥ × is-∃-compact X
Proposition-4-16-12 = ∃-compact∙-types-are-inhabited-and-compact

Proposition-4-16-21 : {X : 𝓤 ̇ } → ∥ X ∥ × is-∃-compact X → is-∃-compact∙ X
Proposition-4-16-21 = inhabited-and-compact-types-are-∃-compact∙

-- prop:exists-compact-pt, ∃-compact is being ∃-compact pointed or empty
Proposition-4-16-empty : {X : 𝓤 ̇ }
                       → is-∃-compact X → is-∃-compact∙ X + is-empty X
Proposition-4-16-empty = ∃-compact-types-are-∃-compact∙-or-empty

Proposition-4-16-empty' : {X : 𝓤 ̇ }
                        → is-∃-compact∙ X + is-empty X → is-∃-compact X
Proposition-4-16-empty' = ∃-compact∙-or-empty-types-are-∃-compact

-- prop:pi-compact-infs
Proposition-4-17 : {X : 𝓤 ̇ } → is-Π-compact X → has-infs X
Proposition-4-17 = Π-compact-has-infs

-- prop:pi-compact-infs, the converse
Proposition-4-17' : {X : 𝓤 ̇ } → has-infs X → is-Π-compact X
Proposition-4-17' = has-infs-Π-compact

-- claim right-adjoint-characterization
Prose-right-adjoint-characterization
 : {X : 𝓤 ̇ } (A : (X → 𝟚) → 𝟚)
 → Κ⊣ A ↔ ((p : X → 𝟚) → A p ＝ ₁ ↔ p ＝ (λ x → ₁))
Prose-right-adjoint-characterization = Κ⊣-charac

Prose-right-adjoint-characterization'
 : {X : 𝓤 ̇ } → is-Π-compact X ↔ (Σ A ꞉ ((X → 𝟚) → 𝟚) , Κ⊣ A)
Prose-right-adjoint-characterization' = Π-compact-iff-Κ-has-right-adjoint

-- prop:clopen-projections
Proposition-4-18 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
Proposition-4-18 = is-clopen-map

-- prop:clopen-projections, the two directions
Proposition-4-18-clopen
 : (X : 𝓤 ̇ )
 → is-∃-compact X
 → ({𝓥 : Universe} (A : 𝓥 ̇ ) → is-clopen-map (fst A X))
Proposition-4-18-clopen = ∃-compact-clopen-projections

Proposition-4-18-clopen'
 : (X : 𝓤 ̇ )
 → ({𝓥 : Universe} (A : 𝓥 ̇ ) → is-clopen-map (fst A X))
 → is-∃-compact X
Proposition-4-18-clopen' {𝓤} = clopen-projections-∃-compact {𝓤} {𝓤₀}

-- lem:sigma-isolated
Lemma-4-19 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
           → ((x : X) → is-Compact (Y x) {𝓤 ⊔ 𝓥})
           → is-isolated (x , y) → is-isolated x
Lemma-4-19 = Σ-isolated-left

-- prop:compact-to-discrete (1), item:pi-compact-discrete-power
Proposition-4-20-1 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → is-Π-compact X
                   → ((x : X) → is-discrete (Y x))
                   → is-discrete ((x : X) → Y x)
Proposition-4-20-1 = discrete-to-power-Compact-is-discrete' (fe _ _)
                   ∘ Π-compact-types-are-Π-Compact

-- prop:compact-to-discrete (2), item:compact-apart-or-equal
Proposition-4-20-2 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → is-compact X
                   → ((x : X) → is-discrete (Y x))
                   → (f g : (x : X) → Y x) → (f ♯ g) + (f ＝ g)
Proposition-4-20-2 = apart-or-equal (fe _ _)

-- ex:cantor-discrete-converse
Example-4-21 : WLPO → is-discrete (ℕ → 𝟚)
Example-4-21 wlpo = discrete-to-power-Π-compact-is-discrete
                    (WLPO-gives-Π-compact-ℕ wlpo) 𝟚-is-discrete

-- def:disconnected
Definition-4-22 : 𝓤 ̇ → 𝓤 ̇
Definition-4-22 = is-disconnected

-- prop:discrete-exponential-gives-compact
Proposition-4-23 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → is-disconnected Y
                 → is-discrete (X → Y)
                 → is-Π-compact X
Proposition-4-23 = discrete-power-of-disconnected-gives-compact-exponent

Proposition-4-23' : {X : 𝓤 ̇ } → is-discrete (X → 𝟚) → is-Π-compact X
Proposition-4-23' = power-of-two-discrete-gives-compact-exponent

-- prop:tot-sep-compact-exponential (1), item:tscd-disconnected
Proposition-4-24-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → is-totally-separated X
                   → is-disconnected Y
                   → is-Π-compact (X → Y)
                   → is-discrete X
Proposition-4-24-1 = tscd₀

Proposition-4-24-1' : {X : 𝓤 ̇ }
                    → is-totally-separated X
                    → is-Π-compact (X → 𝟚)
                    → is-discrete X
Proposition-4-24-1' = tscd

-- prop:tot-sep-compact-exponential (2), item:tscd-reflection
Proposition-4-24-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → is-disconnected Y
                   → is-Π-compact (X → Y)
                   → is-discrete (𝕋 X)
Proposition-4-24-2 = tscd₁

-- ex:not-compact (1), item:simple-not-compact
Examples-4-25-1 : {X : 𝓤₀ ̇ }
                → simple-type X → is-Π-compact X → is-Π-compact ℕ
Examples-4-25-1 = stcwlpo

-- ex:not-compact (2), item:NInf-power-not-compact
Examples-4-25-2 : is-Π-compact (ℕ∞ → 𝟚) → WLPO
Examples-4-25-2 = [ℕ∞→𝟚]-compact-implies-WLPO

-- thm:micro-tychonoff
Theorem-4-26 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
             → is-prop X
             → ((x : X) → is-compact∙ (Y x))
             → is-compact∙ (Π Y)
Theorem-4-26 = micro-tychonoff fe'

-- claim micro-tychonoff-constant-family
Prose-micro-tychonoff-constant-family
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-prop X
 → is-compact∙ Y
 → is-compact∙ (X → Y)
Prose-micro-tychonoff-constant-family i c
 = micro-tychonoff fe' i (λ _ → c)

-- ex:LPO-to-N
Example-4-27 : is-compact∙ (LPO → ℕ)
Example-4-27 = [LPO→ℕ]-is-compact∙ fe₀

-- rem:micro-tychonoff (2), item:pointedness-essential
Remark-4-28-2 : ((X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                  → is-prop X
                  → ((x : X) → is-compact (Y x))
                  → is-compact (Π Y))
              → WEM 𝓤
Remark-4-28-2 = compact-micro-tychonoff-gives-WEM

-- cor:subfinite-tychonoff
Corollary-4-29 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → (n : ℕ)
               → X ↪ Fin n
               → ((x : X) → is-compact∙ (Y x))
               → is-compact∙ (Π Y)
Corollary-4-29 = subfinite-tychonoff fe' fe'

-- def:extension
Definition-4-30 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (X → 𝓦 ̇ ) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ )
Definition-4-30 = Π-extension

-- lem:extension-property (1), item:ext-restricts
Lemma-4-31-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
                   → is-embedding j
                   → (x : X) → Π-extension f j (j x) ≃ f x
Lemma-4-31-1 = Π-extension-property

-- lem:extension-property (2), item:ext-off-image
Lemma-4-31-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y) (y : Y)
                   → ((x : X) → j x ≠ y)
                   → Π-extension f j y ≃ 𝟙 {𝓣}
Lemma-4-31-2 f j = Π-extension-out-of-range f j

-- thm:extended-sum-compact
Theorem-4-32 : {X : 𝓤 ̇ } {K : 𝓥 ̇ } {Y : X → 𝓦 ̇ } (j : X → K)
             → is-embedding j
             → ((x : X) → is-compact∙ (Y x))
             → is-compact∙ K
             → is-compact∙ (Σ (Y / j))
Theorem-4-32 = extended-sum-compact∙

-- lem:extension-tot-sep
Lemma-4-34 : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (j : X → A) (Y : X → 𝓦 ̇ )
                 → ((x : X) → is-totally-separated (Y x))
                 → (a : A) → is-totally-separated ((Y / j) a)
Lemma-4-34 = /-is-totally-separated fe

-- lem:extension-retract (1), item:ext-retract-fiber
Lemma-4-35-1 : {X : 𝓤 ̇ } {K : 𝓥 ̇ } (Y Z : X → 𝓦 ̇ ) (j : X → K)
             → ((x : X) → retract (Y x) of (Z x))
             → (k : K) → retract ((Y / j) k) of ((Z / j) k)
Lemma-4-35-1 = retract-extension

-- lem:extension-retract (2), item:ext-retract-sum
Lemma-4-35-2 : {X : 𝓤 ̇ } {K : 𝓥 ̇ } (Y Z : X → 𝓦 ̇ ) (j : X → K)
             → ((x : X) → retract (Y x) of (Z x))
             → retract (Σ (Y / j)) of (Σ (Z / j))
Lemma-4-35-2 Y₀ Y₁ j ρ = Σ-retract (Y₀ / j) (Y₁ / j)
                          (retract-extension Y₀ Y₁ j ρ)

-- lem:delayed-sequences (1), item:delayed-sequences-1
Lemma-4-36-1 : Σ¹ (λ (_ : ℕ) → Cantor) ＝ (Σ u ꞉ ℕ∞ , (is-finite u → Cantor))
Lemma-4-36-1 = refl

-- lem:delayed-sequences (2), item:delayed-sequences-2
Lemma-4-36-2 : 𝔻 Cantor ≃ Cantor
Lemma-4-36-2 = 𝔻-Cantor-≃-Cantor


\end{code}

Section 5. Ordinals and their arithmetic

Labels: Section 5 = sec:ordinals-prelim.

\begin{code}

-- lem:accessibility-transfinite-induction
Lemma-5-1 : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
          → is-well-founded _<_
          → is-Well-founded _<_ {𝓦}
Lemma-5-1 _<_ w = transfinite-induction _<_ w

Lemma-5-1-converse : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
                   → is-Well-founded _<_ {𝓤 ⊔ 𝓥}
                   → is-well-founded _<_
Lemma-5-1-converse _<_ = transfinite-induction-converse _<_

-- claim ordinal-well-order
Prose-ordinal-well-order : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-well-order = is-well-order

Prose-ordinal-well-order-Ordinal : (𝓤 : Universe) → 𝓤 ⁺ ̇
Prose-ordinal-well-order-Ordinal = Ordinal

-- lem:ext-gives-set
Lemma-5-2 : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
          → is-prop-valued _<_
          → is-extensional _<_
          → is-set X
Lemma-5-2 _<_ = extensionally-ordered-types-are-sets _<_ fe

-- ex:standard-ordinals (1)
Examples-5-3-ω : Ordinal 𝓤₀
Examples-5-3-ω = ω

-- ex:standard-ordinals (2)
Examples-5-3-prop-ordinal : (P : 𝓤 ̇ ) → is-prop P → Ordinal 𝓤
Examples-5-3-prop-ordinal = prop-ordinal

Examples-5-3-𝟘ₒ : Ordinal 𝓤
Examples-5-3-𝟘ₒ = 𝟘ₒ

Examples-5-3-𝟙ₒ : Ordinal 𝓤
Examples-5-3-𝟙ₒ = 𝟙ₒ

-- ex:standard-ordinals (3)
Examples-5-3-𝟚ₒ : Ordinal 𝓤
Examples-5-3-𝟚ₒ = 𝟚ₒ

-- ex:standard-ordinals (4)
Examples-5-3-Ωₒ : Ordinal 𝓤₁
Examples-5-3-Ωₒ = Ωₒ

-- not:ordinals
Notation-5-4 : Ordinal 𝓤 → 𝓤 ̇
Notation-5-4 = ⟨_⟩

-- claim ordinal-of-ordinals
Prose-ordinal-of-ordinals : (𝓤 : Universe) → Ordinal (𝓤 ⁺)
Prose-ordinal-of-ordinals = OO

Prose-ordinal-of-ordinals-⊲ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤 ⁺ ̇
Prose-ordinal-of-ordinals-⊲ = _⊲_

Prose-ordinal-of-ordinals-↓ : (α : Ordinal 𝓤) → ⟨ α ⟩ → Ordinal 𝓤
Prose-ordinal-of-ordinals-↓ = _↓_

Prose-ordinal-of-ordinals-is-set : {𝓤 : Universe} → is-set (Ordinal 𝓤)
Prose-ordinal-of-ordinals-is-set {𝓤} = underlying-type-is-set fe (OO 𝓤)

Prose-ordinal-of-ordinals-↓-preserves-order
 : (α : Ordinal 𝓤) (a b : ⟨ α ⟩) → a ≺⟨ α ⟩ b → (α ↓ a) ⊲ (α ↓ b)
Prose-ordinal-of-ordinals-↓-preserves-order = ↓-preserves-order

-- claim ordinal-comparisons
Prose-ordinal-comparisons : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-comparisons = _⊴_

Prose-ordinal-comparisons-simulation
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-comparisons-simulation = is-simulation

Prose-ordinal-comparisons-order-preserving
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-comparisons-order-preserving = Ordinals.Maps.is-order-preserving

Prose-ordinal-comparisons-initial-segment
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → (⟨ α ⟩ → ⟨ β ⟩) → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-comparisons-initial-segment = Ordinals.Maps.is-initial-segment

Prose-ordinal-comparisons-⊲-gives-⊴ : (α β : Ordinal 𝓤) → α ⊲ β → α ⊴ β
Prose-ordinal-comparisons-⊲-gives-⊴ = ⊲-gives-⊴

Prose-ordinal-comparisons-⊲-⊴ : (α β γ : Ordinal 𝓤) → α ⊲ β → β ⊴ γ → α ⊲ γ
Prose-ordinal-comparisons-⊲-⊴ = ⊲-⊴-gives-⊲

Prose-ordinal-comparisons-at-most-one-simulation
 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f f' : ⟨ α ⟩ → ⟨ β ⟩)
 → is-simulation α β f
 → is-simulation α β f'
 → f ∼ f'
Prose-ordinal-comparisons-at-most-one-simulation =
 Ordinals.Maps.at-most-one-simulation

Prose-ordinal-comparisons-⊴-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                    → is-prop (α ⊴ β)
Prose-ordinal-comparisons-⊴-is-prop = ⊴-is-prop-valued

Prose-ordinal-comparisons-≃ₒ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-comparisons-≃ₒ = _≃ₒ_

Prose-ordinal-comparisons-≃ₒ-is-prop : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                     → is-prop (α ≃ₒ β)
Prose-ordinal-comparisons-≃ₒ-is-prop = ≃ₒ-is-prop-valued fe'

-- lem:surjective-simulations-are-order-equivs
Lemma-5-5 : (α : Ordinal 𝓤) (β : Ordinal 𝓥) (f : ⟨ α ⟩ → ⟨ β ⟩)
          → is-simulation α β f
          → is-surjection f
          → is-order-equiv α β f
Lemma-5-5 = surjective-simulations-are-order-equivs pt fe

-- def:trichotomy
Definition-5-6 : Ordinal 𝓤 → 𝓤 ̇
Definition-5-6 = is-trichotomous

Definition-5-6-Ordinal₃ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-5-6-Ordinal₃ = Ordinal₃

-- rem:trichotomy-EM, excluded middle gives trichotomy
Remark-5-7 : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
           → excluded-middle 𝓥
           → is-well-order _<_
           → is-trichotomous-order _<_
Remark-5-7 = trichotomy₃

-- rem:trichotomy-EM, the converse
Remark-5-7' : funext 𝓤 𝓤₀
            → Every-Discrete-Ordinal-Is-Trichotomous 𝓤
            → EM 𝓤
Remark-5-7' = EM-if-Every-Discrete-Ordinal-Is-Trichotomous

-- lem:trichotomy-gives-discrete
Lemma-5-8 : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
          → is-well-founded _<_
          → is-trichotomous-order _<_
          → is-discrete X
Lemma-5-8 = trichotomous-gives-discrete

-- def:ordinal-addition
Definition-5-9 : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
Definition-5-9 = _+ₒ_

-- lem:addition-well-order
Lemma-5-10 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ ) (_≺_ : Y → Y → 𝓦 ̇ )
          → is-well-order _<_
          → is-well-order _≺_
          → is-well-order (plus.order _<_ _≺_)
Lemma-5-10 = plus.well-order

-- def:lexicographic-order
Definition-5-11 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                → (X → X → 𝓦 ̇ )
                → ({x : X} → Y x → Y x → 𝓣 ̇ )
                → (Σ Y → Σ Y → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ )
Definition-5-11 = slex-order

-- lem:lex-order, proposition-valuedness
Lemma-5-12-prop-valued
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ )
   (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
 → is-prop-valued _<_
 → is-well-founded _<_
 → is-extensional _<_
 → ((x : X) → is-prop-valued (_≺_ {x}))
 → is-prop-valued (sum.order _<_ _≺_)
Lemma-5-12-prop-valued _<_ _≺_ = sum.prop-valued _<_ _≺_ fe

-- lem:lex-order, transitivity
Lemma-5-12-transitive
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ )
   (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
 → is-transitive _<_
 → ((x : X) → is-transitive (_≺_ {x}))
 → is-transitive (sum.order _<_ _≺_)
Lemma-5-12-transitive = sum.transitive

-- lem:lex-order, well-foundedness
Lemma-5-12-well-founded
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ )
   (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
 → is-well-founded _<_
 → ((x : X) → is-well-founded (_≺_ {x}))
 → is-well-founded (sum.order _<_ _≺_)
Lemma-5-12-well-founded = sum.well-founded

-- lem:lex-order, extensionality for a constant family
Lemma-5-12-extensional
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ ) (_≺_ : Y → Y → 𝓣 ̇ )
 → is-well-order _<_
 → is-well-order _≺_
 → is-well-order (times.order _<_ _≺_)
Lemma-5-12-extensional _<_ _≺_ = times.well-order _<_ _≺_ fe

-- def:ordinal-multiplication
Definition-5-13 : Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
Definition-5-13 = _×ₒ_

-- lem:sum-map-order (1), item:sum-map-order-preserving
Lemma-5-14-1 : (τ υ : Ordᵀ) (A : ⟨ τ ⟩ → Ordᵀ) (B : ⟨ υ ⟩ → Ordᵀ)
               (f : ⟨ τ ⟩ → ⟨ υ ⟩)
               (g : (x : ⟨ τ ⟩) → ⟨ A x ⟩ → ⟨ B (f x) ⟩)
             → is-order-preserving τ υ f
             → ((x : ⟨ τ ⟩) → is-order-preserving (A x) (B (f x)) (g x))
             → is-order-preserving (∑ τ A) (∑ υ B) (pair-fun f g)
Lemma-5-14-1 = pair-fun-is-order-preserving

-- lem:sum-map-order (2), item:sum-map-order-reflecting
Lemma-5-14-2 : (τ υ : Ordᵀ) (A : ⟨ τ ⟩ → Ordᵀ) (B : ⟨ υ ⟩ → Ordᵀ)
               (f : ⟨ τ ⟩ → ⟨ υ ⟩)
               (g : (x : ⟨ τ ⟩) → ⟨ A x ⟩ → ⟨ B (f x) ⟩)
             → is-order-reflecting τ υ f
             → is-embedding f
             → ((x : ⟨ τ ⟩) → is-order-reflecting (A x) (B (f x)) (g x))
             → is-order-reflecting (∑ τ A) (∑ υ B) (pair-fun f g)
Lemma-5-14-2 = pair-fun-is-order-reflecting

-- rem:lex-not-extensional
Remark-5-15 : is-extensional _≺ˢ_ → EM 𝓤₀
Remark-5-15 = shulmans-taboo

Remark-5-15' : Extensionality-of-Ordinal-Indexed-Sums 𝓤₁ → EM 𝓤₀
Remark-5-15' = extensionality-of-ordinal-indexed-sums-gives-EM (pe 𝓤₀)

-- lem:trichotomous-sum
Lemma-5-16 : (τ : Ordinal₃ 𝓤) → (⟨ τ ⟩ → Ordinal₃ 𝓤) → Ordinal₃ 𝓤
Lemma-5-16 = ∑³

-- def:topped
Definition-5-17 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-5-17 = Ordinalᵀ

-- ex:NInf-ordinal
Example-5-18 : ℕ∞ → ℕ∞ → 𝓤₀ ̇
Example-5-18 = _≺ℕ∞_

Example-5-18-ordinal : Ordinal 𝓤₀
Example-5-18-ordinal = ℕ∞ₒ

Example-5-18-topped : Ordinalᵀ 𝓤₀
Example-5-18-topped = ℕ∞ᵒ

-- claim topped-arithmetic
Prose-topped-arithmetic : Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤
Prose-topped-arithmetic = _+ᵒ_

Prose-topped-arithmetic' : Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤
Prose-topped-arithmetic' = _×ᵒ_

-- claim trichotomous-arithmetic
Prose-trichotomous-arithmetic : Ordinal₃ 𝓤 → Ordinal₃ 𝓤 → Ordinal₃ 𝓤
Prose-trichotomous-arithmetic = _+₃_

Prose-trichotomous-arithmetic' : Ordinal₃ 𝓤 → Ordinal₃ 𝓤 → Ordinal₃ 𝓤
Prose-trichotomous-arithmetic' = _×₃_

Prose-trichotomous-arithmetic''
 : (τ : Ordinal₃ 𝓤) → (⟨ τ ⟩ → Ordinal₃ 𝓤) → Ordinal₃ 𝓤
Prose-trichotomous-arithmetic'' = ∑³

\end{code}

That the sum of a topped-ordinal-indexed family of topped ordinals is
again topped is Lemma 5.19 below.

Labels: Lemma 5.19 = lem:topped-sum.

\begin{code}

-- lem:topped-sum
Lemma-5-19 : (τ : Ordinalᵀ 𝓤) → (⟨ τ ⟩ → Ordinalᵀ 𝓤) → Ordinalᵀ 𝓤
Lemma-5-19 = ∑

-- lem:sum-compact
Lemma-5-20 : (τ : Ordᵀ) (υ : ⟨ τ ⟩ → Ordᵀ)
                 → is-compact∙ ⟨ τ ⟩
                 → ((x : ⟨ τ ⟩) → is-compact∙ ⟨ υ x ⟩)
                 → is-compact∙ ⟨ ∑ τ υ ⟩
Lemma-5-20 = ∑-compact∙

-- lem:ordinal-extension
Lemma-5-21 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
           → (X → Ordinal 𝓦)
           → (X ↪ A)
           → (A → Ordinal (𝓤 ⊔ 𝓥 ⊔ 𝓦))
Lemma-5-21 = _↗_

-- lem:extension-top
Lemma-5-22 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
           → (X → Ordinalᵀ 𝓦)
           → (X ↪ A)
           → (A → Ordinalᵀ (𝓤 ⊔ 𝓥 ⊔ 𝓦))
Lemma-5-22 = _↗ᵀ_

-- lem:extension-restricts
Lemma-5-23 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
             (α : X → Ordinal 𝓦)
             (𝓮@(j , _) : X ↪ A)
             (x : X)
           → (α ↗ 𝓮) (j x) ≃ₒ α x
Lemma-5-23 = ↗-propertyₒ

-- lem:extension-restricts, algebraic injectivity of the type of ordinals
Lemma-5-23-ainjective : is-univalent (𝓤 ⊔ 𝓥)
                      → ainjective-type (Ordinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Lemma-5-23-ainjective = Ordinal-is-ainjective

-- lem:extension-restricts, and of the type of totally separated ordinals
Lemma-5-23-ainjective-TS : is-univalent (𝓤 ⊔ 𝓥)
                         → ainjective-type (TSOrdinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Lemma-5-23-ainjective-TS = TSOrdinal-is-ainjective fe

-- lem:extension-totally-separated
Lemma-5-24
 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
   (α : X → Ordinal 𝓦)
   (𝓮 : X ↪ A)
 → ((x : X) → is-totally-separated ⟨ α x ⟩)
 → (a : A) → is-totally-separated ⟨ (α ↗ 𝓮) a ⟩
Lemma-5-24 = ↗-is-totally-separated fe

-- claim ordinals-are-ainjective
Prose-ordinals-are-ainjective : ainjective-type (Ordinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Prose-ordinals-are-ainjective {𝓤} {𝓥} = Ordinal-is-ainjective (ua (𝓤 ⊔ 𝓥))

Prose-ordinals-are-ainjective' : ainjective-type (TSOrdinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Prose-ordinals-are-ainjective' {𝓤} {𝓥} =
 TSOrdinal-is-ainjective fe (ua (𝓤 ⊔ 𝓥))

Prose-ordinals-are-ainjective'' : (α β : Ordinal 𝓤) → α ≃ₒ β → α ＝ β
Prose-ordinals-are-ainjective'' {𝓤} = eqtoidₒ (ua 𝓤) fe'

-- def:extended-and-successor-sum (1), item:extended-sum
Definition-5-25-1 : (ℕ → Ordᵀ) → Ordᵀ
Definition-5-25-1 = ∑¹

Definition-5-25-1-explicitly
 : (X : ℕ → 𝓤 ̇ )
 → Σ¹ X ＝ (Σ u ꞉ ℕ∞ , ((φ : is-finite u) → X (size φ)))
Definition-5-25-1-explicitly = Σ¹-explicitly

Definition-5-25-1-compact∙ : (X : ℕ → 𝓤 ̇ )
                           → ((n : ℕ) → is-compact∙ (X n))
                           → is-compact∙ (Σ¹ X)
Definition-5-25-1-compact∙ = Σ¹-compact∙

-- def:extended-and-successor-sum (2), item:successor-sum
Definition-5-25-2 : (ℕ → Ordᵀ) → Ordᵀ
Definition-5-25-2 = ∑₁

-- lem:successor-sum, the underlying type of the successor sum and its top
Lemma-5-26-shape : (X : ℕ → 𝓤 ̇ ) → Σ₁ X ≃ (Σ n ꞉ ℕ , X n) + 𝟙 {𝓤}
Lemma-5-26-shape = Σ₁-explicitly

Lemma-5-26-shape-top : (τ : ℕ → Ordᵀ) → Σ₁-base (top (∑₁ τ)) ＝ inr ⋆
Lemma-5-26-shape-top = ∑₁-top-is-over-inr

-- lem:successor-sum (1), item:successor-sum-is-successor
Lemma-5-26-1 : (τ : ℕ → Ordᵀ) → [ ∑₁ τ ] ≃ₒ (∑ₒ ω τ +ₒ 𝟙ₒ)
Lemma-5-26-1 = ∑₁-is-successorₒ

-- lem:successor-sum (2), item:successor-sum-retract
Lemma-5-26-2 : {X : ℕ → 𝓤 ̇ }
             → ((n : ℕ) → retract (X n) of ℕ)
             → retract (Σ₁ X) of ℕ
Lemma-5-26-2 = Σ₁-ℕ-retract

Lemma-5-26-2-discrete : (X : ℕ → 𝓤 ̇ )
                      → ((n : ℕ) → is-discrete (X n))
                      → is-discrete (Σ₁ X)
Lemma-5-26-2-discrete = Σ₁-is-discrete

-- def:sum-comparison
Definition-5-27 : (X : ℕ → 𝓤 ̇ ) → Σ₁ X → Σ¹ X
Definition-5-27 = Σ-up

Definition-5-27-ordinals : (τ : ℕ → Ordᵀ) → ⟨ ∑₁ τ ⟩ → ⟨ ∑¹ τ ⟩
Definition-5-27-ordinals = ∑-up

Definition-5-27-lc : left-cancellable ι𝟙
Definition-5-27-lc = ι𝟙-lc

-- lem:sum-comparison
Lemma-5-28-embedding : (X : ℕ → 𝓤 ̇ ) → is-embedding (Σ-up X)
Lemma-5-28-embedding = Σ-up-embedding

Lemma-5-28-dense : (X : ℕ → 𝓤 ̇ ) → is-dense (Σ-up X)
Lemma-5-28-dense = Σ-up-dense

Lemma-5-28-order-preserving
 : (τ : ℕ → Ordᵀ) → is-order-preserving (∑₁ τ) (∑¹ τ) (∑-up τ)
Lemma-5-28-order-preserving = ∑-up-is-order-preserving

Lemma-5-28-order-reflecting
 : (τ : ℕ → Ordᵀ) → is-order-reflecting (∑₁ τ) (∑¹ τ) (∑-up τ)
Lemma-5-28-order-reflecting = ∑-up-is-order-reflecting

-- thm:sup, the map σ
Theorem-5-29 : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤)
             → (Σ i ꞉ I , ⟨ α i ⟩) → Ordinal 𝓤
Theorem-5-29 = sum-to-ordinals

-- thm:sup (1), item:sup-is-ordinal
Theorem-5-29-1 : {I : 𝓤 ̇ } → (I → Ordinal 𝓤) → Ordinal 𝓤
Theorem-5-29-1 = sup

-- thm:sup (2), item:sup-surjection
Theorem-5-29-2 : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤)
               → is-surjection (sum-to-sup α)
Theorem-5-29-2 = sum-to-sup-is-surjection

-- thm:sup (3), item:sup-lub
Theorem-5-29-3 : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) (i : I) → α i ⊴ sup α
Theorem-5-29-3 = sup-is-upper-bound

Theorem-5-29-3' : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) (β : Ordinal 𝓤)
                → ((i : I) → α i ⊴ β)
                → sup α ⊴ β
Theorem-5-29-3' = sup-is-lower-bound-of-upper-bounds

Theorem-5-29-3'' : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) (i : I) (x : ⟨ α i ⟩)
                 → sup α ↓ [ α i , sup α ]⟨ sup-is-upper-bound α i ⟩ x
                 ＝ α i ↓ x
Theorem-5-29-3'' = initial-segment-of-sup-at-component

-- cor:sup-compact
Corollary-5-30 : {I : 𝓤 ̇ } {α : I → Ordinal 𝓤}
               → is-compact∙ I
               → ((i : I) → is-compact∙ ⟨ α i ⟩)
               → is-compact∙ ⟨ sup α ⟩
Corollary-5-30 = sup-is-compact∙ sr

-- thm:extended-sup-compact
Theorem-5-31 : {X K : 𝓤 ̇ } (𝓮@(j , _) : X ↪ K) (α : X → Ordinal 𝓤)
             → is-compact∙ K
             → ((x : X) → is-compact∙ ⟨ α x ⟩)
             → is-compact∙ ⟨ sup (α ↗ 𝓮) ⟩
Theorem-5-31 (j , j-is-embedding) α K-compact∙ α-compact∙ =
 sup-is-compact∙ sr K-compact∙
  (λ k → micro-tychonoff (fe _ _) (j-is-embedding k) (α-compact∙ ∘ pr₁))

-- def:extended-supremum
Definition-5-32 : (ℕ → Ordinal 𝓤₀) → Ordinal 𝓤₀
Definition-5-32 α = sup (α ↗ embedding-ℕ-to-ℕ∞ fe₀)

\end{code}

Section 6. Ordinal codes

Labels: Section 6 = sec:brouwer-standard.

\begin{code}

-- def:brouwer-codes
Definition-6-1 : 𝓤₀ ̇
Definition-6-1 = B

Definition-6-1-recursion : {X : 𝓤 ̇ } → X → (X → X) → ((ℕ → X) → X) → B → X
Definition-6-1-recursion = B-rec

\end{code}

The paper denotes the interpretations with a descriptive subscript
recording how the limit constructor is read (sup for a supremum, Σ for
a sum), a superscript 1 for first extending the family along ℕ ↪ ℕ∞,
and a subscript 1 for first extending it along ℕ ↪ ℕ + 𝟙. The mixfix
names below match the paper's notation:

  ⟦_⟧-sup  = ⟦_⟧₀   (the paper's sup)
  ⟦_⟧-Σ    = ⟦_⟧₃   (the paper's Σ)
  ⟦_⟧-sup¹ = ⟦_⟧₂   (the paper's sup¹)
  ⟦_⟧-Σ₁   = BDC.Δ  (the paper's Σ₁)
  ⟦_⟧-Σ¹   = ⟦_⟧₁   (the paper's Σ¹)
  ⟦_⟧-Σ'   = BDC.Κ  (again the paper's Σ¹, but redefined locally
                     in TypeTopology to avoid unnecessary assumptions)

Two of these, ⟦_⟧-Σ₁ and ⟦_⟧-Σ', come from a different module from the
other four, Ordinals.BrouwerCodesDiscreteAndCompactInterpretations,
where they are called Δ and Κ, the first of them Δ because it is the
discrete interpretation, and the second Κ because it is the compact
interpretation.

\begin{code}

⟦_⟧-sup : B → Ordinal 𝓤₀
⟦_⟧-sup = ⟦_⟧₀

⟦_⟧-Σ : B → Ordinal₃ 𝓤₀
⟦_⟧-Σ = ⟦_⟧₃

⟦_⟧-sup¹ : B → Ordinal 𝓤₀
⟦_⟧-sup¹ = ⟦_⟧₂

⟦_⟧-Σ₁ : B → Ordinalᵀ 𝓤₀
⟦_⟧-Σ₁ = BDC.Δ

⟦_⟧-Σ¹ : B → Ordinalᵀ 𝓤₀
⟦_⟧-Σ¹ = ⟦_⟧₁

⟦_⟧-Σ' : B → Ordinalᵀ 𝓤₀
⟦_⟧-Σ' = BDC.Κ

-- def:std-interp
Definition-6-2 : B → Ordinal 𝓤₀
Definition-6-2 = ⟦_⟧-sup

-- prop:std-compact-lpo
Proposition-6-3 : ((b : B) → is-compact ⟨ ⟦ b ⟧-sup ⟩) → LPO
Proposition-6-3 = ⟦_⟧₀-compact-gives-LPO

-- prop:failure-trichotomy
Proposition-6-4 : ((b : B) → is-trichotomous ⟦ b ⟧-sup) → LPO
Proposition-6-4 = FTr.trichotomy-of-the-standard-interpretation-gives-LPO

\end{code}

The sharpened statement of Remark 6.5 is the following, in which the
code depends on the conatural number by a fixed recipe and trichotomy
is assumed of that code.

Labels: Remark 6.5 = rem:trichotomy-hypothesis-use.

\begin{code}

-- rem:trichotomy-hypothesis-use
Remark-6-5 : (u : ℕ∞)
           → is-trichotomous ⟦ FTr.brouwer-code u ⟧-sup
           → is-decidable (is-finite u)
Remark-6-5 = FTr.main-lemma

-- def:non-standard-interpretations
Definition-6-6-Σ : B → Ordinal₃ 𝓤₀
Definition-6-6-Σ = ⟦_⟧-Σ

Definition-6-6-Σ¹ : B → Ordinalᵀ 𝓤₀
Definition-6-6-Σ¹ = ⟦_⟧-Σ¹

Definition-6-6-sup¹ : B → Ordinal 𝓤₀
Definition-6-6-sup¹ = ⟦_⟧-sup¹

-- thm:four-interp-props (1), item:trich-interp
Theorem-6-7-1 : (b : B) → is-trichotomous-order (underlying-order ⟦ b ⟧-Σ)
Theorem-6-7-1 b = 3is-trichotomous ⟦ b ⟧-Σ

-- thm:four-interp-props (2), item:compactsep-interp
Theorem-6-7-2 : (b : B) → is-compact∙ ⟨ ⟦ b ⟧-Σ¹ ⟩
Theorem-6-7-2 = ⟦_⟧₁-is-compact∙

Theorem-6-7-2' : (b : B) → is-totally-separated ⟨ ⟦ b ⟧-Σ¹ ⟩
Theorem-6-7-2' = ⟦_⟧₁-is-totally-separated

-- thm:four-interp-props (3), item:compact-interp
Theorem-6-7-3 : (b : B) → is-compact∙ ⟨ ⟦ b ⟧-sup¹ ⟩
Theorem-6-7-3 = ⟦_⟧₂-is-compact∙

-- claim trichotomous-interpretation-is-discrete
Prose-trichotomous-interpretation-is-discrete
 : (b : B) → is-discrete ⟨ ⟦ b ⟧-Σ ⟩
Prose-trichotomous-interpretation-is-discrete = ⟦_⟧₃-is-discrete

-- prop:trich-compact-lpo
Proposition-6-8 : ((b : B) → is-compact ⟨ ⟦ b ⟧-Σ ⟩) → LPO
Proposition-6-8 = ⟦_⟧₃-compact-gives-LPO

-- prop:failure-tot-sep
Proposition-6-9 : ((b : B) → is-totally-separated ⟨ ⟦ b ⟧-sup¹ ⟩) → ¬¬ WLPO
Proposition-6-9
 = FTS.total-separatedness-of-the-sup-of-extension-interpretation-gives-¬¬WLPO

\end{code}

Examples 3.13(1) has no entry. That total separatedness is not closed
under sums is the example of Examples 3.10(3), whose index type and
fibers are totally separated by the two entries following
Examples-3-10-3 above. That it is not closed under surjective images
is Example 6.10 below.

Labels: Examples 3.13(1) = ex:tot-sep(item:ts-not-sigma),
Examples 3.10(3) = ex:tot-sep-failures(item:two-infinities-not-tot-sep),
Example 6.10 = ex:tot-sep-counterexample.

\begin{code}

-- ex:tot-sep-counterexample
Example-6-10 : Σ I ꞉ 𝓤₀ ̇ , Σ α ꞉ (I → Ordinal 𝓤₀) ,
               is-compact∙ I
             × is-totally-separated I
             × ((i : I) → is-compact∙ ⟨ α i ⟩)
             × ((i : I) → is-totally-separated ⟨ α i ⟩)
             × (is-totally-separated ⟨ sup α ⟩ → ¬¬ WLPO)
Example-6-10 = FTS.counterexample-to-total-separatedness

-- claim extension-is-partial-boolean
Prose-extension-is-partial-boolean
 : (u : ℕ∞) → ⟨ FTS.α̅ u ⟩ ＝ (is-finite u → 𝟚)
Prose-extension-is-partial-boolean u = refl

-- def:sierpinski
Definition-6-11 : 𝓤 ̇ → 𝓤 ̇
Definition-6-11 = FTS.is-semidecidable

Definition-6-11-𝕊 : 𝓤₁ ̇
Definition-6-11-𝕊 = FTS.𝕊

Definition-6-11-order : FTS.𝕊 → FTS.𝕊 → 𝓤₁ ̇
Definition-6-11-order = FTS._≺ₛ_

Definition-6-11-⊥ : FTS.𝕊
Definition-6-11-⊥ = FTS.⊥ₛ

Definition-6-11-⊤ : FTS.𝕊
Definition-6-11-⊤ = FTS.⊤ₛ

Definition-6-11-ordinal : Ordinal 𝓤₁
Definition-6-11-ordinal = FTS.𝓢

-- lem:sierpinski-ordinal
Lemma-6-12-prop-valued : is-prop-valued FTS._≺ₛ_
Lemma-6-12-prop-valued = FTS.≺ₛ-prop-valued

Lemma-6-12-transitive : is-transitive FTS._≺ₛ_
Lemma-6-12-transitive = FTS.≺ₛ-transitive

Lemma-6-12-extensional : is-extensional FTS._≺ₛ_
Lemma-6-12-extensional = FTS.≺ₛ-extensional

Lemma-6-12-well-founded : is-well-founded FTS._≺ₛ_
Lemma-6-12-well-founded = FTS.≺ₛ-well-founded

Lemma-6-12-identity : {t t' : FTS.𝕊}
                    → (pr₁ t holds ↔ pr₁ t' holds)
                    → t ＝ t'
Lemma-6-12-identity = FTS.to-𝕊-＝

-- lem:sup-is-sierpinski
Lemma-6-13 : FTS.𝓼 ≃ₒ FTS.𝓢
Lemma-6-13 = FTS.𝓼-is-𝓢

Lemma-6-13-small : is-small FTS.𝕊
Lemma-6-13-small = FTS.𝕊-is-small

-- lem:sierpinski-separation
Lemma-6-14 : (p : FTS.𝕊 → 𝟚) → p FTS.⊥ₛ ≠ p FTS.⊤ₛ → WLPO
Lemma-6-14 = FTS.𝕊-separation-gives-WLPO

Lemma-6-14' : is-totally-separated FTS.𝕊 → ¬¬ WLPO
Lemma-6-14' = FTS.𝕊-totally-separated-gives-¬¬WLPO

-- thm:comparisons
Theorem-6-15-₀₃ : Excluded-Middle → (b : B) → ⟦ b ⟧-sup ⊴ [ ⟦ b ⟧-Σ ]
Theorem-6-15-₀₃ = comparison₀₃

Theorem-6-15-₀₂ : EM 𝓤₁ → (b : B) → ⟦ b ⟧-sup ⊴ ⟦ b ⟧-sup¹
Theorem-6-15-₀₂ = comparison₀₂

Theorem-6-15-₂₁ : Excluded-Middle → (b : B) → ⟦ b ⟧-sup¹ ⊴ [ ⟦ b ⟧-Σ¹ ]
Theorem-6-15-₂₁ = comparison₂₁

Theorem-6-15-₃₁ : EM 𝓤₀ → (b : B) → [ ⟦ b ⟧-Σ ] ⊴ [ ⟦ b ⟧-Σ¹ ]
Theorem-6-15-₃₁ = comparison₃₁

-- prop:comparisons-taboos (1), item:comparison03-gives-lpo
Proposition-6-16-1 : ((b : B) → ⟦ b ⟧-sup ⊴ [ ⟦ b ⟧-Σ ]) → LPO
Proposition-6-16-1 = FTr.comparison₀₃-gives-LPO

-- prop:comparisons-taboos (2), item:comparison21-gives-notnot-wlpo
Proposition-6-16-2 : ((b : B) → ⟦ b ⟧-sup¹ ⊴ [ ⟦ b ⟧-Σ¹ ]) → ¬¬ WLPO
Proposition-6-16-2 = FTS.comparison₂₁-gives-¬¬WLPO

\end{code}

Question 6.17, which is not formalizable, asks whether the remaining
two comparisons, comparison₀₂ and comparison₃₁ holding for every code,
imply a constructive taboo.

Labels: Question 6.17 = q:comparisons-taboos.

\begin{code}

-- def:delta-kappa
Definition-6-18 : B → Ordᵀ
Definition-6-18 = ⟦_⟧-Σ₁

-- thm:delta-kappa-props (1), item:delta-trichotomous
Theorem-6-19-1 : (b : B) → is-trichotomous [ ⟦ b ⟧-Σ₁ ]
Theorem-6-19-1 = BDC.Δ-is-trichotomous

-- thm:delta-kappa-props (2), item:kappa-compact
Theorem-6-19-2 : (b : B) → is-compact∙ ⟨ ⟦ b ⟧-Σ' ⟩
Theorem-6-19-2 = BDC.Κ-compact∙

-- thm:delta-kappa-props (3), item:delta-retract-N
Theorem-6-19-3 : (b : B) → retract ⟨ ⟦ b ⟧-Σ₁ ⟩ of ℕ
Theorem-6-19-3 = BDC.Δ-retract-of-ℕ

Theorem-6-19-3' : (b : B) → is-discrete ⟨ ⟦ b ⟧-Σ₁ ⟩
Theorem-6-19-3' = BDC.Δ-is-discrete

-- thm:delta-kappa-props (4), item:kappa-retract-cantor
Theorem-6-19-4 : (b : B) → retract ⟨ ⟦ b ⟧-Σ' ⟩ of (ℕ → 𝟚)
Theorem-6-19-4 = BDC.Κ-Cantor-retract

Theorem-6-19-4' : (b : B) → is-totally-separated ⟨ ⟦ b ⟧-Σ' ⟩
Theorem-6-19-4' = BDC.Κ-is-totally-separated

-- rem:tot-sep-via-cantor
Remark-6-20 : (X : ℕ → 𝓤 ̇ )
            → ((n : ℕ) → is-totally-separated (X n))
            → is-totally-separated (Σ¹ X)
Remark-6-20 = Σ¹-is-totally-separated

Remark-6-20' : (A : ℕ∞ → 𝓥 ̇ )
             → ((u : ℕ∞) → is-totally-separated (A u))
             → is-prop (A ∞)
             → is-totally-separated (Σ A)
Remark-6-20'
 = Σ-indexed-by-ℕ∞-is-totally-separated-if-family-at-∞-is-prop fe₀

-- prop:delta-kappa-fail (1), item:delta-compact-lpo
Proposition-6-21-1 : ((b : B) → is-compact ⟨ ⟦ b ⟧-Σ₁ ⟩) ↔ LPO
Proposition-6-21-1 = BDC.Δ-compact-iff-LPO

-- prop:delta-kappa-fail (2), item:kappa-discrete-wlpo
Proposition-6-21-2 : ((b : B) → is-discrete ⟨ ⟦ b ⟧-Σ' ⟩) → WLPO
Proposition-6-21-2 = BDC.Κ-discrete-gives-WLPO

-- def:iota
Definition-6-22 : {b : B} → ⟨ ⟦ b ⟧-Σ₁ ⟩ → ⟨ ⟦ b ⟧-Σ' ⟩
Definition-6-22 {b} = BDC.ι {b}

Definition-6-22-limit-case : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
                           → ((n : ℕ) → X n → Y n)
                           → Σ₁ X → Σ¹ Y
Definition-6-22-limit-case = Σ↑

-- thm:iota (1), an embedding
Theorem-6-23-1 : (b : B) → is-embedding (BDC.ι {b})
Theorem-6-23-1 = BDC.ι-is-embedding

-- thm:iota (2), item:iota-density, dense
Theorem-6-23-2 : (b : B) → is-dense (BDC.ι {b})
Theorem-6-23-2 = BDC.ι-is-dense

-- thm:iota (3), order-preserving
Theorem-6-23-3 : (b : B) (x y : ⟨ ⟦ b ⟧-Σ₁ ⟩)
               → x ≺⟨ [ ⟦ b ⟧-Σ₁ ] ⟩ y
               → BDC.ι {b} x ≺⟨ [ ⟦ b ⟧-Σ' ] ⟩ BDC.ι {b} y
Theorem-6-23-3 = BDC.ι-is-order-preserving

-- thm:iota (4), order-reflecting
Theorem-6-23-4 : (b : B) (x y : ⟨ ⟦ b ⟧-Σ₁ ⟩)
               → BDC.ι {b} x ≺⟨ [ ⟦ b ⟧-Σ' ] ⟩ BDC.ι {b} y
               → x ≺⟨ [ ⟦ b ⟧-Σ₁ ] ⟩ y
Theorem-6-23-4 = BDC.ι-is-order-reflecting

-- ex:omega-plus-one
Example-6-24 : [ ∑₁ (λ _ → 𝟙ᵒ) ] ≃ₒ [ succₒ ω ]
Example-6-24 = ∑₁-of-𝟙ᵒ

Example-6-24' : [ ∑¹ (λ _ → 𝟙ᵒ) ] ≃ₒ [ ℕ∞ᵒ ]
Example-6-24' = ∑¹-of-𝟙ᵒ

Example-6-24'' : (τ : ℕ → Ordᵀ) → is-isolated (top (∑₁ τ))
Example-6-24'' = ∑₁-top-is-isolated

-- prop:brouwer-iota-equiv-LPO
Proposition-6-25 : ((b : B) → is-equiv (BDC.ι {b})) ↔ LPO
Proposition-6-25 = BDC.ι-is-equiv-iff-LPO

-- def:has-inf
Definition-6-26 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Definition-6-26 = has-inf

-- def:has-inf (1), item:conditional-root
Definition-6-26-1 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → 𝟚) → X → 𝓤 ̇
Definition-6-26-1 _≤_ = is-conditional-root _≤_

-- def:has-inf (2), item:roots-infimum
Definition-6-26-2 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
Definition-6-26-2 = is-roots-infimum

Definition-6-26-topped : Ordinalᵀ 𝓤 → 𝓤 ̇
Definition-6-26-topped = has-infs-of-complemented-subsets

-- rem:inf-gives-compact
Remark-6-27 : {X : 𝓤 ̇ } (_≤_ : X → X → 𝓥 ̇ ) → has-inf _≤_ → is-compact∙ X
Remark-6-27 = has-inf-gives-compact∙

-- lem:least-element
Lemma-6-28 : {X : 𝓤 ̇ } (_≤_ : X → X → 𝓥 ̇ )
           → has-inf _≤_
           → (p : X → 𝟚)
           → ¬¬ (Σ x ꞉ X , p x ＝ ₀)
           → Σ x₀ ꞉ X , is-least-root _≤_ p x₀
Lemma-6-28 = has-inf-gives-least-root

-- thm:micro-inf-tychonoff
Theorem-6-29 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
             → is-prop X
             → (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
             → ((x : X) → has-inf (λ (y y' : Y x) → ¬ (y' ≺ y)))
             → has-inf (λ (φ γ : Π Y) → ¬ (Σ x ꞉ X , γ x ≺ φ x))
Theorem-6-29 = micro-inf-tychonoff

-- thm:kappa-infs
Theorem-6-30 : propext 𝓤₀
             → (b : B) → has-infs-of-complemented-subsets (⟦ b ⟧-Σ')
Theorem-6-30 = BDC.Κ-has-infs-of-complemented-subsets

-- cor:kappa-least
Corollary-6-31 : propext 𝓤₀
               → (b : B) (p : ⟨ ⟦ b ⟧-Σ' ⟩ → 𝟚)
               → ¬¬ (Σ x ꞉ ⟨ ⟦ b ⟧-Σ' ⟩ , p x ＝ ₀)
               → Σ x₀ ꞉ ⟨ ⟦ b ⟧-Σ' ⟩ , is-least-root
                                       (underlying-weak-order (⟦ b ⟧-Σ')) p x₀
Corollary-6-31 = BDC.Κ-has-least-roots-of-complemented-subsets

-- prop:delta-least-lpo
Proposition-6-32 : propext 𝓤₀
             → (((b : B) (p : ⟨ ⟦ b ⟧-Σ₁ ⟩ → 𝟚)
                  → ¬¬ (Σ x ꞉ ⟨ ⟦ b ⟧-Σ₁ ⟩ , p x ＝ ₀)
                  → Σ x₀ ꞉ ⟨ ⟦ b ⟧-Σ₁ ⟩ , is-least-root
                                          (underlying-weak-order (⟦ b ⟧-Σ₁)) p x₀)
                ↔ LPO)
Proposition-6-32 = BDC.Δ-least-roots-iff-LPO

-- rem:delta-least-single-code
Remark-6-33 : ((p : ⟨ ⟦ (L (λ _ → Z)) ⟧-Σ₁ ⟩ → 𝟚)
                → ¬¬ (Σ x ꞉ ⟨ ⟦ (L (λ _ → Z)) ⟧-Σ₁ ⟩ , p x ＝ ₀)
                → Σ x₀ ꞉ ⟨ ⟦ (L (λ _ → Z)) ⟧-Σ₁ ⟩ ,
                     is-least-root
                      (underlying-weak-order (⟦ (L (λ _ → Z)) ⟧-Σ₁)) p x₀)
            → LPO
Remark-6-33 = BDC.Δ𝟙-least-roots-gives-LPO

\end{code}

Section 7. Codes defined by induction-recursion

Labels: Section 7 = sec:inductive-recursive.

\begin{code}

-- def:E
Definition-7-1 : 𝓤₀ ̇
Definition-7-1 = IRC.E

Definition-7-1-Δ : IRC.E → Ordᵀ
Definition-7-1-Δ = IRC.Δ

-- thm:E-delta
Theorem-7-2 : (ν : IRC.E) → retract ⟨ IRC.Δ ν ⟩ of ℕ
Theorem-7-2 = IRC.Δ-retract-of-ℕ

Theorem-7-2-discrete : (ν : IRC.E) → is-discrete ⟨ IRC.Δ ν ⟩
Theorem-7-2-discrete = IRC.Δ-is-discrete

Theorem-7-2-trichotomous : (ν : IRC.E) → is-trichotomous [ IRC.Δ ν ]
Theorem-7-2-trichotomous = IRC.Δ-is-trichotomous

-- prop:E-delta-lpo (1), item:E-delta-compact
Proposition-7-3-1 : ((ν : IRC.E) → is-compact ⟨ IRC.Δ ν ⟩) ↔ LPO
Proposition-7-3-1 = IRC.Δ-compact-iff-LPO

-- prop:E-delta-lpo (2), item:E-delta-least
Proposition-7-3-2 : propext 𝓤₀
            → (((ν : IRC.E) (p : ⟨ IRC.Δ ν ⟩ → 𝟚)
                 → ¬¬ (Σ x ꞉ ⟨ IRC.Δ ν ⟩ , p x ＝ ₀)
                 → Σ x₀ ꞉ ⟨ IRC.Δ ν ⟩ ,
                      is-least-root (underlying-weak-order (IRC.Δ ν)) p x₀)
               ↔ LPO)
Proposition-7-3-2 = IRC.Δ-least-roots-iff-LPO

-- def:E-kappa
Definition-7-4 : IRC.E → Ordᵀ
Definition-7-4 = IRC.Κ

Definition-7-4-ι : (ν : IRC.E) → ⟨ IRC.Δ ν ⟩ → ⟨ IRC.Κ ν ⟩
Definition-7-4-ι = IRC.ι

Definition-7-4-extension : (ν : IRC.E) (A : ⟨ IRC.Δ ν ⟩ → IRC.E)
                         → ⟨ IRC.Κ ν ⟩ → Ordᵀ
Definition-7-4-extension = IRC.𝓚

Definition-7-4-ι-is-embedding : (ν : IRC.E) → is-embedding (IRC.ι ν)
Definition-7-4-ι-is-embedding = IRC.ι-is-embedding

-- thm:E-props (1), item:E-comp-infima
Theorem-7-5-1 : propext 𝓤₀
              → (ν : IRC.E) → has-infs-of-complemented-subsets (IRC.Κ ν)
Theorem-7-5-1 = IRC.K-has-infs-of-complemented-subsets

Theorem-7-5-1-compact : (ν : IRC.E) → is-Compact ⟨ IRC.Κ ν ⟩ {𝓥}
Theorem-7-5-1-compact = IRC.Κ-Compact

-- thm:E-props, the dagger (†) step
Theorem-7-5-1-extension : propext 𝓤₀
              → (ν : IRC.E) (A : ⟨ IRC.Δ ν ⟩ → IRC.E) (y : ⟨ IRC.Κ ν ⟩)
              → has-infs-of-complemented-subsets (IRC.𝓚 ν A y)
Theorem-7-5-1-extension = IRC.𝓚-has-infs-of-complemented-subsets

-- thm:E-props (2), item:E-iota-embedding
Theorem-7-5-2-dense : (ν : IRC.E) → is-dense (IRC.ι ν)
Theorem-7-5-2-dense = IRC.ι-is-dense

Theorem-7-5-2-order-preserving
 : (ν : IRC.E) (x y : ⟨ IRC.Δ ν ⟩)
 → x ≺⟨ [ IRC.Δ ν ] ⟩ y
 → IRC.ι ν x ≺⟨ [ IRC.Κ ν ] ⟩ IRC.ι ν y
Theorem-7-5-2-order-preserving = IRC.ι-is-order-preserving

Theorem-7-5-2-order-reflecting
 : (ν : IRC.E) (x y : ⟨ IRC.Δ ν ⟩)
 → IRC.ι ν x ≺⟨ [ IRC.Κ ν ] ⟩ IRC.ι ν y
 → x ≺⟨ [ IRC.Δ ν ] ⟩ y
Theorem-7-5-2-order-reflecting = IRC.ι-is-order-reflecting

-- cor:E-least
Corollary-7-6 : propext 𝓤₀
              → (ν : IRC.E) (p : ⟨ IRC.Κ ν ⟩ → 𝟚)
              → ¬¬ (Σ x ꞉ ⟨ IRC.Κ ν ⟩ , p x ＝ ₀)
              → Σ x₀ ꞉ ⟨ IRC.Κ ν ⟩ ,
                   is-least-root (underlying-weak-order (IRC.Κ ν)) p x₀
Corollary-7-6 = IRC.K-has-least-roots-of-complemented-subsets

-- prop:E-iota-equiv-discrete (1), item:E-iota-equiv
Proposition-7-7-1 : ((ν : IRC.E) → is-equiv (IRC.ι ν)) ↔ LPO
Proposition-7-7-1 = IRC.ι-is-equiv-iff-LPO

-- prop:E-iota-equiv-discrete (2), item:E-kappa-discrete-lpo
Proposition-7-7-2 : LPO → (ν : IRC.E) → is-discrete ⟨ IRC.Κ ν ⟩
Proposition-7-7-2 = IRC.LPO-gives-Κ-discrete

Proposition-7-7-2' : (ν : IRC.E)
                    → is-equiv (IRC.ι ν)
                    → is-discrete ⟨ IRC.Κ ν ⟩
Proposition-7-7-2' = IRC.ι-is-equiv-gives-Κ-discrete

-- prop:E-iota-equiv-discrete (3), item:E-kappa-discrete-wlpo
Proposition-7-7-3 : ((ν : IRC.E) → is-discrete ⟨ IRC.Κ ν ⟩) → WLPO
Proposition-7-7-3 = IRC.Κ-discrete-gives-WLPO

-- prop:E-delta-below-kappa (1), item:iota1-simulation
Proposition-7-8-1 : [ IRC.Δ IRC.⌜ω+𝟙⌝ ] ⊴ [ IRC.Κ IRC.⌜ω+𝟙⌝ ]
Proposition-7-8-1 = ω+𝟙-is-⊴-ℕ∞

-- prop:E-delta-below-kappa (2), item:E-delta-below-kappa-lpo
Proposition-7-8-2 : ((ν : IRC.E) → [ IRC.Δ ν ] ⊴ [ IRC.Κ ν ]) ↔ LPO
Proposition-7-8-2 = IRC.Δ-⊴-Κ-iff-LPO ua

-- prop:E-delta-below-kappa (2), the code of the forward implication
Proposition-7-8-2-code : IRC.E
Proposition-7-8-2-code = IRC.⌜ω+𝟚⌝ ua

Proposition-7-8-2-instance
 : [ IRC.Δ (IRC.⌜ω+𝟚⌝ ua) ] ⊴ [ IRC.Κ (IRC.⌜ω+𝟚⌝ ua) ] → LPO
Proposition-7-8-2-instance = IRC.Δ-⊴-Κ-gives-LPO ua

-- def:brouwer-to-E
Definition-7-9 : B → IRC.E
Definition-7-9 = BtoE.B-to-E

-- thm:brouwer-to-E, the map is an embedding
Theorem-7-10 : is-embedding BtoE.B-to-E
Theorem-7-10 = BtoE.B-to-E-is-embedding

-- thm:brouwer-to-E (1), item:bemb-discrete
Theorem-7-10-1 : (b : B) → [ ⟦ b ⟧-Σ₁ ] ≃ₒ [ IRC.Δ (BtoE.B-to-E b) ]
Theorem-7-10-1 = BtoE.Δ-agreement

-- thm:brouwer-to-E (2), item:bemb-compact
Theorem-7-10-2 : (b : B) → [ ⟦ b ⟧-Σ' ] ≃ₒ [ IRC.Κ (BtoE.B-to-E b) ]
Theorem-7-10-2 = BtoE.Κ-agreement

-- prop:kappa-not-tot-sep
Proposition-7-11 : ((ν : IRC.E) → is-totally-separated ⟨ IRC.Κ ν ⟩) → ¬¬ WLPO
Proposition-7-11 = IRC.Κ-totally-separated-gives-¬¬WLPO

-- prop:kappa-not-tot-sep, the witnessing code
Proposition-7-11-code : IRC.E
Proposition-7-11-code = IRC.⌜ℕ∞₂⌝

Proposition-7-11-instance
 : is-totally-separated ⟨ IRC.Κ IRC.⌜ℕ∞₂⌝ ⟩ → ¬¬ WLPO
Proposition-7-11-instance = IRC.Κ⌜ℕ∞₂⌝-totally-separated-gives-¬¬WLPO

\end{code}

Remark 7.12 concludes that the ordinals witnessing the failure of
Proposition 7.11 are denoted by no Brouwer code, from Theorem 6.19(4)
and Theorem 7.10. It is a comparison rather than a further claim.

Labels: Remark 7.12 = rem:kappa-tot-sep-contrast,
Proposition 7.11 = prop:kappa-not-tot-sep,
Theorem 6.19(4) = thm:delta-kappa-props(item:kappa-retract-cantor),
Theorem 7.10 = thm:brouwer-to-E.

\begin{code}

-- claim limit-points-for-brouwer-codes
Prose-limit-points-for-brouwer-codes : (b : B) → ⟨ ⟦ b ⟧-Σ₁ ⟩ → 𝟚
Prose-limit-points-for-brouwer-codes = BDC.ℓ

Prose-limit-points-for-brouwer-codes-isolated
 : (b : B) (x : ⟨ ⟦ b ⟧-Σ₁ ⟩)
 → BDC.ℓ b x ＝ ₀ → is-isolated (BDC.ι {b} x)
Prose-limit-points-for-brouwer-codes-isolated = BDC.ℓ-isolated

Prose-limit-points-for-brouwer-codes-limit
 : (b : B) (x : ⟨ ⟦ b ⟧-Σ₁ ⟩)
 → BDC.ℓ b x ＝ ₁ → is-limit-point (BDC.ι {b} x)
Prose-limit-points-for-brouwer-codes-limit = BDC.ℓ-limit

Prose-limit-points-for-brouwer-codes-dichotomy
 : (b : B) (x : ⟨ ⟦ b ⟧-Σ₁ ⟩)
 → is-isolated (BDC.ι {b} x) + is-limit-point (BDC.ι {b} x)
Prose-limit-points-for-brouwer-codes-dichotomy = BDC.isolatedness-decision

Prose-limit-points-for-brouwer-codes-decidable
 : ¬ WLPO
 → (b : B) (x : ⟨ ⟦ b ⟧-Σ₁ ⟩)
 → is-decidable (is-isolated (BDC.ι {b} x))
Prose-limit-points-for-brouwer-codes-decidable = BDC.isolatedness-decision'

-- def:limit-point
Definition-7-13 : {X : 𝓤 ̇ } → X → 𝓤 ̇
Definition-7-13 = is-limit-point

-- def:limitfn
Definition-7-14 : (ν : IRC.E) → ⟨ IRC.Δ ν ⟩ → 𝟚
Definition-7-14 = IRC.ℓ

-- thm:limitfn (1), item:limitfn-isolated
Theorem-7-15-1 : (ν : IRC.E) (x : ⟨ IRC.Δ ν ⟩)
              → IRC.ℓ ν x ＝ ₀
              → is-isolated (IRC.ι ν x)
Theorem-7-15-1 = IRC.ℓ-isolated

-- thm:limitfn (2), item:limitfn-limit
Theorem-7-15-2 : (ν : IRC.E) (x : ⟨ IRC.Δ ν ⟩)
              → IRC.ℓ ν x ＝ ₁
              → is-limit-point (IRC.ι ν x)
Theorem-7-15-2 = IRC.ℓ-limit

-- thm:limitfn (3), item:limitfn-dichotomy
Theorem-7-15-3 : (ν : IRC.E) (x : ⟨ IRC.Δ ν ⟩)
              → is-isolated (IRC.ι ν x) + is-limit-point (IRC.ι ν x)
Theorem-7-15-3 = IRC.isolatedness-decision

-- thm:limitfn (4), item:limitfn-decidable
Theorem-7-15-4 : ¬ WLPO
              → (ν : IRC.E) (x : ⟨ IRC.Δ ν ⟩)
              → is-decidable (is-isolated (IRC.ι ν x))
Theorem-7-15-4 = IRC.isolatedness-decision'

\end{code}

Remark 7.16 states that the order notion of limit point, a point of an
ordinal that is neither a successor of anything nor the least element,
does not agree with the topological notion of Definition 7.13, because
the point (∞ , ι 1) of the compact ordinal Κ ν₂ is a topological limit
point but not an order one.

Labels: Remark 7.16 = rem:limit-points-do-not-agree,
Definition 7.13 = def:limit-point.

\begin{code}

-- rem:limit-points-do-not-agree
Remark-7-16 : Σ α ꞉ Ordinal 𝓤₀ ,
              Σ x ꞉ ⟨ α ⟩ , is-limit-point x
                          × ¬ OLP.is-order-limit-point α x
Remark-7-16 = OLP.example-of-topological-limit-point-which-is-not-order-limit

\end{code}
