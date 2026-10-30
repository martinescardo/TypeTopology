Martin Escardo, 30th October 2026.

This is an Agda companion for the paper

   Compact totally separated types (extended abstract)
   ---------------------------------------------------

   Martín Hötzel Escardó
   https://www.cs.bham.ac.uk/~mhe/

   This file is
   https://github.com/martinescardo/TypeTopology/blob/master/source/TypeTopology/CompactTotallySeparatedTypesExtendedAbstract.lagda

   and its HTML rendering is
   https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.CompactTotallySeparatedTypesExtendedAbstract.html

The extended abstract is a shortened version of the paper [1], which
contains all proofs and has its own Agda companion [2].

This file follows the definitions, lemmas, propositions, theorems,
examples and remarks of the extended abstract, in the same order and
with the same numbering, including the mathematical discussions in its
prose, so that a reader of the extended abstract can walk this file
alongside it. The name of each entry is the number the item has in the
extended abstract, and the comment after it is the LaTeX label of that
item.

Claims that the extended abstract makes in running prose, outside
proofs, appear here too, under names beginning with Prose. Claims
about models rather than about the theory, such as the ones about the
effective topos, are recorded as comments, since they are not
formalizable here.

What the extended abstract calls extreme density is called density in
TypeTopology, and the names below keep the TypeTopology spelling.

We include all HoTT/UF assumptions as module parameters. They do not
include function extensionality because it follows from
univalence. However, the TypeTopology repository is careful to
minimize the number of assumptions for each result, and readers
interested in such foundational issues can follow the definitions
given here to find out exactly what assumptions each result uses.

[1] Martín Hötzel Escardó. Compact totally separated types.
    https://arxiv.org/abs/2609.10447

[2] TypeTopology.CompactTotallySeparatedTypesArticle
    https://github.com/martinescardo/TypeTopology/blob/master/source/TypeTopology/CompactTotallySeparatedTypesArticle.lagda

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.Size
open import UF.Yoneda using (univalence-via-singletons←)
open import UF.EquivalenceExamples using (Σ-cong)
open import UF.Equiv-FunExt using (≃-Sym)
open import UF.Univalence

module TypeTopology.CompactTotallySeparatedTypesExtendedAbstract
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
open import TypeTopology.DenseMapsProperties using (surjections-are-dense)
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
open import UF.Retracts-FunExt
      using (codomain-is-retract-of-function-space-with-pointed-domain)
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
open import TypeTopology.Cantor using (𝟚ᴺ ; module notions-of-continuity)
open notions-of-continuity 𝟚 𝟚-is-discrete using (uniformly-continuous)
open import TypeTopology.CantorSearch
      using (Cantor-uniformly-searchable ; having-root-is-decidable)
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
      using (Cantor ;
             𝔻-Cantor-≃-Cantor ;
             is-Cantor-𝔻-coalgebra-map ;
             Cantor-is-final-𝔻-coalgebra)
open import TypeTopology.DelayMonad fe
      using (𝔻 ;
             is-𝔻-coalgebra-map ;
             𝔻-is-final-coalgebra)
open import TypeTopology.BoundedDecreasingSequences fe'
      using (𝔹 ; 𝔹-is-compact∙ ; 𝔹-is-totally-separated)

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

Section 3. Totally separated types

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

-- prop:discrete-closure (1), item:discrete-plus
Proposition-3-5-1-inl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (x : X)
                      → is-isolated x → is-isolated (inl {𝓤} {𝓥} {X} {Y} x)
Proposition-3-5-1-inl = inl-is-isolated

Proposition-3-5-1-inr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y)
                      → is-isolated y → is-isolated (inr {𝓤} {𝓥} {X} {Y} y)
Proposition-3-5-1-inr = inr-is-isolated

Proposition-3-5-1-+ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → is-discrete X → is-discrete Y → is-discrete (X + Y)
Proposition-3-5-1-+ = +-is-discrete

-- prop:discrete-closure (2), item:discrete-retract
Proposition-3-5-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → retract Y of X → is-discrete X → is-discrete Y
Proposition-3-5-2 = retract-is-discrete

-- prop:discrete-closure (3), item:discrete-sigma
Proposition-3-5-3 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                  → is-discrete X
                  → ((x : X) → is-discrete (Y x))
                  → is-discrete (Σ Y)
Proposition-3-5-3 = Σ-is-discrete

-- prop:discrete-closure (4), item:discrete-sigma-isolated
Proposition-3-5-4 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                  → is-isolated x
                  → is-isolated y
                  → is-isolated {_} {Σ Y} (x , y)
Proposition-3-5-4 = Σ-isolated

Proposition-3-5-4' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
                   → is-set X
                   → is-isolated {_} {Σ Y} (x , y)
                   → is-isolated y
Proposition-3-5-4' = Σ-isolated-right

Proposition-3-5-4'' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y}
                    → is-isolated (x , y)
                    → is-isolated x
Proposition-3-5-4'' = ×-isolated-left

-- prop:discrete-closure (5), item:discrete-reflected
Proposition-3-5-5 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                  → left-cancellable f
                  → (x : X) → is-isolated (f x) → is-isolated x
Proposition-3-5-5 = lc-maps-reflect-isolatedness

Proposition-3-5-5' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                   → is-equiv f
                   → (x : X) → is-isolated x → is-isolated (f x)
Proposition-3-5-5' = equivs-preserve-isolatedness

-- lem:sigma-isolated
Lemma-3-6 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x}
          → ((x : X) → is-Compact (Y x) {𝓤 ⊔ 𝓥})
          → is-isolated (x , y) → is-isolated x
Lemma-3-6 = Σ-isolated-left

-- prop:discrete-exponential (1)
Proposition-3-7-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → has-two-distinct-points Y
                  → is-discrete (X → Y)
                  → is-decidable (is-empty X)
Proposition-3-7-1 =
 discrete-exponential-has-decidable-emptiness-of-exponent fe'

-- prop:discrete-exponential (2)
Proposition-3-7-2 : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
                  → is-prop P
                  → ((p : P) → is-h-isolated (f p))
                  → is-embedding f
Proposition-3-7-2 = maps-of-props-into-h-isolated-points-are-embeddings

Proposition-3-7-2' : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
                   → is-prop P
                   → ((p : P) → is-isolated (f p))
                   → is-embedding f
Proposition-3-7-2' = maps-of-props-into-isolated-points-are-embeddings

-- def:tot-sep
Definition-3-8 : 𝓤 ̇ → 𝓤 ̇
Definition-3-8 = is-totally-separated

-- lem:tot-sep-basic (1), item:disc-gives-ts
Lemma-3-9-1 : {X : 𝓤 ̇ } → is-discrete X → is-totally-separated X
Lemma-3-9-1 = discrete-types-are-totally-separated

-- lem:tot-sep-basic (2), item:ts-gives-nnsep
Lemma-3-9-2 : (X : 𝓤 ̇ ) → is-totally-separated X → is-¬¬-separated X
Lemma-3-9-2 = totally-separated-types-are-¬¬-separated

-- lem:tot-sep-basic (3), item:nn-separated-is-set
Lemma-3-9-3 : {X : 𝓤 ̇ } → is-¬¬-separated X → is-set X
Lemma-3-9-3 = ¬¬-separated-types-are-sets fe'

-- lem:tot-sep-basic (4), item:ts-is-set
Lemma-3-9-4 : (X : 𝓤 ̇ ) → is-totally-separated X → is-set X
Lemma-3-9-4 = totally-separated-types-are-sets fe'


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

-- ex:tot-sep-failures (2), item:two-infinities-not-tot-sep
Examples-3-10-2 : is-totally-separated ℕ∞₂ → ¬¬ WLPO
Examples-3-10-2 = ℕ∞₂-is-not-totally-separated-in-general

-- ex:tot-sep-failures (2), the index type is totally separated
Examples-3-10-2-index : is-totally-separated ℕ∞
Examples-3-10-2-index = ℕ∞-is-totally-separated fe₀

-- ex:tot-sep-failures (2), the fibers are totally separated
Examples-3-10-2-fibers : (u : ℕ∞) → is-totally-separated (u ＝ ∞ → 𝟚)
Examples-3-10-2-fibers u = Π-is-totally-separated fe₀
                            (λ _ → 𝟚-is-totally-separated)

-- prop:tot-sep-closure (1), item:tot-sep-retract
Proposition-3-11-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   → retract Y of X
                   → is-totally-separated X
                   → is-totally-separated Y
Proposition-3-11-1 = retract-of-totally-separated

-- prop:tot-sep-closure (1), item:tot-sep-retract, equivalence
Proposition-3-11-1-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → X ≃ Y
                         → is-totally-separated X
                         → is-totally-separated Y
Proposition-3-11-1-equiv = equiv-to-totally-separated

-- prop:tot-sep-closure (2), item:tot-sep-product
Proposition-3-11-2 : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                   → is-totally-separated X
                   → is-totally-separated Y
                   → is-totally-separated (X × Y)
Proposition-3-11-2 = ×-totally-separated

-- prop:tot-sep-closure (3)
Proposition-3-11-3 : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                   → is-discrete X
                   → ((x : X) → is-totally-separated (Y x))
                   → is-totally-separated (Σ Y)
Proposition-3-11-3 = Σ-is-totally-separated-if-index-type-is-discrete

-- prop:tot-sep-closure (3), the + case
Proposition-3-11-3-+ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                     → is-totally-separated X
                     → is-totally-separated Y
                     → is-totally-separated (X + Y)
Proposition-3-11-3-+ = +-totally-separated

-- prop:tot-sep-closure (4)
Proposition-3-11-4 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   → ((x : X) → is-totally-separated (Y x))
                   → is-totally-separated (Π Y)
Proposition-3-11-4 = Π-is-totally-separated fe'

-- ex:tot-sep (2), item:simple-types
Examples-3-12-2 : 𝓤₀ ̇ → 𝓤₁ ̇
Examples-3-12-2 = simple-type

Examples-3-12-2' : {X : 𝓤₀ ̇ } → simple-type X → is-totally-separated X
Examples-3-12-2' = simple-types-are-totally-separated

Examples-3-12-2'' : {X : 𝓤₀ ̇ } → simple-type X → retract ℕ of X
Examples-3-12-2'' = ℕ-is-retract-of-any-simple-type

-- ex:tot-sep (2), item:simple-types, pointedness and the retract clause
Examples-3-12-2-pointed : {X : 𝓤₀ ̇ } → simple-type X → X
Examples-3-12-2-pointed = simple-types-pointed

Examples-3-12-2-r : {X A : 𝓤₀ ̇ }
                  → retract A of ℕ → simple-type X → retract A of X
Examples-3-12-2-r = simple-types-r

-- ex:tot-sep (2), item:simple-types, the induction step of the retract
Examples-3-12-2-r-step : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                       → X → retract A of Y → retract A of (X → Y)
Examples-3-12-2-r-step x =
 retracts-compose (codomain-is-retract-of-function-space-with-pointed-domain x)

-- ex:tot-sep (3), item:cantor-not-discrete
Examples-3-12-3 : is-discrete (ℕ → 𝟚) → WLPO
Examples-3-12-3 = ℕ∞-discrete-gives-WLPO
                ∘ retract-is-discrete (ℕ∞-retract-of-Cantor fe₀)

-- lem:sigma-NInf-tot-sep
Lemma-3-13 : (A : ℕ∞ → 𝓥 ̇ )
           → ((u : ℕ∞) → is-totally-separated (A u))
           → is-prop (A ∞)
           → is-totally-separated (Σ A)
Lemma-3-13 = Σ-indexed-by-ℕ∞-is-totally-separated-if-family-at-∞-is-prop fe₀


\end{code}

Section 4. Compact types

Labels: Section 4 = sec:compact-types-theory.

\begin{code}

-- def:compact
Definition-4-1 : 𝓤 ̇ → 𝓤 ̇
Definition-4-1 = is-compact

-- lem:compact-decidable
Lemma-4-2 : (X : 𝓤 ̇ ) → is-compact X → is-decidable X
Lemma-4-2 = compact-types-are-decidable

Lemma-4-2' : (X : 𝓤 ̇ ) → is-prop X → is-decidable X → is-compact X
Lemma-4-2' = decidable-propositions-are-compact

-- prop:global-choice
Proposition-4-3 : ((X : 𝓤 ̇ ) → is-Compact X {𝓤}) → Global-Choice 𝓤
Proposition-4-3 = all-types-compact-gives-global-choice

-- prop:global-choice, the converse
Proposition-4-3' : Global-Choice 𝓤 → ((X : 𝓤 ̇ ) → is-Compact X {𝓤})
Proposition-4-3' = global-choice-gives-all-types-compact

-- ex:compact-basic (1), the finite types
Examples-4-4-1-Fin : ℕ → 𝓤₀ ̇
Examples-4-4-1-Fin = Fin

-- ex:compact-basic (1), they are compact
Examples-4-4-1 : {n : ℕ} → is-Compact (Fin n) {𝓤}
Examples-4-4-1 = Fin-Compact

-- ex:compact-basic (2), item:N-compact-lpo
Examples-4-4-2 : is-compact ℕ ↔ LPO
Examples-4-4-2 = compact-ℕ-gives-LPO fe₀ , LPO-gives-compact-ℕ fe₀

-- lem:compact-pt, item:compact-and-pointed from item:universal-witness
Lemma-4-5-2 : {X : 𝓤 ̇ } → is-compact X → X → is-compact∙ X
Lemma-4-5-2 = compact-pointed-types-are-compact∙

-- lem:compact-pt (1), item:compact-and-pointed, against
-- (2), item:universal-witness
Lemma-4-5-1 : {X : 𝓤 ̇ } → is-compact∙ X → is-compact X
Lemma-4-5-1 = compact∙-types-are-compact

Lemma-4-5-1' : {X : 𝓤 ̇ } → is-compact∙ X → X
Lemma-4-5-1' = compact∙-types-are-pointed

-- lem:dense-into-nn-separated-rc
Lemma-4-6 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ } {j : X → Y} {f g : Π Z}
          → is-dense j
          → ((y : Y) → is-¬¬-separated (Z y))
          → f ∘ j ∼ g ∘ j
          → f ∼ g
Lemma-4-6 = dense-maps-into-¬¬-separated-types-are-rc'

-- lem:dense-into-nn-separated-rc, the constant family
Lemma-4-6' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {j : X → Y} {f g : Y → Z}
           → is-dense j
           → is-¬¬-separated Z
           → f ∘ j ∼ g ∘ j
           → f ∼ g
Lemma-4-6' = dense-maps-into-¬¬-separated-types-are-rc

-- ex:compact-pt-basic (1)
Examples-4-7-1 : is-compact∙ 𝟚
Examples-4-7-1 = 𝟚-is-compact∙

-- ex:compact-pt-basic (2), item:NInf-compact
Examples-4-7-2 : is-compact∙ ℕ∞
Examples-4-7-2 = ℕ∞-compact∙

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

-- cor:compact-pt-closure (1), item:pt-retract
Corollary-4-9-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → retract Y Of X → is-compact∙ X → is-compact∙ Y
Corollary-4-9-1 = retract-is-compact∙

Corollary-4-9-1' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → X ≃ Y → is-compact∙ X → is-compact∙ Y
Corollary-4-9-1' = compact∙-types-are-closed-under-equiv

-- cor:compact-pt-closure (2), item:pt-sigma
Corollary-4-9-2 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                → is-compact∙ X
                → ((x : X) → is-compact∙ (Y x))
                → is-compact∙ (Σ Y)
Corollary-4-9-2 = Σ-is-compact∙

-- cor:compact-pt-closure (2), item:pt-sigma, products and coproducts
Corollary-4-9-2-× : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-compact∙ X → is-compact∙ Y → is-compact∙ (X × Y)
Corollary-4-9-2-× = ×-is-compact∙

Corollary-4-9-2-+ : {X₀ X₁ : 𝓤 ̇ }
                  → is-compact∙ X₀ → is-compact∙ X₁ → is-compact∙ (X₀ + X₁)
Corollary-4-9-2-+ = +-is-compact∙

-- cor:compact-pt-closure (3), item:pt-image
Corollary-4-9-3 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                → is-surjection f → is-compact∙ X → is-compact∙ Y
Corollary-4-9-3 = codomain-of-surjection-is-compact∙ pt

Corollary-4-9-3' : {X Y : 𝓤₀ ̇ } (f : X → Y)
                 → is-compact∙ X → is-compact∙ (image f)
Corollary-4-9-3' = image-is-compact∙ pt

-- prop:compact-complemented (1), item:complemented-subtype-compact
Proposition-4-10-1 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                   → is-Compact X {𝓥 ⊔ 𝓦}
                   → is-complemented A
                   → ((x : X) → is-prop (A x))
                   → is-Compact (Σ x ꞉ X , A x) {𝓦}
Proposition-4-10-1 = complemented-subset-of-compact-type

-- prop:compact-complemented (2), item:decide-sum-or-product
Proposition-4-10-2 : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
                   → is-compact X
                   → ((x : X) → A x + B x)
                   → (Σ x ꞉ X , A x) + (Π x ꞉ X , B x)
Proposition-4-10-2 = compact-gives-Σ+Π

-- prop:compact-complemented (3), item:complemented-choice
Proposition-4-10-3 : {X : 𝓤 ̇ } → is-Σ-Compact X {𝓥} → Complemented-choice X {𝓥}
Proposition-4-10-3 = Σ-Compactness-gives-Complemented-choice


\end{code}

Remark 4.11 records that the compactness of the Cantor type is
independent of our type theory, holding in the topological topos and
in the Kleene--Vesley topos and failing in the effective topos. This
is a statement about models rather than a theorem of our type theory,
so it has no entry. What it says about finite products is Theorem 4.8(3).

Labels: Remark 4.11 = rem:tychonoff-independence,
Theorem 4.8(3) = thm:compact-closure(item:compact-sigma).

The paragraph after Remark 4.11 claims that the Brouwerian principle
that all maps of the Cantor type into a discrete type are uniformly
continuous makes the Cantor type compact. The paper does not adopt
this principle, and so the claim takes it as a hypothesis. The two
primed entries are the notions of modulus of uniform continuity and of
uniform continuity that the paragraph defines.

Labels: Remark 4.11 = rem:tychonoff-independence.

\begin{code}

-- claim uniform-continuity-gives-cantor-compact
Prose-uniform-continuity-gives-cantor-compact
 : ((N : 𝓤₀ ̇ ) (d : is-discrete N) (p : 𝟚ᴺ → N)
      → notions-of-continuity.uniformly-continuous N d p)
 → (p : 𝟚ᴺ → 𝟚) → is-decidable (Σ α ꞉ 𝟚ᴺ , p α ＝ ₀)
Prose-uniform-continuity-gives-cantor-compact ucp p
 = having-root-is-decidable p (ucp 𝟚 𝟚-is-discrete p)

Prose-uniform-continuity-gives-cantor-compact'
 : (N : 𝓤 ̇ ) → is-discrete N → ℕ → (𝟚ᴺ → N) → 𝓤 ̇
Prose-uniform-continuity-gives-cantor-compact' N d
 = notions-of-continuity._is-a-modulus-of-uc-of_ N d

Prose-uniform-continuity-gives-cantor-compact''
 : (N : 𝓤 ̇ ) → is-discrete N → (𝟚ᴺ → N) → 𝓤 ̇
Prose-uniform-continuity-gives-cantor-compact'' N d
 = notions-of-continuity.uniformly-continuous N d

-- prop:cantor-uniform-search
Proposition-4-12 : (p : 𝟚ᴺ → 𝟚)
                 → uniformly-continuous p
                 → Σ α₀ ꞉ 𝟚ᴺ , (p α₀ ＝ ₁ → (α : 𝟚ᴺ) → p α ＝ ₁)
Proposition-4-12 = Cantor-uniformly-searchable

Proposition-4-12' : (p : 𝟚ᴺ → 𝟚)
                  → uniformly-continuous p
                  → is-decidable (Σ α ꞉ 𝟚ᴺ , p α ＝ ₀)
Proposition-4-12' = having-root-is-decidable

-- prop:compact-to-discrete
Proposition-4-13 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                 → is-compact X
                 → ((x : X) → is-discrete (Y x))
                 → (f g : (x : X) → Y x) → (f ♯ g) + (f ＝ g)
Proposition-4-13 = apart-or-equal (fe _ _)

-- prop:compact-to-discrete, in particular the product is discrete
Proposition-4-13' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                  → is-compact X
                  → ((x : X) → is-discrete (Y x))
                  → is-discrete ((x : X) → Y x)
Proposition-4-13' = discrete-to-power-compact-is-discrete (fe _ _)

-- ex:discrete-exponentials
Example-4-14 : is-discrete (ℕ∞ → 𝟚)
Example-4-14 = ℕ∞→𝟚-is-discrete

Example-4-14' : is-discrete (ℕ∞ → ℕ)
Example-4-14' = ℕ∞→ℕ-is-discrete

-- thm:micro-tychonoff
Theorem-4-15 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
             → is-prop X
             → ((x : X) → is-compact∙ (Y x))
             → is-compact∙ (Π Y)
Theorem-4-15 = micro-tychonoff fe'

-- ex:LPO-to-N
Example-4-16 : is-compact∙ (LPO → ℕ)
Example-4-16 = [LPO→ℕ]-is-compact∙ fe₀

-- def:extension
Definition-4-17 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (X → 𝓦 ̇ ) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ )
Definition-4-17 = Π-extension

-- lem:extension-property (1), item:ext-restricts
Lemma-4-18-1 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
             → is-embedding j
             → (x : X) → Π-extension f j (j x) ≃ f x
Lemma-4-18-1 = Π-extension-property

-- lem:extension-property (2), item:ext-off-image
Lemma-4-18-2 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y) (y : Y)
             → ((x : X) → j x ≠ y)
             → Π-extension f j y ≃ 𝟙 {𝓣}
Lemma-4-18-2 f j = Π-extension-out-of-range f j

-- lem:extension-property (3), item:extended-sum-compact
Lemma-4-18-3 : {X : 𝓤 ̇ } {K : 𝓥 ̇ } {Y : X → 𝓦 ̇ } (j : X → K)
             → is-embedding j
             → ((x : X) → is-compact∙ (Y x))
             → is-compact∙ K
             → is-compact∙ (Σ (Y / j))
Lemma-4-18-3 = extended-sum-compact∙

-- lem:extension-property (4), item:extension-tot-sep
Lemma-4-18-4 : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (j : X → A) (Y : X → 𝓦 ̇ )
             → ((x : X) → is-totally-separated (Y x))
             → (a : A) → is-totally-separated ((Y / j) a)
Lemma-4-18-4 = /-is-totally-separated fe

-- lem:extension-property (5), item:ext-retract-fiber
Lemma-4-18-5 : {X : 𝓤 ̇ } {K : 𝓥 ̇ } (Y Z : X → 𝓦 ̇ ) (j : X → K)
             → ((x : X) → retract (Y x) of (Z x))
             → (k : K) → retract ((Y / j) k) of ((Z / j) k)
Lemma-4-18-5 = retract-extension

-- lem:extension-property (6), item:ext-retract-sum
Lemma-4-18-6 : {X : 𝓤 ̇ } {K : 𝓥 ̇ } (Y Z : X → 𝓦 ̇ ) (j : X → K)
             → ((x : X) → retract (Y x) of (Z x))
             → retract (Σ (Y / j)) of (Σ (Z / j))
Lemma-4-18-6 Y₀ Y₁ j ρ = Σ-retract (Y₀ / j) (Y₁ / j)
                          (retract-extension Y₀ Y₁ j ρ)

-- lem:delayed-sequences
Lemma-4-19 : 𝔻 Cantor ≃ Cantor
Lemma-4-19 = 𝔻-Cantor-≃-Cantor


\end{code}

Section 5. Equipping compact types with well-orders

Labels: Section 5 = sec:ordinals-prelim.

\begin{code}

-- claim ordinal-well-order
Prose-ordinal-well-order : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Prose-ordinal-well-order = is-well-order

Prose-ordinal-well-order-Ordinal : (𝓤 : Universe) → 𝓤 ⁺ ̇
Prose-ordinal-well-order-Ordinal = Ordinal

-- ex:standard-ordinals (1)
Examples-5-1-ω : Ordinal 𝓤₀
Examples-5-1-ω = ω

-- ex:standard-ordinals (2)
Examples-5-1-prop-ordinal : (P : 𝓤 ̇ ) → is-prop P → Ordinal 𝓤
Examples-5-1-prop-ordinal = prop-ordinal

Examples-5-1-𝟘ₒ : Ordinal 𝓤
Examples-5-1-𝟘ₒ = 𝟘ₒ

Examples-5-1-𝟙ₒ : Ordinal 𝓤
Examples-5-1-𝟙ₒ = 𝟙ₒ

-- ex:standard-ordinals (3)
Examples-5-1-𝟚ₒ : Ordinal 𝓤
Examples-5-1-𝟚ₒ = 𝟚ₒ

-- not:ordinals
Notation-5-2 : Ordinal 𝓤 → 𝓤 ̇
Notation-5-2 = ⟨_⟩

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

-- def:trichotomy
Definition-5-3 : Ordinal 𝓤 → 𝓤 ̇
Definition-5-3 = is-trichotomous

Definition-5-3-Ordinal₃ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-5-3-Ordinal₃ = Ordinal₃

-- lem:trichotomy-gives-discrete (1)
Lemma-5-4-1 : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
            → is-well-founded _<_
            → is-trichotomous-order _<_
            → is-discrete X
Lemma-5-4-1 = trichotomous-gives-discrete

-- lem:trichotomy-gives-discrete (2), item:trichotomy-EM,
-- excluded middle gives trichotomy
Lemma-5-4-2 : {X : 𝓤 ̇ } (_<_ : X → X → 𝓥 ̇ )
            → excluded-middle 𝓥
            → is-well-order _<_
            → is-trichotomous-order _<_
Lemma-5-4-2 = trichotomy₃

-- lem:trichotomy-gives-discrete (2), item:trichotomy-EM,
-- the converse
Lemma-5-4-2' : funext 𝓤 𝓤₀
             → Every-Discrete-Ordinal-Is-Trichotomous 𝓤
             → EM 𝓤
Lemma-5-4-2' = EM-if-Every-Discrete-Ordinal-Is-Trichotomous

-- def:ordinal-addition
Definition-5-5 : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
Definition-5-5 = _+ₒ_

-- def:lexicographic-order
Definition-5-6 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
               → (X → X → 𝓦 ̇ )
               → ({x : X} → Y x → Y x → 𝓣 ̇ )
               → (Σ Y → Σ Y → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ )
Definition-5-6 = slex-order

-- lem:lex-order, proposition-valuedness
Lemma-5-7-prop-valued
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ )
   (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
 → is-prop-valued _<_
 → is-well-founded _<_
 → is-extensional _<_
 → ((x : X) → is-prop-valued (_≺_ {x}))
 → is-prop-valued (sum.order _<_ _≺_)
Lemma-5-7-prop-valued _<_ _≺_ = sum.prop-valued _<_ _≺_ fe

-- lem:lex-order, transitivity
Lemma-5-7-transitive
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ )
   (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
 → is-transitive _<_
 → ((x : X) → is-transitive (_≺_ {x}))
 → is-transitive (sum.order _<_ _≺_)
Lemma-5-7-transitive = sum.transitive

-- lem:lex-order, well-foundedness
Lemma-5-7-well-founded
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ )
   (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
 → is-well-founded _<_
 → ((x : X) → is-well-founded (_≺_ {x}))
 → is-well-founded (sum.order _<_ _≺_)
Lemma-5-7-well-founded = sum.well-founded

-- lem:lex-order, extensionality for a constant family
Lemma-5-7-extensional
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_<_ : X → X → 𝓦 ̇ ) (_≺_ : Y → Y → 𝓣 ̇ )
 → is-well-order _<_
 → is-well-order _≺_
 → is-well-order (times.order _<_ _≺_)
Lemma-5-7-extensional _<_ _≺_ = times.well-order _<_ _≺_ fe

-- def:ordinal-multiplication
Definition-5-8 : Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
Definition-5-8 = _×ₒ_

-- lem:sum-map (1), item:sum-map-equiv
Lemma-5-9-1 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
              (f : X → Y) (g : (x : X) → A x → B (f x))
            → is-vv-equiv f
            → ((x : X) → is-vv-equiv (g x))
            → is-vv-equiv (pair-fun {A = A} {B = B} f g)
Lemma-5-9-1 = pair-fun-is-vv-equiv

-- lem:sum-map (2), item:sum-map-embedding
Lemma-5-9-2 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
              (f : X → Y) (g : (x : X) → A x → B (f x))
            → is-embedding f
            → ((x : X) → is-embedding (g x))
            → is-embedding (pair-fun {A = A} {B = B} f g)
Lemma-5-9-2 = pair-fun-is-embedding

-- lem:sum-map (3), item:sum-map-dense
Lemma-5-9-3 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {Y : 𝓦 ̇ } {B : Y → 𝓣 ̇ }
              (f : X → Y) (g : (x : X) → A x → B (f x))
            → is-dense f
            → ((x : X) → is-dense (g x))
            → is-dense (pair-fun {A = A} {B = B} f g)
Lemma-5-9-3 = pair-fun-dense

-- lem:sum-map (4), item:sum-map-retraction
Lemma-5-9-4 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
            → ((x : X) → retract (A x) of (B x))
            → retract (Σ A) of (Σ B)
Lemma-5-9-4 = Σ-retract

-- lem:sum-map-order (1), item:sum-map-order-preserving
Lemma-5-10-1 : (τ υ : Ordᵀ) (A : ⟨ τ ⟩ → Ordᵀ) (B : ⟨ υ ⟩ → Ordᵀ)
               (f : ⟨ τ ⟩ → ⟨ υ ⟩)
               (g : (x : ⟨ τ ⟩) → ⟨ A x ⟩ → ⟨ B (f x) ⟩)
             → is-order-preserving τ υ f
             → ((x : ⟨ τ ⟩) → is-order-preserving (A x) (B (f x)) (g x))
             → is-order-preserving (∑ τ A) (∑ υ B) (pair-fun f g)
Lemma-5-10-1 = pair-fun-is-order-preserving

-- lem:sum-map-order (2), item:sum-map-order-reflecting
Lemma-5-10-2 : (τ υ : Ordᵀ) (A : ⟨ τ ⟩ → Ordᵀ) (B : ⟨ υ ⟩ → Ordᵀ)
               (f : ⟨ τ ⟩ → ⟨ υ ⟩)
               (g : (x : ⟨ τ ⟩) → ⟨ A x ⟩ → ⟨ B (f x) ⟩)
             → is-order-reflecting τ υ f
             → is-embedding f
             → ((x : ⟨ τ ⟩) → is-order-reflecting (A x) (B (f x)) (g x))
             → is-order-reflecting (∑ τ A) (∑ υ B) (pair-fun f g)
Lemma-5-10-2 = pair-fun-is-order-reflecting

-- rem:lex-not-extensional
Remark-5-11 : Extensionality-of-Ordinal-Indexed-Sums 𝓤₁ → EM 𝓤₀
Remark-5-11 = extensionality-of-ordinal-indexed-sums-gives-EM (pe 𝓤₀)

-- lem:trichotomous-sum
Lemma-5-12 : (τ : Ordinal₃ 𝓤) → (⟨ τ ⟩ → Ordinal₃ 𝓤) → Ordinal₃ 𝓤
Lemma-5-12 = ∑³

-- def:topped
Definition-5-13 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-5-13 = Ordinalᵀ

-- ex:NInf-ordinal
Example-5-14 : ℕ∞ → ℕ∞ → 𝓤₀ ̇
Example-5-14 = _≺ℕ∞_

Example-5-14-ordinal : Ordinal 𝓤₀
Example-5-14-ordinal = ℕ∞ₒ

Example-5-14-topped : Ordinalᵀ 𝓤₀
Example-5-14-topped = ℕ∞ᵒ

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
again topped is Lemma 5.15 below.

Labels: Lemma 5.15 = lem:topped-sum.

\begin{code}

-- lem:topped-sum
Lemma-5-15 : (τ : Ordinalᵀ 𝓤) → (⟨ τ ⟩ → Ordinalᵀ 𝓤) → Ordinalᵀ 𝓤
Lemma-5-15 = ∑

-- lem:extension-ordinals (1), item:ordinal-extension
Lemma-5-16-1 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
             → (X → Ordinal 𝓦)
             → (X ↪ A)
             → (A → Ordinal (𝓤 ⊔ 𝓥 ⊔ 𝓦))
Lemma-5-16-1 = _↗_

-- lem:extension-ordinals (2), item:extension-top
Lemma-5-16-2 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
             → (X → Ordinalᵀ 𝓦)
             → (X ↪ A)
             → (A → Ordinalᵀ (𝓤 ⊔ 𝓥 ⊔ 𝓦))
Lemma-5-16-2 = _↗ᵀ_

-- lem:extension-ordinals (3), item:extension-restricts
Lemma-5-16-3 : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
               (α : X → Ordinal 𝓦)
               (𝓮@(j , _) : X ↪ A)
               (x : X)
             → (α ↗ 𝓮) (j x) ≃ₒ α x
Lemma-5-16-3 = ↗-propertyₒ

-- lem:extension-ordinals (3), item:extension-restricts,
-- algebraic injectivity of the type of ordinals
Lemma-5-16-3-ainjective : is-univalent (𝓤 ⊔ 𝓥)
                        → ainjective-type (Ordinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Lemma-5-16-3-ainjective = Ordinal-is-ainjective

-- lem:extension-ordinals (3), item:extension-restricts,
-- and of the type of totally separated ordinals
Lemma-5-16-3-ainjective-TS : is-univalent (𝓤 ⊔ 𝓥)
                           → ainjective-type (TSOrdinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Lemma-5-16-3-ainjective-TS = TSOrdinal-is-ainjective fe

-- claim ordinals-are-ainjective
Prose-ordinals-are-ainjective : ainjective-type (Ordinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Prose-ordinals-are-ainjective {𝓤} {𝓥} = Ordinal-is-ainjective (ua (𝓤 ⊔ 𝓥))

Prose-ordinals-are-ainjective' : ainjective-type (TSOrdinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Prose-ordinals-are-ainjective' {𝓤} {𝓥} =
 TSOrdinal-is-ainjective fe (ua (𝓤 ⊔ 𝓥))

Prose-ordinals-are-ainjective'' : (α β : Ordinal 𝓤) → α ≃ₒ β → α ＝ β
Prose-ordinals-are-ainjective'' {𝓤} = eqtoidₒ (ua 𝓤) fe'

-- def:extended-and-successor-sum (1), item:extended-sum
Definition-5-17-1 : (ℕ → Ordᵀ) → Ordᵀ
Definition-5-17-1 = ∑¹

Definition-5-17-1-explicitly
 : (X : ℕ → 𝓤 ̇ )
 → Σ¹ X ＝ (Σ u ꞉ ℕ∞ , ((φ : is-finite u) → X (size φ)))
Definition-5-17-1-explicitly = Σ¹-explicitly

Definition-5-17-1-compact∙ : (X : ℕ → 𝓤 ̇ )
                           → ((n : ℕ) → is-compact∙ (X n))
                           → is-compact∙ (Σ¹ X)
Definition-5-17-1-compact∙ = Σ¹-compact∙

-- def:extended-and-successor-sum (2), item:successor-sum
Definition-5-17-2 : (ℕ → Ordᵀ) → Ordᵀ
Definition-5-17-2 = ∑₁

-- lem:successor-sum, the underlying type of the successor sum and its top
Lemma-5-18-shape : (X : ℕ → 𝓤 ̇ ) → Σ₁ X ≃ (Σ n ꞉ ℕ , X n) + 𝟙 {𝓤}
Lemma-5-18-shape = Σ₁-explicitly

Lemma-5-18-shape-top : (τ : ℕ → Ordᵀ) → Σ₁-base (top (∑₁ τ)) ＝ inr ⋆
Lemma-5-18-shape-top = ∑₁-top-is-over-inr

-- lem:successor-sum (1), item:successor-sum-is-successor
Lemma-5-18-1 : (τ : ℕ → Ordᵀ) → [ ∑₁ τ ] ≃ₒ (∑ₒ ω τ +ₒ 𝟙ₒ)
Lemma-5-18-1 = ∑₁-is-successorₒ

-- lem:successor-sum (2), item:successor-sum-retract
Lemma-5-18-2 : {X : ℕ → 𝓤 ̇ }
             → ((n : ℕ) → retract (X n) of ℕ)
             → retract (Σ₁ X) of ℕ
Lemma-5-18-2 = Σ₁-ℕ-retract

Lemma-5-18-2-discrete : (X : ℕ → 𝓤 ̇ )
                      → ((n : ℕ) → is-discrete (X n))
                      → is-discrete (Σ₁ X)
Lemma-5-18-2-discrete = Σ₁-is-discrete

-- def:sum-comparison
Definition-5-19 : (X : ℕ → 𝓤 ̇ ) → Σ₁ X → Σ¹ X
Definition-5-19 = Σ-up

Definition-5-19-ordinals : (τ : ℕ → Ordᵀ) → ⟨ ∑₁ τ ⟩ → ⟨ ∑¹ τ ⟩
Definition-5-19-ordinals = ∑-up

Definition-5-19-lc : left-cancellable ι𝟙
Definition-5-19-lc = ι𝟙-lc

-- lem:sum-comparison
Lemma-5-20-embedding : (X : ℕ → 𝓤 ̇ ) → is-embedding (Σ-up X)
Lemma-5-20-embedding = Σ-up-embedding

Lemma-5-20-dense : (X : ℕ → 𝓤 ̇ ) → is-dense (Σ-up X)
Lemma-5-20-dense = Σ-up-dense

Lemma-5-20-order-preserving
 : (τ : ℕ → Ordᵀ) → is-order-preserving (∑₁ τ) (∑¹ τ) (∑-up τ)
Lemma-5-20-order-preserving = ∑-up-is-order-preserving

Lemma-5-20-order-reflecting
 : (τ : ℕ → Ordᵀ) → is-order-reflecting (∑₁ τ) (∑¹ τ) (∑-up τ)
Lemma-5-20-order-reflecting = ∑-up-is-order-reflecting

-- thm:sup, the map σ
Theorem-5-21 : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤)
             → (Σ i ꞉ I , ⟨ α i ⟩) → Ordinal 𝓤
Theorem-5-21 = sum-to-ordinals

-- thm:sup (1), item:sup-is-ordinal
Theorem-5-21-1 : {I : 𝓤 ̇ } → (I → Ordinal 𝓤) → Ordinal 𝓤
Theorem-5-21-1 = sup

-- thm:sup (2), item:sup-surjection
Theorem-5-21-2 : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤)
               → is-surjection (sum-to-sup α)
Theorem-5-21-2 = sum-to-sup-is-surjection

-- thm:sup (3), item:sup-lub
Theorem-5-21-3 : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) (i : I) → α i ⊴ sup α
Theorem-5-21-3 = sup-is-upper-bound

Theorem-5-21-3' : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) (β : Ordinal 𝓤)
                → ((i : I) → α i ⊴ β)
                → sup α ⊴ β
Theorem-5-21-3' = sup-is-lower-bound-of-upper-bounds

Theorem-5-21-3'' : {I : 𝓤 ̇ } (α : I → Ordinal 𝓤) (i : I) (x : ⟨ α i ⟩)
                 → sup α ↓ [ α i , sup α ]⟨ sup-is-upper-bound α i ⟩ x
                 ＝ α i ↓ x
Theorem-5-21-3'' = initial-segment-of-sup-at-component

-- cor:sup-compact
Corollary-5-22 : {I : 𝓤 ̇ } {α : I → Ordinal 𝓤}
               → is-compact∙ I
               → ((i : I) → is-compact∙ ⟨ α i ⟩)
               → is-compact∙ ⟨ sup α ⟩
Corollary-5-22 = sup-is-compact∙ sr

-- thm:extended-sup-compact
Theorem-5-23 : {X K : 𝓤 ̇ } (𝓮@(j , _) : X ↪ K) (α : X → Ordinal 𝓤)
             → is-compact∙ K
             → ((x : X) → is-compact∙ ⟨ α x ⟩)
             → is-compact∙ ⟨ sup (α ↗ 𝓮) ⟩
Theorem-5-23 (j , j-is-embedding) α K-compact∙ α-compact∙ =
 sup-is-compact∙ sr K-compact∙
  (λ k → micro-tychonoff (fe _ _) (j-is-embedding k) (α-compact∙ ∘ pr₁))

-- def:extended-supremum
Definition-5-24 : (ℕ → Ordinal 𝓤₀) → Ordinal 𝓤₀
Definition-5-24 α = sup (α ↗ embedding-ℕ-to-ℕ∞ fe₀)


\end{code}

Section 6. Compact totally separated ordinals from Brouwer codes

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

-- prop:std-interp-failures (1), item:std-compact-lpo
Proposition-6-3-1 : ((b : B) → is-compact ⟨ ⟦ b ⟧-sup ⟩) → LPO
Proposition-6-3-1 = ⟦_⟧₀-compact-gives-LPO

-- prop:std-interp-failures (2), item:failure-trichotomy
Proposition-6-3-2 : ((b : B) → is-trichotomous ⟦ b ⟧-sup) → LPO
Proposition-6-3-2 = FTr.trichotomy-of-the-standard-interpretation-gives-LPO

-- def:non-standard-interpretations
Definition-6-4-Σ : B → Ordinal₃ 𝓤₀
Definition-6-4-Σ = ⟦_⟧-Σ

Definition-6-4-Σ¹ : B → Ordinalᵀ 𝓤₀
Definition-6-4-Σ¹ = ⟦_⟧-Σ¹

Definition-6-4-sup¹ : B → Ordinal 𝓤₀
Definition-6-4-sup¹ = ⟦_⟧-sup¹

-- thm:four-interp-props (1), item:trich-interp
Theorem-6-5-1 : (b : B) → is-trichotomous-order (underlying-order ⟦ b ⟧-Σ)
Theorem-6-5-1 b = 3is-trichotomous ⟦ b ⟧-Σ

-- thm:four-interp-props (2), item:compactsep-interp
Theorem-6-5-2 : (b : B) → is-compact∙ ⟨ ⟦ b ⟧-Σ¹ ⟩
Theorem-6-5-2 = ⟦_⟧₁-is-compact∙

Theorem-6-5-2' : (b : B) → is-totally-separated ⟨ ⟦ b ⟧-Σ¹ ⟩
Theorem-6-5-2' = ⟦_⟧₁-is-totally-separated

-- thm:four-interp-props (3), item:kappa-retract-cantor
Theorem-6-5-3 : (b : B) → retract ⟨ ⟦ b ⟧-Σ' ⟩ of (ℕ → 𝟚)
Theorem-6-5-3 = BDC.Κ-Cantor-retract

-- thm:four-interp-props (4), item:compact-interp
Theorem-6-5-4 : (b : B) → is-compact∙ ⟨ ⟦ b ⟧-sup¹ ⟩
Theorem-6-5-4 = ⟦_⟧₂-is-compact∙

-- prop:trich-compact-lpo
Proposition-6-6 : ((b : B) → is-compact ⟨ ⟦ b ⟧-Σ ⟩) → LPO
Proposition-6-6 = ⟦_⟧₃-compact-gives-LPO

-- prop:failure-tot-sep
Proposition-6-7 : ((b : B) → is-totally-separated ⟨ ⟦ b ⟧-sup¹ ⟩) → ¬¬ WLPO
Proposition-6-7
 = FTS.total-separatedness-of-the-sup-of-extension-interpretation-gives-¬¬WLPO


\end{code}

Examples 3.12(1) has no entry. That total separatedness is not closed
under sums is the example of Examples 3.10(2), whose index type and
fibers are totally separated by the two entries following
Examples-3-10-2 above.

Labels: Examples 3.12(1) = ex:tot-sep(item:ts-not-sigma),
Examples 3.10(2) = ex:tot-sep-failures(item:two-infinities-not-tot-sep).

\begin{code}

-- thm:comparisons
Theorem-6-8-₀₃ : Excluded-Middle → (b : B) → ⟦ b ⟧-sup ⊴ [ ⟦ b ⟧-Σ ]
Theorem-6-8-₀₃ = comparison₀₃

Theorem-6-8-₀₂ : EM 𝓤₁ → (b : B) → ⟦ b ⟧-sup ⊴ ⟦ b ⟧-sup¹
Theorem-6-8-₀₂ = comparison₀₂

Theorem-6-8-₂₁ : Excluded-Middle → (b : B) → ⟦ b ⟧-sup¹ ⊴ [ ⟦ b ⟧-Σ¹ ]
Theorem-6-8-₂₁ = comparison₂₁

Theorem-6-8-₃₁ : EM 𝓤₀ → (b : B) → [ ⟦ b ⟧-Σ ] ⊴ [ ⟦ b ⟧-Σ¹ ]
Theorem-6-8-₃₁ = comparison₃₁

-- prop:comparisons-taboos (1), item:comparison03-gives-lpo
Proposition-6-9-1 : ((b : B) → ⟦ b ⟧-sup ⊴ [ ⟦ b ⟧-Σ ]) → LPO
Proposition-6-9-1 = FTr.comparison₀₃-gives-LPO

-- prop:comparisons-taboos (2), item:comparison21-gives-notnot-wlpo
Proposition-6-9-2 : ((b : B) → ⟦ b ⟧-sup¹ ⊴ [ ⟦ b ⟧-Σ¹ ]) → ¬¬ WLPO
Proposition-6-9-2 = FTS.comparison₂₁-gives-¬¬WLPO

-- def:delta-kappa
Definition-6-10 : B → Ordᵀ
Definition-6-10 = ⟦_⟧-Σ₁

-- thm:delta-kappa-props (1), item:delta-trichotomous
Theorem-6-11-1 : (b : B) → is-trichotomous [ ⟦ b ⟧-Σ₁ ]
Theorem-6-11-1 = BDC.Δ-is-trichotomous

-- thm:delta-kappa-props (2), item:delta-retract-N
Theorem-6-11-2 : (b : B) → retract ⟨ ⟦ b ⟧-Σ₁ ⟩ of ℕ
Theorem-6-11-2 = BDC.Δ-retract-of-ℕ

Theorem-6-11-2' : (b : B) → is-discrete ⟨ ⟦ b ⟧-Σ₁ ⟩
Theorem-6-11-2' = BDC.Δ-is-discrete

-- prop:delta-kappa-fail (1), item:delta-compact-lpo
Proposition-6-12-1 : ((b : B) → is-compact ⟨ ⟦ b ⟧-Σ₁ ⟩) ↔ LPO
Proposition-6-12-1 = BDC.Δ-compact-iff-LPO

-- prop:delta-kappa-fail (2), item:kappa-discrete-wlpo
Proposition-6-12-2 : ((b : B) → is-discrete ⟨ ⟦ b ⟧-Σ' ⟩) → WLPO
Proposition-6-12-2 = BDC.Κ-discrete-gives-WLPO

-- def:iota
Definition-6-13 : {b : B} → ⟨ ⟦ b ⟧-Σ₁ ⟩ → ⟨ ⟦ b ⟧-Σ' ⟩
Definition-6-13 {b} = BDC.ι {b}

Definition-6-13-limit-case : (X : ℕ → 𝓤 ̇ ) (Y : ℕ → 𝓤 ̇ )
                           → ((n : ℕ) → X n → Y n)
                           → Σ₁ X → Σ¹ Y
Definition-6-13-limit-case = Σ↑

-- thm:iota, an embedding
Theorem-6-14 : (b : B) → is-embedding (BDC.ι {b})
Theorem-6-14 = BDC.ι-is-embedding

-- thm:iota, dense
Theorem-6-14' : (b : B) → is-dense (BDC.ι {b})
Theorem-6-14' = BDC.ι-is-dense

-- thm:iota, order-preserving
Theorem-6-14'' : (b : B) (x y : ⟨ ⟦ b ⟧-Σ₁ ⟩)
               → x ≺⟨ [ ⟦ b ⟧-Σ₁ ] ⟩ y
               → BDC.ι {b} x ≺⟨ [ ⟦ b ⟧-Σ' ] ⟩ BDC.ι {b} y
Theorem-6-14'' = BDC.ι-is-order-preserving

-- thm:iota, order-reflecting
Theorem-6-14''' : (b : B) (x y : ⟨ ⟦ b ⟧-Σ₁ ⟩)
                → BDC.ι {b} x ≺⟨ [ ⟦ b ⟧-Σ' ] ⟩ BDC.ι {b} y
                → x ≺⟨ [ ⟦ b ⟧-Σ₁ ] ⟩ y
Theorem-6-14''' = BDC.ι-is-order-reflecting

-- ex:omega-plus-one
Example-6-15 : [ ∑₁ (λ _ → 𝟙ᵒ) ] ≃ₒ [ succₒ ω ]
Example-6-15 = ∑₁-of-𝟙ᵒ

Example-6-15' : [ ∑¹ (λ _ → 𝟙ᵒ) ] ≃ₒ [ ℕ∞ᵒ ]
Example-6-15' = ∑¹-of-𝟙ᵒ

Example-6-15'' : (τ : ℕ → Ordᵀ) → is-isolated (top (∑₁ τ))
Example-6-15'' = ∑₁-top-is-isolated

-- prop:brouwer-iota-equiv-LPO
Proposition-6-16 : ((b : B) → is-equiv (BDC.ι {b})) ↔ LPO
Proposition-6-16 = BDC.ι-is-equiv-iff-LPO

-- def:has-inf
Definition-6-17 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Definition-6-17 = has-inf

-- def:has-inf (1), item:conditional-root
Definition-6-17-1 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → 𝟚) → X → 𝓤 ̇
Definition-6-17-1 _≤_ = is-conditional-root _≤_

-- def:has-inf (2), item:roots-infimum
Definition-6-17-2 : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → (X → 𝟚) → X → 𝓤 ⊔ 𝓥 ̇
Definition-6-17-2 = is-roots-infimum

Definition-6-17-topped : Ordinalᵀ 𝓤 → 𝓤 ̇
Definition-6-17-topped = has-infs-of-complemented-subsets

-- lem:least-element
Lemma-6-18 : {X : 𝓤 ̇ } (_≤_ : X → X → 𝓥 ̇ )
           → has-inf _≤_
           → (p : X → 𝟚)
           → ¬¬ (Σ x ꞉ X , p x ＝ ₀)
           → Σ x₀ ꞉ X , is-least-root _≤_ p x₀
Lemma-6-18 = has-inf-gives-least-root

-- thm:micro-inf-tychonoff
Theorem-6-19 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
             → is-prop X
             → (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
             → ((x : X) → has-inf (λ (y y' : Y x) → ¬ (y' ≺ y)))
             → has-inf (λ (φ γ : Π Y) → ¬ (Σ x ꞉ X , γ x ≺ φ x))
Theorem-6-19 = micro-inf-tychonoff

-- thm:kappa-infs
Theorem-6-20 : propext 𝓤₀
             → (b : B) → has-infs-of-complemented-subsets (⟦ b ⟧-Σ')
Theorem-6-20 = BDC.Κ-has-infs-of-complemented-subsets

-- cor:kappa-least
Corollary-6-21 : propext 𝓤₀
               → (b : B) (p : ⟨ ⟦ b ⟧-Σ' ⟩ → 𝟚)
               → ¬¬ (Σ x ꞉ ⟨ ⟦ b ⟧-Σ' ⟩ , p x ＝ ₀)
               → Σ x₀ ꞉ ⟨ ⟦ b ⟧-Σ' ⟩ , is-least-root
                                       (underlying-weak-order (⟦ b ⟧-Σ')) p x₀
Corollary-6-21 = BDC.Κ-has-least-roots-of-complemented-subsets

-- prop:delta-least-lpo
Proposition-6-22 : propext 𝓤₀
                 → (((b : B) (p : ⟨ ⟦ b ⟧-Σ₁ ⟩ → 𝟚)
                      → ¬¬ (Σ x ꞉ ⟨ ⟦ b ⟧-Σ₁ ⟩ , p x ＝ ₀)
                      → Σ x₀ ꞉ ⟨ ⟦ b ⟧-Σ₁ ⟩ ,
                         is-least-root (underlying-weak-order (⟦ b ⟧-Σ₁)) p x₀)
                    ↔ LPO)
Proposition-6-22 = BDC.Δ-least-roots-iff-LPO


\end{code}

Section 7. An inductive-recursive universe of compact ordinals

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

-- prop:E-delta-lpo
Proposition-7-3 : ((ν : IRC.E) → is-compact ⟨ IRC.Δ ν ⟩) ↔ LPO
Proposition-7-3 = IRC.Δ-compact-iff-LPO

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

-- thm:E-props, the dagger (†) step
Theorem-7-5-1-extension
 : propext 𝓤₀
 → (ν : IRC.E) (A : ⟨ IRC.Δ ν ⟩ → IRC.E) (y : ⟨ IRC.Κ ν ⟩)
 → has-infs-of-complemented-subsets (IRC.𝓚 ν A y)
Theorem-7-5-1-extension = IRC.𝓚-has-infs-of-complemented-subsets

-- thm:E-props (1), item:E-comp-infima
Theorem-7-5-1 : propext 𝓤₀
              → (ν : IRC.E) → has-infs-of-complemented-subsets (IRC.Κ ν)
Theorem-7-5-1 = IRC.K-has-infs-of-complemented-subsets

Theorem-7-5-1-compact : (ν : IRC.E) → is-Compact ⟨ IRC.Κ ν ⟩ {𝓥}
Theorem-7-5-1-compact = IRC.Κ-Compact

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

-- prop:E-iota-equiv-discrete (3), item:E-kappa-discrete-wlpo
Proposition-7-7-3 : ((ν : IRC.E) → is-discrete ⟨ IRC.Κ ν ⟩) → WLPO
Proposition-7-7-3 = IRC.Κ-discrete-gives-WLPO

-- prop:E-delta-least-lpo
Proposition-7-8 : propext 𝓤₀
                → (((ν : IRC.E) (p : ⟨ IRC.Δ ν ⟩ → 𝟚)
                     → ¬¬ (Σ x ꞉ ⟨ IRC.Δ ν ⟩ , p x ＝ ₀)
                     → Σ x₀ ꞉ ⟨ IRC.Δ ν ⟩ ,
                          is-least-root (underlying-weak-order (IRC.Δ ν)) p x₀)
                   ↔ LPO)
Proposition-7-8 = IRC.Δ-least-roots-iff-LPO

-- prop:E-delta-below-kappa (1), item:iota1-simulation
Proposition-7-9-1 : [ IRC.Δ IRC.⌜ω+𝟙⌝ ] ⊴ [ IRC.Κ IRC.⌜ω+𝟙⌝ ]
Proposition-7-9-1 = ω+𝟙-is-⊴-ℕ∞

-- prop:E-delta-below-kappa (2), item:E-delta-below-kappa-lpo
Proposition-7-9-2 : ((ν : IRC.E) → [ IRC.Δ ν ] ⊴ [ IRC.Κ ν ]) ↔ LPO
Proposition-7-9-2 = IRC.Δ-⊴-Κ-iff-LPO ua

-- prop:E-delta-below-kappa (2), the code of the forward implication
Proposition-7-9-2-code : IRC.E
Proposition-7-9-2-code = IRC.⌜ω+𝟚⌝ ua

Proposition-7-9-2-instance
 : [ IRC.Δ (IRC.⌜ω+𝟚⌝ ua) ] ⊴ [ IRC.Κ (IRC.⌜ω+𝟚⌝ ua) ] → LPO
Proposition-7-9-2-instance = IRC.Δ-⊴-Κ-gives-LPO ua

-- def:brouwer-to-E
Definition-7-10 : B → IRC.E
Definition-7-10 = BtoE.B-to-E

-- thm:brouwer-to-E (1), item:E-is-set
Theorem-7-11-1 : is-set IRC.E
Theorem-7-11-1 = IRC.E-is-set

-- thm:brouwer-to-E (2), item:bemb-embedding
Theorem-7-11-2 : is-embedding BtoE.B-to-E
Theorem-7-11-2 = BtoE.B-to-E-is-embedding

-- thm:brouwer-to-E (3), item:bemb-discrete
Theorem-7-11-3 : (b : B) → [ ⟦ b ⟧-Σ₁ ] ≃ₒ [ IRC.Δ (BtoE.B-to-E b) ]
Theorem-7-11-3 = BtoE.Δ-agreement

-- thm:brouwer-to-E (4), item:bemb-compact
Theorem-7-11-4 : (b : B) → [ ⟦ b ⟧-Σ' ] ≃ₒ [ IRC.Κ (BtoE.B-to-E b) ]
Theorem-7-11-4 = BtoE.Κ-agreement

-- prop:kappa-not-tot-sep
Proposition-7-12 : ((ν : IRC.E) → is-totally-separated ⟨ IRC.Κ ν ⟩) → ¬¬ WLPO
Proposition-7-12 = IRC.Κ-totally-separated-gives-¬¬WLPO

-- prop:kappa-not-tot-sep, the witnessing code
Proposition-7-12-code : IRC.E
Proposition-7-12-code = IRC.⌜ℕ∞₂⌝

Proposition-7-12-instance
 : is-totally-separated ⟨ IRC.Κ IRC.⌜ℕ∞₂⌝ ⟩ → ¬¬ WLPO
Proposition-7-12-instance = IRC.Κ⌜ℕ∞₂⌝-totally-separated-gives-¬¬WLPO


\end{code}
