Tom de Jong and Martin Escardo
January 2026

This file follows the definitions, equations, lemmas, propositions, theorems and
remarks of our paper

   Tom de Jong and Martín Hötzel Escardó
   Examples and counterexamples of injective types
   January 2026
   https://arxiv.org/abs/TODO

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-} -- --lossy-unification (TODO)

\end{code}

Our global assumptions are univalence and the existence of propositional
truncations.

Function extensionality and propositional extensionality can be derived from
univalence.

\begin{code}

open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.ExamplesCounterExamplesArticle
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import Notation.General

open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.NotNotStablePropositions
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.SIP-Examples
open import UF.Size
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open import InjectiveTypes.Blackboard fe hiding (extension)
open import InjectiveTypes.CharacterizationViaLifting fe
open import InjectiveTypes.NonEmptyTypes pt ua
open import InjectiveTypes.OverSmallMaps fe
open import InjectiveTypes.PointedDcpos fe pt

open import Iterative.Multisets
open import Iterative.Multisets-Addendum ua
open import Iterative.Sets ua
open import Iterative.Sets-Addendum ua

open import Ordinals.Injectivity
open import Ordinals.Type

open import Quotient.Type

open import Various.DedekindNonAxiomatic pt fe' pe' using (𝓡∞)

\end{code}

Section 2. Preliminaries

\begin{code}

Definition-2-1 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-1 𝓤 = is-small (Ω¬¬ 𝓤)

Lemma-2-2 : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : (x : X) → A x → 𝓦 ̇ )
            (x y : X) (a : A x) (b : B x a) (p : x ＝ y)
          → transport (λ - → Sigma (A -) (B -)) p (a , b)
            ＝ transport A p a , transportd A B a p b
Lemma-2-2 A B x y a b p = transport-Σ A B y p a {b}

module Lemma-2-3
        {X : 𝓤 ̇ } (a : X) {Y : X → 𝓥 ̇ } (i : is-prop X)
       where

 Lemma-2-3-i : Π Y ≃ Y a
 Lemma-2-3-i = prop-indexed-product a fe' i

 Lemma-2-3-i₁ : ⌜ Lemma-2-3-i ⌝ ＝ (λ f → f a)
 Lemma-2-3-i₁ = refl

 Lemma-2-3-i₂ : ⌜ Lemma-2-3-i ⌝⁻¹ ＝ (λ y x → transport Y (i a x) y)
 Lemma-2-3-i₂ = refl

 Lemma-2-3-ii : Y a ≃ Σ Y
 Lemma-2-3-ii = ≃-sym (prop-indexed-sum a i)

 Lemma-2-3-ii₁ : ⌜ Lemma-2-3-ii ⌝ ＝ (λ y → (a , y))
 Lemma-2-3-ii₁ = refl

 Lemma-2-3-ii₂ : ⌜ Lemma-2-3-ii ⌝⁻¹ ＝ (λ (x , y) → transport Y (i x a) y)
 Lemma-2-3-ii₂ = refl

\end{code}

Section 3. Flabbiness and injectivity

\begin{code}

Definition-3-1 : (D : 𝓦 ̇ ) (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ⊔ 𝓦 ̇
Definition-3-1 = ainjective-type

Definition-3-2 : (D : 𝓦 ̇ ) (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓦 ̇
Definition-3-2 = aflabby

Lemma-3-3-i : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → aflabby D 𝓤
Lemma-3-3-i = ainjective-types-are-aflabby

Lemma-3-3-ii : (D : 𝓦 ̇ ) → aflabby D (𝓤 ⊔ 𝓥) → ainjective-type D 𝓤 𝓥
Lemma-3-3-ii = aflabby-types-are-ainjective

Lemma-3-4 : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥
          → (D' : 𝓦 ̇ ) → retract D' of D → ainjective-type D' 𝓤 𝓥
Lemma-3-4 D ainj D' = retract-of-ainjective D' D ainj

Lemma-3-5 : (D : 𝓦 ̇ ) → aflabby D 𝓣
          → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (j : X → Y)
          → is-embedding j
          → j is 𝓣 small-map
          → (f : X → D)
          → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f
Lemma-3-5 D aflab X Y = aflabbiness-gives-injectivity-over-small-maps D aflab

Lemma-3-6 : {𝓦 𝓤 𝓥 𝓣₀ 𝓣₁ 𝓣₂ : Universe}
          → (D : 𝓦 ̇ ) → ainjective-type D (𝓣₀ ⊔ 𝓣₁) 𝓣₂
          → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (j : X → Y)
          → is-embedding j
          → j is 𝓣₀ small-map
          → (f : X → D)
          → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f
Lemma-3-6 {𝓦} {𝓤} {𝓥} {𝓣₀} {𝓣₁} {𝓣₂} D ainj X Y j =
 ainjectivity-over-small-maps 𝓣₁ D ainj j

module Lemma-3-7
        {𝓤 𝓥 𝓣₀ 𝓣₁ 𝓣₂ : Universe}
        (D : 𝓤 ̇ ) (ainj : ainjective-type D (𝓣₀ ⊔ 𝓣₁) 𝓣₂)
        (Y : 𝓥 ̇ ) (j : D → Y)
        (j-emb : is-embedding j)
        (j-small : j is 𝓣₀ small-map)
       where

 Lemma-3-7-i : retract D of Y
 Lemma-3-7-i = embedding-retract' 𝓣₁ D Y j j-emb j-small ainj

 Lemma-3-7-ii : section Lemma-3-7-i ＝ j
 Lemma-3-7-ii = refl

module Algebras-of-the-lifting-monad
        (𝓣 : Universe)
       where

 open ainjectivity-of-Lifting 𝓣
 open ainjectivity-of-Lifting' 𝓣 (ua 𝓣)

 Lemma-3-8 : (X : 𝓤 ̇ ) → (η ∶ (X → 𝓛 X)) is 𝓣 small-map
 Lemma-3-8 X = η-is-small-map

 Lemma-3-9 : (D : 𝓤 ̇ ) → ainjective-type D (𝓥 ⊔ 𝓣) 𝓦
           → retract D of 𝓛 D
 Lemma-3-9 {𝓤} {𝓥} = ainjective-is-retract-of-free-𝓛-algebra' 𝓥

 Theorem-3-10 : (D : 𝓤 ̇ )
              → ainjective-type D 𝓣 𝓣 ↔ (Σ X ꞉ 𝓤 ̇  , retract D of 𝓛 X)
 Theorem-3-10 = ainjectives-in-terms-of-free-𝓛-algebras'

 Theorem-3-11
  : (D : 𝓤 ̇ )
  → ainjective-type D 𝓣 𝓣 ↔ (Σ A ꞉ 𝓣 ⁺ ⊔ 𝓤 ̇  , 𝓛-alg A × (retract D of A))
 Theorem-3-11 = ainjectives-in-terms-of-𝓛-algebras

\end{code}

Section 4. Examples

\begin{code}

Examples-1-i : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
Examples-1-i {𝓤} = universes-are-ainjective-Σ (ua 𝓤)

Examples-1-ii : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
Examples-1-ii {𝓤} = universes-are-ainjective-Π (ua 𝓤)

Examples-2 : ainjective-type (Ω 𝓤) 𝓤 𝓤
Examples-2 {𝓤} = Ω-ainjective pe'

\end{code}

Examples (3)—(5) can be found below and are postponed for now (as in the paper).

\begin{code}

Examples-6-i : set-quotients-exist → ainjective-type (Ordinal 𝓤) 𝓤 𝓤
Examples-6-i {𝓤} sqe =
 pointed-dcpos-are-ainjective-types 𝓤 (Ord-DCPO , 𝟘ₒ , 𝟘ₒ-least-⊴)
  where
   open import DomainTheory.Basics.Dcpo pt fe' 𝓤
   open import Ordinals.AdditionProperties ua
   open import Ordinals.Arithmetic fe
   open import Ordinals.Equivalence
   open import Ordinals.OrdinalOfOrdinals ua
   open import Ordinals.OrdinalOfOrdinalsSuprema ua
   open import Quotient.GivesSetReplacement

   sr : Set-Replacement pt
   sr = set-replacement-from-set-quotients-and-prop-trunc sqe pt

   Ord-DCPO : DCPO {𝓤 ⁺} {𝓤}
   Ord-DCPO = (Ordinal 𝓤 , _⊴_ ,
               (the-type-of-ordinals-is-a-set (ua 𝓤) fe' ,
                ⊴-is-prop-valued , ⊴-refl , ⊴-trans , ⊴-antisym) ,
               (λ I α _ → ordinal-of-ordinals-has-small-suprema' pt sr I α))
    where
     open suprema pt sr

Examples-6-ii : ainjective-type (Ordinal 𝓤) 𝓤 𝓤
Examples-6-ii {𝓤} = Ordinal-is-ainjective (ua 𝓤)
 where
  open ordinals-injectivity fe

Proposition-4-1 : let NE = (Σ X ꞉ 𝓤 ̇  , ¬¬ X) in
                  (retract NE of (𝓤 ̇ )) × ainjective-type NE 𝓤 𝓤
Proposition-4-1 {𝓤} = Non-Empty-retract 𝓤 , Non-Empty-is-injective 𝓤

Lemma-4-2 : (P : 𝓣 ̇ ) (X : P → 𝓤 ̇ ) → is-prop P
          → (Π p ꞉ P , ¬¬ X p) → ¬¬ Π X
Lemma-4-2 P X i φ ν = ν III
 where
  I : (p : P) → ¬ X p
  I p x = ν (λ p' → transport X (i p p') x)
  II : ¬ P
  II p = φ p (I p)
  III : (p : P) → X p
  III p = 𝟘-elim (II p)

Proposition-4-1-alt : ainjective-type (Σ X ꞉ 𝓤 ̇  , ¬¬ X) 𝓤 𝓤
Proposition-4-1-alt =
 ainjectivity-of-type-of-structures (¬¬_) (Π-closure-criterion ¬¬_ T T-refl c)
  where
   open import InjectiveTypes.MathematicalStructures ua
   T : {X Y : 𝓤 ̇ } → (X ≃ Y) → ¬¬ X → ¬¬ Y
   T 𝕗 = ¬¬-functor ⌜ 𝕗 ⌝
   T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
   T-refl x = refl
   c : closed-under-prop-Π' ¬¬_ T T-refl
   c (P , i) X = m-is-equiv
    where
     m : ¬¬ Π X → Π p ꞉ P , ¬¬ X p
     m h p = T (prop-indexed-product p fe' i) h
     m-is-equiv : is-equiv m
     m-is-equiv = qinvs-are-equivs m
                   (Lemma-4-2 P X i ,
                    (λ _ → negations-are-props fe' _ _) ,
                    (λ _ → Π-is-prop fe' (λ p → negations-are-props fe') _ _))

module Carriers-of-pointed-dcpos
        (𝓥 : Universe)
       where

 open import DomainTheory.Basics.Pointed pt fe' 𝓥

 Proposition-4-3 : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → ainjective-type ⟪ 𝓓 ⟫ 𝓥 𝓥
 Proposition-4-3 = pointed-dcpos-are-ainjective-types 𝓥

Example-4-4 : ainjective-type 𝓡∞ 𝓤₀ 𝓤₀
Example-4-4 = pointed-dcpos-are-ainjective-types 𝓤₀ 𝓡∞-DCPO⊥
 where
  open import DomainTheory.Examples.ExtendedPartialDedekindReals pt fe' pe'

Theorem-4-5 : aflabby (𝕄 𝓤) 𝓤
Theorem-4-5 {𝓤} = 𝕄-is-aflabby-Σ 𝓤

Corollary-4-6 : ainjective-type (𝕄 𝓤) 𝓤 𝓤
Corollary-4-6 {𝓤} = 𝕄-is-ainjective-Σ 𝓤

Theorem-4-7 : set-quotients-exist → ainjective-type (𝕍 𝓤) 𝓤 𝓤
Theorem-4-7 {𝓤} sqe = 𝕍-is-ainjective 𝓤 pt sr
 where
  open import Quotient.GivesSetReplacement
  sr : Set-Replacement pt
  sr = set-replacement-from-set-quotients-and-prop-trunc sqe pt

module Types-of-mathematical-structures-1
        (S : 𝓤 ̇  → 𝓥 ̇ )
       where

 open import InjectiveTypes.MathematicalStructures ua

 Definition-4-8 : 𝓤 ⁺ ⊔ 𝓥 ̇
 Definition-4-8 = closed-under-prop-Π S

 Lemma-4-9 : closed-under-prop-Π S → aflabby (Σ S) 𝓤
 Lemma-4-9 = aflabbiness-of-type-of-structured-types S

 module Lemma-4-10
         (T : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y)
         (r : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id)
        where

  open canonical-map' S T r

  Lemma-4-10-i : {X Y : 𝓤 ̇ } (h : X ≃ Y)
               → T h ∼ treq S h
  Lemma-4-10-i = transport-eqtoid S T r

  Lemma-4-10-ii
   : (P : Ω 𝓤) (A : P holds → 𝓤 ̇ ) (s : S (Π A)) (p : P holds)
   → ρ P A s p ＝ T (π P A p) s
  Lemma-4-10-ii P A s p = happly (ρ-and-τ-agree P A s) p

module Types-of-mathematical-structures-2
       where

 open import InjectiveTypes.MathematicalStructures ua

 Lemma-4-11 : {𝓤 𝓥₁ 𝓥₂ : Universe} (S₁ : 𝓤 ̇ → 𝓥₁ ̇ ) (S₂ : 𝓤 ̇  → 𝓥₂ ̇ )
            → closed-under-prop-Π S₁
            → closed-under-prop-Π S₂
            → closed-under-prop-Π (λ X → S₁ X × S₂ X)
 Lemma-4-11 S₁ S₂ = closure-under-prop-Π-×

 Lemma-4-12 : (S : 𝓤 ̇ → 𝓥 ̇) (S-closed : closed-under-prop-Π S)
              (𝔞 : (X : 𝓤 ̇) → S X → Ω 𝓦)
            → ((P : Ω 𝓤) (A : P holds → 𝓤 ̇)
               → (α : (p : P holds) → S (A p))
               → ((p : P holds) → 𝔞 (A p) (α p) holds)
               → 𝔞 (Π A) (inverse (canonical-map.ρ S P A) (S-closed P A) α) holds)
            → closed-under-prop-Π (λ X → Σ s ꞉ S X , 𝔞 X s holds)
 Lemma-4-12 S S-closed 𝔞 =
  closure-under-prop-Π-with-axioms S S-closed
   (λ X s → 𝔞 X s holds) (λ X s → holds-is-prop (𝔞 X s))

module Examples-4-13-a where
 open import InjectiveTypes.MathematicalStructures ua

 [1] : ainjective-type (Pointed-type 𝓤) 𝓤 𝓤
 [1] = ainjectivity-of-type-of-pointed-types

 [2] : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
 [2] = ainjectivity-of-∞-Magma

 [3] : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
 [3] = ainjectivity-of-∞-Magma

 [4] : ainjective-type (monoid.Monoid {𝓤}) 𝓤 𝓤
 [4] = ainjectivity-of-Monoid

 [5] : ainjective-type (group.Group {𝓤}) 𝓤 𝓤
 [5] = {!!} -- TODO or not?

module Examples-4-13-b where
 open import InjectiveTypes.MathematicalStructuresMoreGeneral ua

 [6] : ainjective-type (Graph 𝓤) 𝓤 𝓤
 [6] = ainjectivity-of-Graph

 [7] : ainjective-type (Poset 𝓤) 𝓤 𝓤
 [7] = ainjectivity-of-Poset

 [8] : ainjective-type (Fam 𝓤) 𝓤 𝓤
 [8] = ainjectivity-of-Fam

 [9] : ainjective-type (Σ X ꞉ 𝓤 ̇  , Σ Y ꞉ 𝓤 ̇  , (X → Y)) 𝓤 𝓤
 [9] = ainjectivity-of-type-of-all-functions

module Σ-types
        (X : 𝓤 ̇ )
        (A : X → 𝓥 ̇ )
        (ϕ : aflabby X 𝓦)
        where
 open import InjectiveTypes.Sigma fe

 Definition-4-14 : (P : Ω 𝓦) (f : P holds → X)
                 → A (extension ϕ P f) → Π p ꞉ P holds , A (f p)
 Definition-4-14 = ρ A ϕ

 Theorem-4-15 : compatibility-data A ϕ → aflabby (Σ A) 𝓦
 Theorem-4-15 = Σ-is-aflabby A ϕ

\end{code}

Section 4.7. Models of generalized algebraic theories is not formalized.
This concludes Section 4.

Section 5. Weak excluded middle and De Morgan's Law

\begin{code}

-- TODO

\end{code}

Section 6. A Rice-like theorem for injective types

\begin{code}

-- TODO

\end{code}

Section 7. Counterexamples

\begin{code}

-- TODO

\end{code}