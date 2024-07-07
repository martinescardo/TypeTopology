Tom de Jong, July 2024.

This file corresponds to the paper

   "Domain Theory in Univalent Foundations II:
    Continuous and algebraic domains"
   Tom de Jong and Martín Hötzel Escardó
   2024
   https://arxiv.org/abs/TODO

See DomainTheory.index.lagda for an overview of all domain theory in
TypeTopology.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

\end{code}

Our global assumptions are function extensionality, propositional extensionality
and the existence of propositional truncations.

\begin{code}

module DomainTheory.Part-II
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.List
open import MLTT.Spartan

{-
open import Naturals.Order hiding (subtraction')
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order hiding (_⊑_ ; _≼_)

open import UF.Base
open import UF.Hedberg
open import UF.Powerset-MultiUniverse
open import UF.Subsingletons-FunExt

-}

open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt
open import UF.Powerset-Fin pt hiding (⟨_⟩)
open import UF.Powerset-MultiUniverse renaming (𝓟 to 𝓟-general)
open import UF.Powerset
open import UF.Sets
open import UF.Size hiding (is-locally-small ; is-small)
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier renaming (⊥ to 𝟘Ω ; ⊤ to 𝟙Ω)
open import UF.Univalence
open import UF.UA-FunExt

open import OrderedTypes.Poset fe
open PosetAxioms
open binary-unions-of-subsets pt

\end{code}

Section 2

\begin{code}

module _ (𝓥 : Universe) where

 open import DomainTheory.Basics.Dcpo pt fe 𝓥
 open import DomainTheory.Basics.Pointed pt fe 𝓥
 open import DomainTheory.Basics.WayBelow pt fe 𝓥

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  Definition-2-1 : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-2-1 x y = x ≪⟨ 𝓓 ⟩ y

  Lemma-2-2 : ({x y : ⟨ 𝓓 ⟩} → is-prop (x ≪⟨ 𝓓 ⟩ y))
            × ({x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y)
            × ({x y v w : ⟨ 𝓓 ⟩} → x ⊑⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ w → x ≪⟨ 𝓓 ⟩ w)
            × is-antisymmetric (way-below 𝓓)
            × is-transitive (way-below 𝓓)
  Lemma-2-2 = ≪-is-prop-valued 𝓓 ,
              ≪-to-⊑ 𝓓 ,
              ⊑-≪-to-≪ 𝓓 ,
              (λ x y → ≪-is-antisymmetric 𝓓) ,
              (λ x y z → ≪-is-transitive 𝓓)

  Definition-2-3 : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-2-3 x = is-compact 𝓓 x

 Example-2-4 : (𝓓 : DCPO⊥ {𝓤} {𝓣}) → is-compact (𝓓 ⁻) (⊥ 𝓓)
 Example-2-4 𝓓 = ⊥-is-compact 𝓓

 module _ where
  open import DomainTheory.Examples.Omega pt fe pe 𝓥 hiding (κ)
  Example-2-5 : (P : Ω 𝓥)
              → (is-compact Ω-DCPO P ↔ (P ＝ 𝟘Ω) + (P ＝ 𝟙Ω))
              × (is-compact Ω-DCPO P ↔ is-decidable (P holds))
  Example-2-5 P = compact-iff-empty-or-unit P ,
                  compact-iff-decidable P

  open import Lifting.Construction 𝓥 renaming (⊥ to ⊥𝓛)
  open import DomainTheory.Lifting.LiftingSet pt fe 𝓥 pe
  open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓥 hiding (κ)
  Example-2-6 : {X : 𝓥 ̇  } (X-set : is-set X) (l : 𝓛 X)
              → (is-compact (𝓛-DCPO X-set) l ↔ (l ＝ ⊥𝓛) + (Σ x ꞉ X , η x ＝ l))
              × (is-compact (𝓛-DCPO X-set) l ↔ is-decidable (is-defined l))
  Example-2-6 s l = compact-iff-⊥-or-η s l ,
                    compact-iff-is-defined-decidable s l

 Lemma-2-7 : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
           → x ⊑⟨ 𝓓 ⟩ z → y ⊑⟨ 𝓓 ⟩ z
           → ((d : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ d → y ⊑⟨ 𝓓 ⟩ d → z ⊑⟨ 𝓓 ⟩ d)
           → is-compact 𝓓 x → is-compact 𝓓 y → is-compact 𝓓 z
 Lemma-2-7 = binary-join-is-compact


 Definition-2-8 : (X : 𝓤 ̇  ) → 𝓟-general {𝓣} X → 𝓤 ⊔ 𝓣 ̇
 Definition-2-8 X = 𝕋

 Definition-2-9 : {X : 𝓤 ̇} → 𝓟 X → 𝓤 ̇
 Definition-2-9 = is-Kuratowski-finite-subset

 module _
         {X : 𝓤 ̇  }
         (X-set : is-set X)
        where

  open singleton-subsets X-set
  open singleton-Kuratowski-finite-subsets X-set

  Lemma-2-10 : is-Kuratowski-finite-subset {𝓤} {X} ∅
             × ({x : X} → is-Kuratowski-finite-subset ❴ x ❵)
             × ((A B : 𝓟 X)
                     → is-Kuratowski-finite-subset A
                     → is-Kuratowski-finite-subset B
                     → is-Kuratowski-finite-subset (A ∪ B))
  Lemma-2-10 = ∅-is-Kuratowski-finite-subset ,
               ❴❵-is-Kuratowski-finite-subset X-set ,
               ∪-is-Kuratowski-finite-subset {𝓤} {X}

  Lemma-2-11 : {𝓣 : Universe} (Q : 𝓚 X → 𝓣 ̇)
             → ((A : 𝓚 X) → is-prop (Q A))
             → Q ∅[𝓚]
             → ((x : X) → Q (❴ x ❵[𝓚]))
             → ((A B : 𝓚 X) → Q A → Q B → Q (A ∪[𝓚] B))
             → (A : 𝓚 X) → Q A
  Lemma-2-11 = Kuratowski-finite-subset-induction pe fe X X-set

  open canonical-map-from-lists-to-subsets X-set renaming (κ to β)

  Definition-2-12 : List X → 𝓟 X
  Definition-2-12 = β

  Lemma-2-13 : (A : 𝓟 X)
             → (A ∈image β → is-Kuratowski-finite-subset A)
             × (is-Kuratowski-finite-subset A → A ∈image β)
  Lemma-2-13 A = Kuratowski-finite-subset-if-in-image-of-κ A ,
                 in-image-of-κ-if-Kuratowski-finite-subset pe fe A

\end{code}

We now work with the less general assumption that X lives in 𝓥, i.e. in the same
universe as the index types for directed completeness.

\begin{code}

 module _
         {X : 𝓥 ̇  }
         (X-set : is-set X)
        where

  open import DomainTheory.Examples.Powerset pt fe pe X-set
  Example-2-14 : (A : 𝓟 X)
               → is-compact 𝓟-DCPO A ↔ is-Kuratowski-finite-subset A
  Example-2-14 A = Kuratowski-finite-subset-if-compact A ,
                   compact-if-Kuratowski-finite-subset A

 open import DomainTheory.Basics.Miscelanea pt fe 𝓥

 module _
         (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
         (ρ : 𝓓 continuous-retract-of 𝓔)
        where

  open _continuous-retract-of_ ρ

  Lemma-2-15 : (y : ⟨ 𝓔 ⟩) (x : ⟨ 𝓓 ⟩)
             → y ≪⟨ 𝓔 ⟩ s x
             → r y ≪⟨ 𝓓 ⟩ x
  Lemma-2-15 = continuous-retraction-≪-criterion 𝓓 𝓔 ρ

 module _
         (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
         (ε : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (π : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩)
         (ε-cont : is-continuous 𝓓 𝓔 ε)
         (π-cont : is-continuous 𝓔 𝓓 π)
         ((sec , defl) : is-embedding-projection-pair 𝓓 𝓔 (ε , ε-cont) (π , π-cont))
        where

  Lemma-2-16 : (x y : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ y ↔ ε x ≪⟨ 𝓔 ⟩ ε y
  Lemma-2-16 x y = embeddings-preserve-≪ 𝓓 𝓔 ε ε-cont π π-cont sec defl x y ,
                   embeddings-reflect-≪ 𝓓 𝓔 ε ε-cont π π-cont sec defl x y

  Lemma-2-16-ad : (x : ⟨ 𝓓 ⟩) → is-compact 𝓓 x ↔ is-compact 𝓔 (ε x)
  Lemma-2-16-ad x =
   embeddings-preserve-compactness 𝓓 𝓔 ε ε-cont π π-cont sec defl x ,
   embeddings-reflect-compactness 𝓓 𝓔 ε ε-cont π π-cont sec defl x

\end{code}

Section 3

\begin{code}

 open import DomainTheory.BasesAndContinuity.IndCompletion pt fe 𝓥
 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  open Ind-completion 𝓓

  Definition-3-1 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-3-1 = Ind

  Definition-3-1-ad : Ind → Ind → 𝓥 ⊔ 𝓣 ̇
  Definition-3-1-ad = _≲_

  Lemma-3-2 : is-prop-valued _≲_
            × is-reflexive _≲_
            × is-transitive _≲_
  Lemma-3-2 = ≲-is-prop-valued ,
              ≲-is-reflexive ,
              ≲-is-transitive

  Lemma-3-3 : is-directed-complete _≲_
  Lemma-3-3 I α δ = Ind-∐ α δ ,
                    Ind-∐-is-upperbound α δ ,
                    Ind-∐-is-lowerbound-of-upperbounds α δ

  Lemma-3-4 : Ind → ⟨ 𝓓 ⟩
  Lemma-3-4 = ∐-map

  Lemma-3-4-ad : (α β : Ind) → α ≲ β → ∐-map α ⊑⟨ 𝓓 ⟩ ∐-map β
  Lemma-3-4-ad = ∐-map-is-monotone

  Definition-3-5 : (x : ⟨ 𝓓 ⟩) (α : Ind) → (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  ) × (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  )
  Definition-3-5 x α = α approximates x , α is-left-adjunct-to x

  Remark-3-6 : (L : ⟨ 𝓓 ⟩ → Ind)
             → (  ((x y : ⟨ 𝓓 ⟩) → underlying-order 𝓓 x y → L x ≲ L y)
                × ((x : ⟨ 𝓓 ⟩) (β : Ind) → (L x ≲ β) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map β)))
             ↔ ((x : ⟨ 𝓓 ⟩) → (L x) is-left-adjunct-to x)
  Remark-3-6 L = pr₂ ,
                 (λ adj → left-adjoint-to-∐-map-is-monotone L adj , adj)

  Lemma-3-7 : (L : ⟨ 𝓓 ⟩ → Ind)
            → ((x : ⟨ 𝓓 ⟩) → (L x) is-left-adjunct-to x)
            → (x y : ⟨ 𝓓 ⟩) → underlying-order 𝓓 x y → L x ≲ L y
  Lemma-3-7 = left-adjoint-to-∐-map-is-monotone

  Lemma-3-8 : (α : Ind) (x : ⟨ 𝓓 ⟩) → α approximates x ↔ α is-left-adjunct-to x
  Lemma-3-8 α x = left-adjunct-to-if-approximates α x ,
                  approximates-if-left-adjunct-to α x

  Proposition-3-9 : (L : ⟨ 𝓓 ⟩ → Ind)
                  → is-approximating L ≃ left-adjoint-to-∐-map L
  Proposition-3-9 = left-adjoint-to-∐-map-characterization

\end{code}

Section 4.1

\begin{code}


 open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥
  renaming (structurally-continuous to continuity-data ;
            structurally-algebraic to algebraicity-data)
 open import DomainTheory.BasesAndContinuity.ContinuityDiscussion pt fe 𝓥

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  open Ind-completion 𝓓

  Definition-4-1 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-4-1 = continuity-data 𝓓

  Proposition-4-2 : ∐-map-has-specified-left-adjoint ≃ continuity-data 𝓓
  Proposition-4-2 = specified-left-adjoint-structurally-continuous-≃ 𝓓

 -- TODO
 Remark-4-3 : Σ 𝓔 ꞉ DCPO {𝓤₁} {𝓤₁} , ¬ is-prop (continuity-data 𝓔)
 Remark-4-3 = {!!}
 {- s = s' , h
  where
   open structurally-continuous s
   I = index-of-approximating-family
   α = approximating-family
   s' : continuity-data 𝓓
   s' = record
          { index-of-approximating-family = λ x → I x + I x
          ; approximating-family = λ x → cases (α x) (α x)
          ; approximating-family-is-directed = {!!}
          ; approximating-family-is-way-below = {!!}
          ; approximating-family-∐-＝ = {!!}
          }
   h : s ≠ s'
   h e = {!!}
    where
     baz : structurally-continuous-to-Σ 𝓓 s ＝
             structurally-continuous-to-Σ 𝓓 s'
     baz = ap (structurally-continuous-to-Σ 𝓓) e
     bazz = happly baz
     foo : (x : ⟨ 𝓓 ⟩) → I x ＝ I x + I x
     foo x = ap pr₁ (happly baz x)
 -}

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  open Ind-completion 𝓓

  Definition-4-4 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-4-4 = is-continuous-dcpo 𝓓

  Proposition-4-5 : ∐-map-has-unspecified-left-adjoint 𝓓 ≃ is-continuous-dcpo 𝓓
  Proposition-4-5 = is-continuous-dcpo-iff-∐-map-has-unspecified-left-adjoint 𝓓

  module _
          (c : continuity-data 𝓓)
         where

   open continuity-data c

\end{code}

We introduce the following abbrevations for readability and to match the paper.

\begin{code}

   I = index-of-approximating-family
   α = approximating-family

   Lemma-4-6 : (x y : ⟨ 𝓓 ⟩)
             → (x ⊑⟨ 𝓓 ⟩ y ↔ ((i : I x) → α x i ⊑⟨ 𝓓 ⟩ y))
             × (x ⊑⟨ 𝓓 ⟩ y ↔ ((i : I x) → α x i ≪⟨ 𝓓 ⟩ y))
   Lemma-4-6 x y = (structurally-continuous-⊑-criterion-converse 𝓓 c ,
                    structurally-continuous-⊑-criterion 𝓓 c) ,
                   (structurally-continuous-⊑-criterion'-converse 𝓓 c ,
                    structurally-continuous-⊑-criterion' 𝓓 c)

   Lemma-4-7 : (x y : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ y ↔ (∃ i ꞉ I y , x ⊑⟨ 𝓓 ⟩ α y i)
   Lemma-4-7 x y = structurally-continuous-≪-criterion-converse 𝓓 c ,
                   structurally-continuous-≪-criterion 𝓓 c

  Lemma-4-8 : is-continuous-dcpo 𝓓
            → (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
  Lemma-4-8 = ≪-nullary-interpolation 𝓓

  Lemma-4-9 : is-continuous-dcpo 𝓓
            → {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
            → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
  Lemma-4-9 = ≪-unary-interpolation 𝓓

  Lemma-4-10 : is-continuous-dcpo 𝓓
             → {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
             → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (y ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ z)
  Lemma-4-10 = ≪-binary-interpolation 𝓓

 Theorem-4-11 : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
              → 𝓓 continuous-retract-of 𝓔
              → (continuity-data 𝓔 → continuity-data 𝓓)
              × (is-continuous-dcpo 𝓔 → is-continuous-dcpo 𝓓)
 Theorem-4-11 𝓓 𝓔 ρ =
  structural-continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ ,
  continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ

 Proposition-4-12 : (𝓓 : DCPO {𝓤} {𝓣})
                  → is-continuous-dcpo 𝓓
                  → (is-locally-small 𝓓
                  ↔ ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)))
 Proposition-4-12 𝓓 c = ≪-is-small-valued pe 𝓓 c ,
                        ≪-is-small-valued-converse pe 𝓓 c

\end{code}

Section 4.2

\begin{code}

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  open Ind-completion 𝓓
  open Ind-completion-poset-reflection pe 𝓓

  Definition-4-13 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-4-13 = is-pseudocontinuous-dcpo 𝓓

  Proposition-4-14 : ∐-map/-has-specified-left-adjoint
                   ≃ is-pseudocontinuous-dcpo 𝓓
  Proposition-4-14 = specified-left-adjoint-pseudo-continuous-≃ pe 𝓓

  Table-1 : (continuity-data 𝓓 ≃ ∐-map-has-specified-left-adjoint)
          × (Σ 𝓔 ꞉ DCPO {𝓤₁} {𝓤₁} , ¬ is-prop (continuity-data 𝓔))
          × (is-continuous-dcpo 𝓓 ≃ ∐-map-has-unspecified-left-adjoint 𝓓)
          × is-prop (is-continuous-dcpo 𝓓)
          × (is-pseudocontinuous-dcpo 𝓓 ≃ ∐-map/-has-specified-left-adjoint)
          × is-prop (is-pseudocontinuous-dcpo 𝓓)
  Table-1 = ≃-sym (specified-left-adjoint-structurally-continuous-≃ 𝓓) ,
            Remark-4-3 ,
            ≃-sym (is-continuous-dcpo-iff-∐-map-has-unspecified-left-adjoint 𝓓) ,
            being-continuous-dcpo-is-prop 𝓓 ,
            ≃-sym (specified-left-adjoint-pseudo-continuous-≃ pe 𝓓) ,
            being-pseudocontinuous-dcpo-is-prop 𝓓

  -- Remark-4-15: No formalisable content  (as it's a meta-mathematical remark)

\end{code}

Section 4.3

\begin{code}

  Definition-4-16 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-4-16 = algebraicity-data 𝓓

  Definition-4-17 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-4-17 = is-algebraic-dcpo 𝓓

  Lemma-4-18 : is-algebraic-dcpo 𝓓 → is-continuous-dcpo 𝓓
  Lemma-4-18 = is-continuous-dcpo-if-algebraic-dcpo 𝓓

\end{code}

Section 5

\begin{code}

 open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥

 Definition-5-1 : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇  } (β : B → ⟨ 𝓓 ⟩)
                → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Definition-5-1 = is-small-basis

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
         {B : 𝓥 ̇  }
         (β : B → ⟨ 𝓓 ⟩)
         (β-is-small-basis : is-small-basis 𝓓 β)
        where

  open is-small-basis β-is-small-basis

  Remark-5-2 : (x : ⟨ 𝓓 ⟩)
             → (↡ᴮ 𝓓 β x ≃ ↡ᴮₛ x)
             × is-Directed 𝓓 (↡-inclusionₛ x)
             × (∐ 𝓓 (↡ᴮₛ-is-directed x) ＝ x)
  Remark-5-2 x = Σ-cong (λ b → ≃-sym ≪ᴮₛ-≃-≪ᴮ) ,
                 ↡ᴮₛ-is-directed x ,
                 ↡ᴮₛ-∐-＝ x

 Lemma-5-3 : (𝓓 : DCPO {𝓤} {𝓣})
           → (has-specified-small-basis 𝓓 → continuity-data 𝓓)
           × (has-unspecified-small-basis 𝓓 → is-continuous-dcpo 𝓓)
 Lemma-5-3 𝓓 = structurally-continuous-if-specified-small-basis 𝓓 ,
               is-continuous-dcpo-if-unspecified-small-basis 𝓓

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
         {B : 𝓥 ̇  }
         (β : B → ⟨ 𝓓 ⟩)
         (β-is-small-basis : is-small-basis 𝓓 β)
        where

  open is-small-basis β-is-small-basis

  Lemma-5-4 : {x y : ⟨ 𝓓 ⟩}
            → x ⊑⟨ 𝓓 ⟩ y ≃ ((b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
  Lemma-5-4 = ⊑-in-terms-of-≪ᴮ 𝓓 β β-is-small-basis

 Proposition-5-5 : (𝓓 : DCPO {𝓤} {𝓣})
                 → has-unspecified-small-basis 𝓓
                 → is-locally-small 𝓓
                 × ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
 Proposition-5-5 𝓓 =
  ∥∥-rec (×-is-prop (being-locally-small-is-prop 𝓓 (λ _ → pe))
                    (Π₂-is-prop fe
                      (λ x y → prop-being-small-is-prop
                                (λ _ → pe) (λ _ _ → fe)
                                (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓))))
         (λ (B , β , β-sb) → locally-small-if-small-basis 𝓓 β β-sb ,
                             ≪-is-small-valued-if-small-basis 𝓓 β β-sb)

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
         {B : 𝓥 ̇  }
         (β : B → ⟨ 𝓓 ⟩)
         (β-is-small-basis : is-small-basis 𝓓 β)
        where

  open is-small-basis β-is-small-basis

  Lemma-5-6 : (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x
  Lemma-5-6 = ≪-nullary-interpolation-basis 𝓓 β β-is-small-basis

  Lemma-5-7 : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
            → ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
  Lemma-5-7 = ≪-unary-interpolation-basis 𝓓 β β-is-small-basis

  Lemma-5-8 : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
            → ∃ b ꞉ B , (x   ≪⟨ 𝓓 ⟩ β b)
                      × (y   ≪⟨ 𝓓 ⟩ β b)
                      × (β b ≪⟨ 𝓓 ⟩ z  )
  Lemma-5-8 = ≪-binary-interpolation-basis 𝓓 β β-is-small-basis

 Lemma-5-9 : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } (β : B → ⟨ 𝓓 ⟩)
             (x : ⟨ 𝓓 ⟩) {I : 𝓥 ̇ } (σ : I → ↡ᴮ 𝓓 β x)
           → (is-sup (underlying-order 𝓓) x (↡-inclusion 𝓓 β x ∘ σ)
             → is-sup (underlying-order 𝓓) x (↡-inclusion 𝓓 β x))
           × ((δ : is-Directed 𝓓 (↡-inclusion 𝓓 β x ∘ σ))
             → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
             → is-Directed 𝓓 (↡-inclusion 𝓓 β x))
 Lemma-5-9 𝓓 β x σ = ↡ᴮ-sup-criterion 𝓓 β x σ ,
                     ↡ᴮ-directedness-criterion 𝓓 β x σ

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
         (𝓔 : DCPO {𝓤'} {𝓣'})
        where

  Theorem-5-10 : (s : DCPO[ 𝓓 , 𝓔 ]) (r : DCPO[ 𝓔 , 𝓓 ])
               → is-continuous-retract 𝓓 𝓔 s r
               → {B : 𝓥 ̇  } (β : B → ⟨ 𝓔 ⟩)
               → is-small-basis 𝓔 β
               → is-small-basis 𝓓 ([ 𝓔 , 𝓓 ]⟨ r ⟩ ∘ β)
  Theorem-5-10 (s , s-cont) (r , r-cont) s-section-of-r =
   small-basis-from-continuous-retract pe 𝓓 𝓔
    (record
       { s = s
       ; r = r
       ; s-section-of-r = s-section-of-r
       ; s-is-continuous = s-cont
       ; r-is-continuous = r-cont
       })

  open import DomainTheory.Basics.Exponential pt fe 𝓥

  Proposition-5-11 : has-unspecified-small-basis 𝓓
                   → is-locally-small 𝓔
                   → is-locally-small (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
  Proposition-5-11 = locally-small-exponential-criterion pe 𝓓 𝓔

\end{code}

Section 5.1

\begin{code}

 Definition-5-12 : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇  } (β : B → ⟨ 𝓓 ⟩)
                 → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Definition-5-12 = is-small-compact-basis

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
         {B : 𝓥 ̇  }
         (β : B → ⟨ 𝓓 ⟩)
         (β-is-small-compact-basis : is-small-compact-basis 𝓓 β)
        where

  open is-small-compact-basis β-is-small-compact-basis

  Remark-5-13 : (x : ⟨ 𝓓 ⟩)
              → (↓ᴮ 𝓓 β x ≃ ↓ᴮₛ x)
              × is-Directed 𝓓 (↓-inclusionₛ x)
              × (∐ 𝓓 (↓ᴮₛ-is-directed x) ＝ x)
  Remark-5-13 x = Σ-cong (λ b → ≃-sym ⊑ᴮₛ-≃-⊑ᴮ) ,
                  ↓ᴮₛ-is-directed x ,
                  ↓ᴮₛ-∐-＝ x

 Lemma-5-14 : (𝓓 : DCPO {𝓤} {𝓣})
            → (has-specified-small-compact-basis 𝓓 → algebraicity-data 𝓓)
            × (has-unspecified-small-compact-basis 𝓓 → is-algebraic-dcpo 𝓓)
 Lemma-5-14 𝓓 = structurally-algebraic-if-specified-small-compact-basis 𝓓 ,
                is-algebraic-dcpo-if-unspecified-small-compact-basis 𝓓

 Lemma-5-15 : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇} (β : B → ⟨ 𝓓 ⟩)
            → is-small-basis 𝓓 β
            → ((b : B) → is-compact 𝓓 (β b))
            → is-small-compact-basis 𝓓 β
 Lemma-5-15 = small-and-compact-basis

 Proposition-5-16 : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇} (β : B → ⟨ 𝓓 ⟩)
                  → is-small-compact-basis 𝓓 β
                  → (x : ⟨ 𝓓 ⟩) → is-compact 𝓓 x → ∃ b ꞉ B , β b ＝ x
 Proposition-5-16 = small-compact-basis-contains-all-compact-elements

\end{code}

Section 5.2

\begin{code}

 module _ where
  open import DomainTheory.Examples.Omega pt fe pe 𝓥
  Example-5-17 : is-small-compact-basis Ω-DCPO κ
               × is-algebraic-dcpo Ω-DCPO
  Example-5-17 = κ-is-small-compact-basis , Ω-is-algebraic-dcpo

 module _ where
  open import Lifting.Construction 𝓥 renaming (⊥ to ⊥𝓛)
  open import DomainTheory.Lifting.LiftingSet pt fe 𝓥 pe
  open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓥
  Example-5-18 : {X : 𝓥 ̇  } (X-set : is-set X)
               → is-small-compact-basis (𝓛-DCPO X-set) (κ X-set)
               × is-algebraic-dcpo (𝓛-DCPO X-set)
  Example-5-18 X-set = κ-is-small-compact-basis X-set ,
                       𝓛-is-algebraic-dcpo X-set

 module _
         {X : 𝓥 ̇  }
         (X-set : is-set X)
        where

  open import DomainTheory.Examples.Powerset pt fe pe X-set
  open canonical-map-from-lists-to-subsets X-set renaming (κ to β)
  Example-5-19 : is-small-compact-basis 𝓟-DCPO (canonical-map-from-lists-to-subsets.κ X-set)
               × is-algebraic-dcpo 𝓟-DCPO
  Example-5-19 = κ-is-small-compact-basis , 𝓟-is-algebraic-dcpo

 module _
         (P : 𝓤 ̇  )
         (P-is-prop : is-prop P)
        where

  open import DomainTheory.Examples.LiftingLargeProposition pt fe pe 𝓥 𝓤 P P-is-prop
  Example-5-20 : is-algebraic-dcpo (𝓛P ⁻)
               × (has-unspecified-small-compact-basis (𝓛P ⁻) ↔ P is 𝓥 small)
  Example-5-20 = 𝓛P-is-algebraic ,
                 (𝓛P-has-unspecified-small-compact-basis-resizes ,
                  ∣_∣ ∘ resizing-gives-small-compact-basis)

\end{code}

Example 5.21 is one of the few places where we use univalence (and set
replacement, or equivalently, small set quotients).

\begin{code}

module _
        (ua : Univalence)
        (sr : Set-Replacement pt)
        (𝓤 : Universe)
       where

 fe' : Fun-Ext
 fe' {𝓤 } {𝓥} = Univalence-gives-FunExt ua 𝓤 𝓥

 open import DomainTheory.Examples.Ordinals pt ua sr 𝓤
 open import DomainTheory.Basics.Dcpo pt fe' 𝓤
 open import DomainTheory.Basics.SupComplete pt fe' 𝓤
 open import DomainTheory.BasesAndContinuity.Continuity pt fe' 𝓤
 open import DomainTheory.BasesAndContinuity.Bases pt fe' 𝓤

 Example-5-21 : DCPO {𝓤 ⁺} {𝓤}
              × is-sup-complete Ordinals-DCPO
              × is-algebraic-dcpo Ordinals-DCPO
              × ¬ (has-unspecified-small-basis Ordinals-DCPO)
 Example-5-21 = Ordinals-DCPO ,
                Ordinals-DCPO-is-sup-complete ,
                Ordinals-DCPO-is-algebraic ,
                Ordinals-DCPO-has-no-small-basis

\end{code}

Section 5.3

\begin{code}

module _
        (𝓥 : Universe)
       where

 open import DomainTheory.Basics.Dcpo pt fe 𝓥
 open import DomainTheory.Basics.Miscelanea pt fe 𝓥
 open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
 open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥
 open import DomainTheory.BasesAndContinuity.CompactBasis pt fe 𝓥

 module _
         (𝓓 : DCPO {𝓤} {𝓣})
        where

  Lemma-5-22 : is-algebraic-dcpo 𝓓
             → (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↓ᴷ-inclusion 𝓓 x)
  Lemma-5-22 = ↓ᴷ-is-sup 𝓓

  Lemma-5-23 : Set-Replacement pt
             → has-specified-small-compact-basis 𝓓 → is-small (K 𝓓)
  Lemma-5-23 = K-is-small' 𝓓

  Lemma-5-23-ad : Univalence
                → Set-Replacement pt
                → has-unspecified-small-compact-basis 𝓓 → is-small (K 𝓓)
  Lemma-5-23-ad = K-is-small 𝓓

  Proposition-5-24 : Univalence → Set-Replacement pt
                   → has-specified-small-compact-basis 𝓓
                   ↔ has-unspecified-small-compact-basis 𝓓
  Proposition-5-24 ua sr = specified-unspecified-equivalence ua sr 𝓓

\end{code}

Section 6

\begin{code}

\end{code}

Section 6.1

\begin{code}

\end{code}

Section 6.2

\begin{code}

\end{code}

Section 6.3

\begin{code}

\end{code}

Section 7.1

\begin{code}

\end{code}

Section 7.2

\begin{code}

\end{code}