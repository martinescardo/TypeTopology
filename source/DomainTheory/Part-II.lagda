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
open import UF.Size hiding (is-locally-small)
open import UF.Subsingletons-FunExt
open import UF.Univalence

-}

open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Powerset-Fin pt hiding (⟨_⟩)
open import UF.Powerset-MultiUniverse renaming (𝓟 to 𝓟-general)
open import UF.Powerset
open import UF.Sets
open import UF.SubtypeClassifier renaming (⊥ to 𝟘Ω ; ⊤ to 𝟙Ω)

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

  open canonical-map-from-lists-to-subsets X-set

  Definition-2-12 : List X → 𝓟 X
  Definition-2-12 = κ

\end{code}

To match the paper, we write β for κ.

\begin{code}

  β = κ

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

\end{code}

Section 4.2

\begin{code}

\end{code}

Section 4.3

\begin{code}

\end{code}

Section 5

\begin{code}

\end{code}

Section 5.1

\begin{code}

\end{code}

Section 5.2

\begin{code}

\end{code}

Section 5.3

\begin{code}

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