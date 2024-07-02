Tom de Jong, July 2024.

This file corresponds to the paper

   "Domain Theory in Univalent Foundations I:
    Directed complete posets and Scott’s D∞"
   Tom de Jong
   2024
   https://arxiv.org/abs/TODO

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc

module DomainTheory.Part-I
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.Powerset-MultiUniverse
open import UF.Sets
open import UF.Size hiding (is-locally-small)
open import UF.SubtypeClassifier

open import OrderedTypes.Poset fe

{- Section 2 -}

Definition-2-1 : (𝓤 : Universe) (X : 𝓥 ̇  ) → 𝓤 ⁺ ⊔ 𝓥 ̇
Definition-2-1 𝓤 X = X is 𝓤 small

Definition-2-2 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-2 𝓤 = Ω 𝓤

Definition-2-3 : (𝓥 : Universe) (X : 𝓤 ̇  ) → 𝓥 ⁺ ⊔ 𝓤 ̇
Definition-2-3 𝓥 X = 𝓟 {𝓥} X

Definition-2-4 : (𝓥 : Universe) (X : 𝓤 ̇  )
               → (X → 𝓟 {𝓥} X → 𝓥 ̇  )
               × (𝓟 {𝓥} X → 𝓟 {𝓥} X → 𝓥 ⊔ 𝓤 ̇  )
Definition-2-4 𝓥 X = _∈_ , _⊆_

{- Section 3 -}

module _
        (P : 𝓤 ̇  ) (_⊑_ : P → P → 𝓣 ̇  )
       where

 open PosetAxioms

 Definition-3-1 : 𝓤 ⊔ 𝓣 ̇
 Definition-3-1 = is-prop-valued _⊑_
                × is-reflexive _⊑_
                × is-transitive _⊑_

 Definition-3-2 : 𝓤 ⊔ 𝓣 ̇
 Definition-3-2 = Definition-3-1 × is-antisymmetric _⊑_

 Lemma-3-3 : is-prop-valued _⊑_
           → is-reflexive _⊑_
           → is-antisymmetric _⊑_
           → is-set P
 Lemma-3-3 = posets-are-sets _⊑_

 module _ (𝓥 : Universe) where
  open import DomainTheory.Basics.Dcpo pt fe 𝓥

  Definition-3-4 : {I : 𝓥 ̇  } → (I → P) → (𝓥 ⊔ 𝓣 ̇  ) × (𝓥 ⊔ 𝓣 ̇  )
  Definition-3-4 {I} α = is-semidirected _⊑_ α , is-directed _⊑_ α

  Remark-3-5 : {I : 𝓥 ̇  } (α : I → P)
             → is-directed _⊑_ α
             ＝ ∥ I ∥ × ((i j : I) → ∥ Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k) ∥)
  Remark-3-5 α = refl

  Definition-3-6 : {I : 𝓥 ̇  } → P → (I → P) → (𝓥 ⊔ 𝓣 ̇  ) × (𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇  )
  Definition-3-6 {I} x α = (is-upperbound _⊑_ x α) , is-sup _⊑_ x α

  Definition-3-6-ad : poset-axioms _⊑_
                    → {I : 𝓥 ̇  } (α : I → P)
                    → {x y : P} → is-sup _⊑_ x α → is-sup _⊑_ y α → x ＝ y
  Definition-3-6-ad pa {I} α = sups-are-unique _⊑_ pa α

  Definition-3-7 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  Definition-3-7 = is-directed-complete _⊑_

  Definition-3-7-ad : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇}
                      {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
  Definition-3-7-ad = ∐

  Remark-3-8 : poset-axioms _⊑_
             → {I : 𝓥 ̇  } (α : I → P)
             → is-prop (has-sup _⊑_ α)
  Remark-3-8 = having-sup-is-prop _⊑_

module _ (𝓥 : Universe) where
 open import DomainTheory.Basics.Dcpo pt fe 𝓥

 Definition-3-9 : {𝓤 𝓣 : Universe} → (𝓤 ⊔ 𝓥 ⊔ 𝓣) ⁺ ̇
 Definition-3-9 {𝓤} {𝓣} = DCPO {𝓤} {𝓣}

 -- Remark-3-10: No formalisable content.

 open import DomainTheory.Basics.Pointed pt fe 𝓥
 open import DomainTheory.Basics.Miscelanea pt fe 𝓥

 Definition-3-11 : {𝓤 𝓣 : Universe} → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
 Definition-3-11 {𝓤} {𝓣} = DCPO⊥ {𝓤} {𝓣}

 Definition-3-12 : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Definition-3-12 𝓓 = is-locally-small' 𝓓

 Lemma-3-13 : (𝓓 : DCPO {𝓤} {𝓣})
            → is-locally-small 𝓓 ≃ is-locally-small' 𝓓
 Lemma-3-13 𝓓 = local-smallness-equivalent-definitions 𝓓

 open import DomainTheory.Examples.Omega pt fe pe 𝓥

 Example-3-14 : DCPO⊥ {𝓥 ⁺} {𝓥}
 Example-3-14 = Ω-DCPO⊥

 module _
         (X : 𝓤 ̇  )
         (X-is-set : is-set X)
        where

  open import DomainTheory.Examples.Powerset pt fe pe X-is-set

  Example-3-15 :  DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓤}
  Example-3-15 = generalized-𝓟-DCPO⊥ 𝓥

 module _
         (X : 𝓥 ̇  )
         (X-is-set : is-set X)
        where

  open import DomainTheory.Examples.Powerset pt fe pe X-is-set

  Example-3-15-ad :  DCPO⊥ {𝓥 ⁺} {𝓥}
  Example-3-15-ad = 𝓟-DCPO⊥

 Proposition-3-16 : (𝓓 : DCPO {𝓤} {𝓣})
                  → is-ω-complete (underlying-order 𝓓)
 Proposition-3-16 = dcpos-are-ω-complete

{- Section 4 -}

 Definition-4-1 : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
 Definition-4-1 𝓓 𝓔 f = is-continuous 𝓓 𝓔 f

 -- Remark-4-2: Note that the parameter 𝓥 in the type DCPO is fixed.

 module _
         (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
        where

  Lemma-4-3 : (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
            → is-prop (is-continuous 𝓓 𝓔 f)
  Lemma-4-3 = being-continuous-is-prop 𝓓 𝓔

  Lemma-4-3-ad : (f g : DCPO[ 𝓓 , 𝓔 ])
               → underlying-function 𝓓 𝓔 f ＝ underlying-function 𝓓 𝓔 g
               → f ＝ g
  Lemma-4-3-ad f g e = to-continuous-function-＝ 𝓓 𝓔 (happly e)

  Lemma-4-4 : (f : DCPO[ 𝓓 , 𝓔 ])
            → is-monotone 𝓓 𝓔 [ 𝓓 , 𝓔 ]⟨ f ⟩
  Lemma-4-4 = monotone-if-continuous 𝓓 𝓔

  Lemma-4-5 : {f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩} → is-monotone 𝓓 𝓔 f
            → {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
            → is-Directed 𝓓 α
            → is-Directed 𝓔 (f ∘ α)
  Lemma-4-5 = image-is-directed 𝓓 𝓔

  Lemma-4-6 : (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
              (δ : is-Directed 𝓓 α)
            → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩
              ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
  Lemma-4-6 = continuous-∐-⊑ 𝓓 𝓔

  Lemma-4-6-ad : (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (m : is-monotone 𝓓 𝓔 f)
               → ((I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                     → f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed 𝓓 𝓔 m δ))
               → is-continuous 𝓓 𝓔 f
  Lemma-4-6-ad = continuity-criterion 𝓓 𝓔

  -- Remark-4-7: No formalisable content.


\end{code}