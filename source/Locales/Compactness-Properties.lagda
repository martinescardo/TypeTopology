---
title:        Properties of compactness
author:       Ayberk Tosun
date-started: 2024-07-19
---

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.Classifiers
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

module Locales.Compactness-Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Fin.Kuratowski pt
open import Fin.Type
open import Locales.Frame     pt fe
open import Locales.WayBelowRelation.Definition  pt fe
open import MLTT.List using (member; []; _∷_; List; in-head; in-tail; length)
open import Slice.Family
open import Taboos.FiniteSubsetTaboo pt fe
open import UF.Equiv hiding (_■)
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Powerset-Fin pt hiding (⟨_⟩)
open import UF.Powerset-MultiUniverse
open import UF.Sets-Properties
open import Locales.Compactness pt fe

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt

\end{code}

\section{Preliminaries}

Given a family `S`, we denote the type of its subfamilies by `SubFam S`.

\begin{code}

SubFam : {A : 𝓤  ̇} {𝓦 : Universe} → Fam 𝓦 A → 𝓦 ⁺  ̇
SubFam {𝓤} {A} {𝓦} (I , α) = Σ J ꞉ 𝓦  ̇ , (J → I)

\end{code}

\begin{code}

not-in-empty-list : {A : 𝓤  ̇} {x : A} → ¬ ∥ member x [] ∥
not-in-empty-list = ∥∥-rec 𝟘-is-prop (λ ())

\end{code}

Compactness could have been alternatively defined as:

\begin{code}

is-compact-open' : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open' {𝓤} {𝓥} {𝓦} X U =
 Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
  U ≤ (⋁[ 𝒪 X ] S) ⇒
   (Ǝ (J , h) ꞉ SubFam S ,
       is-Kuratowski-finite J
     × (U ≤ (⋁[ 𝒪 X ] ⁅  S [ h j ] ∣ j ∶ J ⁆)) holds)
  where
   open PosetNotation (poset-of (𝒪 X))

\end{code}

Given any list, the type of elements that fall in the list is a
Kuratowski-finite type.

TODO: The following function `nth` should be placed in a more appropriate
module.

\begin{code}

nth : {X : 𝓤  ̇} → (xs : List X) → (i : Fin (length xs)) → Σ x ꞉ X , ∥ member x xs ∥
nth         (x ∷ _)  (inr ⋆) = x , ∣ in-head ∣
nth {_} {X} (_ ∷ xs) (inl n) = x , ∥∥-functor in-tail (pr₂ IH)
 where
  IH : Σ x ꞉ X , ∥ member x xs ∥
  IH = nth xs n

  x : X
  x = pr₁ IH

nth-is-surjection : {X : 𝓤  ̇} (xs : List X) → is-surjection (nth xs)
nth-is-surjection []       (y , μ) = ∥∥-rec ∃-is-prop (λ ()) μ
nth-is-surjection (x ∷ xs) (y , μ) = ∥∥-rec ∃-is-prop † μ
 where

  † : member y (x ∷ xs) → ∃ i ꞉ Fin (length (x ∷ xs)) , (nth (x ∷ xs) i ＝ y , μ)
  † in-head     = ∣ inr ⋆ , to-subtype-＝ (λ _ → ∥∥-is-prop) refl ∣
  † (in-tail p) = ∥∥-rec ∃-is-prop ‡ IH
   where
    IH : (y , ∣ p ∣) ∈image nth xs
    IH = nth-is-surjection xs (y , ∣ p ∣)

    ‡ : Σ i ꞉ Fin (length xs) , (nth xs i ＝ y , ∣ p ∣)
      → ∃ i ꞉ Fin (length (x ∷ xs)) , (nth (x ∷ xs) i ＝ y , μ)
    ‡ (i , q) =
     ∣ (inl i) , (to-subtype-＝ (λ _ → ∥∥-is-prop) (pr₁ (from-Σ-＝ q))) ∣

list-members-is-Kuratowski-finite : {X : 𝓤  ̇}
                                  → (xs : List X)
                                  → is-Kuratowski-finite (Σ x ꞉ X , ∥ member x xs ∥)
list-members-is-Kuratowski-finite {𝓤} {A} xs =
 ∣ length xs , nth xs , nth-is-surjection xs ∣

\end{code}

It is easy to show that this implies the standdard definition of compactness,
but we need a bit of preparation first.

Given a family `S`, we denote by `family-of-lists S` the family of families
of lists of `S`.

\begin{code}

module Some-Lemmas-On-Directification (F : Frame 𝓤 𝓥 𝓦) where

 family-of-lists : Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 (Fam 𝓦 ⟨ F ⟩)
 family-of-lists S = List (index S) , h
  where
   h : List (index S) → Fam 𝓦 ⟨ F ⟩
   h is = (Σ i ꞉ index S , ∥ member i is ∥) , S [_] ∘ pr₁

\end{code}

Using this, we can give an alternative definition of the directification of
a family:

\begin{code}

 directify₂ : Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
 directify₂ S = ⁅ ⋁[ F ] T ∣ T ε family-of-lists S ⁆

\end{code}

The function `directify₂` is equal to `directify` as expected.

\begin{code}

 directify₂-is-equal-to-directify
  : (S : Fam 𝓦 ⟨ F ⟩)
  → directify₂ S [_] ∼ directify F S [_]

 directify₂-is-equal-to-directify S [] =
  directify₂ S [ [] ]   ＝⟨ Ⅰ    ⟩
  𝟎[ F ]                ＝⟨ refl ⟩
  directify F S [ [] ]   ∎
   where

    † : (directify₂ S [ [] ] ≤[ poset-of F ] 𝟎[ F ]) holds
    † = ⋁[ F ]-least
         (family-of-lists S [ [] ])
         (𝟎[ F ] , λ { (_ , μ) → 𝟘-elim (not-in-empty-list μ) })

    Ⅰ = only-𝟎-is-below-𝟎 F (directify₂ S [ [] ]) †

 directify₂-is-equal-to-directify S (i ∷ is) =
  directify₂ S [ i ∷ is ]                ＝⟨ Ⅰ    ⟩
  S [ i ] ∨[ F ] directify₂ S [ is ]     ＝⟨ Ⅱ    ⟩
  S [ i ] ∨[ F ] directify  F S [ is ]   ＝⟨ refl ⟩
  directify F S [ i ∷ is ]               ∎
   where
    open PosetNotation (poset-of F)
    open PosetReasoning (poset-of F)
    open Joins (λ x y → x ≤[ poset-of F ] y)

    IH = directify₂-is-equal-to-directify S is

    β : ((S [ i ] ∨[ F ] directify₂ S [ is ])
          is-an-upper-bound-of
         (family-of-lists S [ i ∷ is ]))
         holds
    β (j , ∣μ∣) =
     ∥∥-rec (holds-is-prop (S [ j ] ≤ (S [ i ] ∨[ F ] directify₂ S [ is ]))) † ∣μ∣
      where
       † : member j (i ∷ is)
         → (S [ j ] ≤ (S [ i ] ∨[ F ] directify₂ S [ is ]))
            holds
       † in-head     = ∨[ F ]-upper₁ (S [ j ]) (directify₂ S [ is ])
       † (in-tail μ) =
        family-of-lists S [ i ∷ is ] [ j , μ′ ]  ＝⟨ refl ⟩ₚ
        S [ j ]                                  ≤⟨ Ⅰ     ⟩
        directify₂ S [ is ]                      ≤⟨ Ⅱ     ⟩
        S [ i ] ∨[ F ] directify₂ S [ is ]       ■
         where
          μ′ : ∥ member j (i ∷ is) ∥
          μ′ = ∣ in-tail μ ∣

          Ⅰ = ⋁[ F ]-upper (family-of-lists S [ is ]) (j , ∣ μ ∣)
          Ⅱ = ∨[ F ]-upper₂ (S [ i ]) (directify₂ S [ is ])

    γ : ((directify₂ S [ i ∷ is ])
          is-an-upper-bound-of
         (family-of-lists S [ is ]))
        holds
    γ (k , μ) = ∥∥-rec (holds-is-prop (S [ k ] ≤ directify₂ S [ i ∷ is ])) ♢ μ
     where
      ♢ : member k is → (S [ k ] ≤ directify₂ S [ i ∷ is ]) holds
      ♢ μ = ⋁[ F ]-upper (family-of-lists S [ i ∷ is ]) (k , ∣ in-tail μ ∣)

    † : (directify₂ S [ i ∷ is ] ≤ (S [ i ] ∨[ F ] directify₂ S [ is ]))
         holds
    † = ⋁[ F ]-least
         (family-of-lists S [ i ∷ is ])
         ((S [ i ] ∨[ F ] directify₂ S [ is ]) , β)

    ‡ : ((S [ i ] ∨[ F ] directify₂ S [ is ]) ≤ directify₂ S [ i ∷ is ])
         holds
    ‡ = ∨[ F ]-least ‡₁ ‡₂
     where
      ‡₁ : (S [ i ] ≤ directify₂ S [ i ∷ is ]) holds
      ‡₁ = ⋁[ F ]-upper (family-of-lists S [ i ∷ is ]) (i , ∣ in-head ∣)

      ‡₂ : (directify₂ S [ is ] ≤ directify₂ S [ i ∷ is ]) holds
      ‡₂ = ⋁[ F ]-least
            (family-of-lists S [ is ])
            (directify₂ S [ i ∷ is ] , γ)


    Ⅱ  = ap (λ - → S [ i ] ∨[ F ] -) IH
    Ⅰ  = ≤-is-antisymmetric (poset-of F) † ‡

\end{code}

Using the equality between `directify` and `directify₂`, we can now easily show
how to obtain a subcover, from which it follows that `is-compact` implies
`is-compact'`.

\begin{code}

module Characterization-Of-Compactness₁ (X : Locale 𝓤 𝓥 𝓦) where

 open Some-Lemmas-On-Directification (𝒪 X)
 open PosetNotation (poset-of (𝒪 X))
 open PosetReasoning (poset-of (𝒪 X))

 finite-subcover-through-directification
  : (U : ⟨ 𝒪 X ⟩)
  → (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
  → (is : List (index S))
  → (U ≤ directify (𝒪 X) S [ is ]) holds
  → Σ (J , β) ꞉ SubFam S ,
     is-Kuratowski-finite J × (U ≤ (⋁[ 𝒪 X ] ⁅  S [ β j ] ∣ j ∶ J ⁆)) holds
 finite-subcover-through-directification U S is p = T , 𝕗 , q
  where
   T : SubFam S
   T = (Σ i ꞉ index S , ∥ member i is ∥) , pr₁

   𝕗 : is-Kuratowski-finite (index T)
   𝕗 = list-members-is-Kuratowski-finite is

   † = directify₂-is-equal-to-directify S is ⁻¹

   q : (U ≤ (⋁[ 𝒪 X ] ⁅ S [ T [ x ] ] ∣ x ∶ index T ⁆)) holds
   q = U                                          ≤⟨ p     ⟩
       directify (𝒪 X) S [ is ]                   ＝⟨ †    ⟩ₚ
       directify₂ S [ is ]                        ＝⟨ refl ⟩ₚ
       ⋁[ 𝒪 X ] ⁅ S [ T [ x ] ] ∣ x ∶ index T ⁆   ■

\end{code}

It follows from this that `is-compact-open` implies `is-compact-open'`.

\begin{code}

 compact-open-implies-compact-open' : (U : ⟨ 𝒪 X ⟩)
                                    → is-compact-open  X U holds
                                    → is-compact-open' X U holds
 compact-open-implies-compact-open' U κ S q =
  ∥∥-functor † (κ S↑ δ p)
  where
   open JoinNotation (join-of (𝒪 X))

   Xₚ = poset-of (𝒪 X)

   S↑ : Fam 𝓦 ⟨ 𝒪 X ⟩
   S↑ = directify (𝒪 X) S

   δ : is-directed (𝒪 X) (directify (𝒪 X) S) holds
   δ = directify-is-directed (𝒪 X) S

   p : (U ≤[ Xₚ ] (⋁[ 𝒪 X ] S↑)) holds
   p = U             ≤⟨ Ⅰ ⟩
       ⋁[ 𝒪 X ] S    ＝⟨ Ⅱ ⟩ₚ
       ⋁[ 𝒪 X ] S↑   ■
        where
         Ⅰ = q
         Ⅱ = directify-preserves-joins (𝒪 X) S

   † : (Σ is ꞉ index S↑ , (U ≤[ Xₚ ] S↑ [ is ]) holds)
     → Σ (J , β) ꞉ SubFam S ,
        is-Kuratowski-finite J × (U ≤[ Xₚ ] (⋁⟨ j ∶ J ⟩ S [ β j ])) holds
   † = uncurry (finite-subcover-through-directification U S)

\end{code}

\section{The property `is-compact-open'` implies `is-compact-open`}

We now prove the converse which is a bit more difficult. We start with some
preparation.

Given a subset `P : ⟨ 𝒪 X ⟩ → Ω` and a family `S : Fam 𝓤 ⟨ 𝒪 X ⟩`, the type
`Upper-Bound-Data P S` is the type indices of `S` such that `S [ i ]` is an
upper bound of the subset `P`.

\begin{code}

module Characterization-Of-Compactness₂ (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open Some-Lemmas-On-Directification (𝒪 X)
 open PosetNotation (poset-of (𝒪 X))
 open PosetReasoning (poset-of (𝒪 X))
 open Joins (λ x y → x ≤ y)

 Upper-Bound-Data : 𝓟 {𝓣} ⟨ 𝒪 X ⟩ → Fam 𝓤 ⟨ 𝒪 X ⟩ → 𝓤 ⁺ ⊔ 𝓣  ̇
 Upper-Bound-Data P S =
  Σ i ꞉ index S , (Ɐ x ꞉ ⟨ 𝒪 X ⟩ , P x ⇒ x ≤ S [ i ]) holds

\end{code}

Now, the truncated version of this which we denote `has-upper-bound-in`:

\begin{code}

 has-upper-bound-in :  𝓟 {𝓣} ⟨ 𝒪 X ⟩ → Fam 𝓤 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺ ⊔ 𝓣)
 has-upper-bound-in P S = ∥ Upper-Bound-Data P S ∥Ω

\end{code}

We define the following version of the characteristic function.

\begin{code}

 χ∙ : Fam 𝓤 ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 χ∙ S U = U ∈image (S [_]) , being-in-the-image-is-prop U (S [_])
  where
   open Equality carrier-of-[ poset-of (𝒪 X) ]-is-set

\end{code}

\begin{code}

 open singleton-Kuratowski-finite-subsets
 open binary-unions-of-subsets pt

 main-lemma : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
            → is-directed (𝒪 X) S holds
            → (P : 𝓟 {𝓤 ⁺} ⟨ 𝒪 X ⟩)
            → (P ⊆ χ∙ S)
            → is-Kuratowski-finite-subset P
            → has-upper-bound-in P S holds
 main-lemma S (ι , υ) P ψ 𝕗 =
  Kuratowski-finite-subset-induction pe fe ⟨ 𝒪 X ⟩ σ R i β γ δ {!!} {!!}
   where
    R : 𝓚 ⟨ 𝒪 X ⟩ → 𝓤 ⁺  ̇
    R (Q , φ) = (Q ⊆ P) → has-upper-bound-in Q S holds

    i : (A : 𝓚 ⟨ 𝒪 X ⟩) → is-prop (R A)
    i (A , _) = Π-is-prop fe (λ q → holds-is-prop (has-upper-bound-in A S))

    σ : is-set ⟨ 𝒪 X ⟩
    σ = carrier-of-[ poset-of (𝒪 X) ]-is-set

    β : R ∅[𝓚]
    β _ = ∥∥-functor (λ i → i , λ _ ()) ι

    γ : (U : ⟨ 𝒪 X ⟩) → R (❴ σ ❵[𝓚] U)
    γ U μ = ∥∥-functor † (ψ U (μ U refl))
     where
      † : Σ i ꞉ index S , S [ i ] ＝ U
        → Σ i ꞉ index S , ((V : ⟨ 𝒪 X ⟩) → U ＝ V → (V ≤ S [ i ]) holds)
      † (i , p) = i , ϑ
       where
        ϑ : (V : ⟨ 𝒪 X ⟩) → U ＝ V → (V ≤ S [ i ]) holds
        ϑ V q = V        ＝⟨ q ⁻¹ ⟩ₚ
                U        ＝⟨ p ⁻¹ ⟩ₚ
                S [ i ]  ■

    δ : (𝒜 ℬ : 𝓚 ⟨ 𝒪 X ⟩) → R 𝒜 → R ℬ → R (𝒜 ∪[𝓚] ℬ)
    δ 𝒜@(A , _) ℬ@(B , _) φ ψ h =
     ∥∥-rec₂ (holds-is-prop (has-upper-bound-in (A ∪ B) S)) † (φ i₁) (ψ i₂)
      where
       i₁ : A ⊆ P
       i₁ = ⊆-trans A (A ∪ B) P (∪-is-upperbound₁ A B) h

       i₂ : B ⊆ P
       i₂ = ⊆-trans B (A ∪ B) P (∪-is-upperbound₂ A B) h

       † : Upper-Bound-Data A S
         → Upper-Bound-Data B S
         → has-upper-bound-in (A ∪ B) S holds
       † (i , a) (j , b) = ∥∥-functor ‡ (υ i j)
        where
         ‡ : (Σ k ꞉ index S ,
               ((S [ k ]) is-an-upper-bound-of₂ (S [ i ] , S [ j ])) holds)
           → Σ k ꞉ index S , ((U : ⟨ 𝒪 X ⟩) → U ∈ (A ∪ B) → (U ≤ S [ k ]) holds)
         ‡ (k , p₁ , p₂) = {!!}

\end{code}

A directed family contains at least one upper bound of every Kuratowski-finite
subfamily.

\begin{code}

 directed-families-have-upper-bounds-of-Kuratowski-finite-subfamilies
  : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
  → is-directed (𝒪 X) S holds
  → is-Kuratowski-finite (index S)
  → has-upper-bound-in (χ∙ S) S holds
 directed-families-have-upper-bounds-of-Kuratowski-finite-subfamilies S 𝒹 𝒻 =
  {!!}

\end{code}

\begin{code}

 compact-open'-implies-compact-open : (U : ⟨ 𝒪 X ⟩)
                                    → is-compact-open' X U holds
                                    → is-compact-open  X U holds
 compact-open'-implies-compact-open U κ S δ p =
  ∥∥-rec ∃-is-prop † (κ S p)
  where
   † : (Σ (J , h) ꞉ SubFam S , is-Kuratowski-finite J × ((U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] (J , (λ x → S [ h x ])))) holds))
     → (Ǝ k ꞉ index S , ((U ≤[ poset-of (𝒪 X) ] S [ k ]) holds)) holds
   † ((J , h) , κ , q) = ∥∥-rec ∃-is-prop ‡ {!!}
    where
     ‡ : (Σ j ꞉ J , (((S [ h j ]) is-an-upper-bound-of (J , (S [_] ∘ h))) holds))
       → ∃ (λ k → rel-syntax (poset-of (𝒪 X)) U (S [ k ]) holds)
     ‡ (j , υ) = ∣ h j , {!!} ∣
      where
       ♢ : (U ≤[ poset-of (𝒪 X) ] S [ h j ]) holds
       ♢ = U ≤⟨ q ⟩ ⋁[ 𝒪 X ] (J , (λ x → S [ h x ])) ≤⟨ ⋁[ 𝒪 X ]-least (J , (λ x → S [ h x ])) ((S [ h j ]) , υ) ⟩ S [ h j ] ■

\end{code}
