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
   h is = (Σ i ꞉ index S , member i is) , S [_] ∘ pr₁

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
    † = ⋁[ F ]-least (family-of-lists S [ [] ]) (_ , λ ())

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
    β (j , in-head)   = ∨[ F ]-upper₁ (S [ j ]) (directify₂ S [ is ])
    β (j , in-tail p) =
     family-of-lists S [ i ∷ is ] [ j , in-tail p ]   ＝⟨ refl ⟩ₚ
     S [ j ]                                          ≤⟨ Ⅰ     ⟩
     directify₂ S [ is ]                              ≤⟨ Ⅱ     ⟩
     S [ i ] ∨[ F ] directify₂ S [ is ]               ■
      where
       Ⅰ = ⋁[ F ]-upper (family-of-lists S [ is ]) (j , p)
       Ⅱ = ∨[ F ]-upper₂ (S [ i ]) (directify₂ S [ is ])

    γ : ((directify₂ S [ i ∷ is ])
          is-an-upper-bound-of
         (family-of-lists S [ is ]))
        holds
    γ (k , μ) = ⋁[ F ]-upper (family-of-lists S [ i ∷ is ]) (k , in-tail μ)

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
      ‡₁ = ⋁[ F ]-upper (family-of-lists S [ i ∷ is ]) (i , in-head)

      ‡₂ : (directify₂ S [ is ] ≤ directify₂ S [ i ∷ is ]) holds
      ‡₂ = ⋁[ F ]-least
            (family-of-lists S [ is ])
            (directify₂ S [ i ∷ is ] , γ)


    Ⅱ  = ap (λ - → S [ i ] ∨[ F ] -) IH
    Ⅰ  = ≤-is-antisymmetric (poset-of F) † ‡

\end{code}

Using the equality between `directify` and `directify₂`, we can now easily show
how to obtain a subcover.

\begin{code}

module Characterization-Of-Compactness (X : Locale 𝓤 𝓥 𝓦) where

 open Some-Lemmas-On-Directification (𝒪 X)
 open PosetNotation (poset-of (𝒪 X))

 finite-subcover-through-directification
  : (U : ⟨ 𝒪 X ⟩)
  → (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
  → (is : List (index S))
  → (U ≤ directify (𝒪 X) S [ is ]) holds
  → Σ (J , β) ꞉ SubFam S ,
     is-Kuratowski-finite J × (U ≤ (⋁[ 𝒪 X ] ⁅  S [ β j ] ∣ j ∶ J ⁆)) holds
 finite-subcover-through-directification U S is p = T , 𝕗 , q
  where
   open PosetReasoning (poset-of (𝒪 X))

   T : SubFam S
   T = (Σ i ꞉ index S , ∥ member i is ∥) , pr₁

   𝕗 : is-Kuratowski-finite (index T)
   𝕗 = list-members-is-Kuratowski-finite is

   † = directify₂-is-equal-to-directify S is ⁻¹

   q : (U ≤ (⋁[ 𝒪 X ] ⁅ S [ T [ x ] ] ∣ x ∶ index T ⁆)) holds
   q = U                                          ≤⟨ p ⟩
       directify (𝒪 X) S [ is ]                   ＝⟨ † ⟩ₚ
       directify₂ S [ is ]                        ＝⟨ {!!} ⟩ₚ
       ⋁[ 𝒪 X ] ⁅ S [ T [ x ] ] ∣ x ∶ index T ⁆   ■

\end{code}

\begin{code}

compact-open-implies-compact-open' : (X : Locale 𝓤 𝓥 𝓦)
                                   → (U : ⟨ 𝒪 X ⟩)
                                   → is-compact-open  X U holds
                                   → is-compact-open' X U holds
compact-open-implies-compact-open' {_} {_} {𝓦} X U κ S q =
 ∥∥-functor † (κ S↑ δ p)
 where
  open PosetReasoning (poset-of (𝒪 X))

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

  † : (Σ is ꞉ index S↑ , (U ≤[ Xₚ ] (S↑ [ is ])) holds)
    → Σ (J , h) ꞉ SubFam S ,
        is-Kuratowski-finite J × (U ≤[ Xₚ ] (⋁[ 𝒪 X ] (J , S [_] ∘ h))) holds
  † (is , r) = {!!}

\end{code}
