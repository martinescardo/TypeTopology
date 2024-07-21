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

It is easy to show that this implies the standdard definition of compactness,
but we need a bit of preparation first.

Given a family `S`, we denote by `family-of-lists S` the family of families
of lists of `S`.

\begin{code}

family-of-lists : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 (Fam 𝓦 ⟨ F ⟩)
family-of-lists {𝓤} {𝓥} {𝓦} F S = List (index S) , h
 where
  h : List (index S) → Fam 𝓦 ⟨ F ⟩
  h is = (Σ i ꞉ index S , member i is) , S [_] ∘ pr₁

\end{code}

Using this, we can give an alternative definition of the directification of
a family:

\begin{code}

directify₂ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
directify₂ F S = ⁅ ⋁[ F ] T ∣ T ε family-of-lists F S ⁆

\end{code}

As expected, `directify₂` is equal to `directify`.

\begin{code}

directify₂-is-equal-to-directify
 : (F : Frame 𝓤 𝓥 𝓦)
 → (S : Fam 𝓦 ⟨ F ⟩)
 → directify₂ F S [_] ∼ directify F S [_]

directify₂-is-equal-to-directify F S [] =
 directify₂ F S [ [] ]   ＝⟨ Ⅰ    ⟩
 𝟎[ F ]                  ＝⟨ refl ⟩
 directify  F S [ [] ]   ∎
  where
   † : (directify₂ F S [ [] ] ≤[ poset-of F ] 𝟎[ F ]) holds
   † = ⋁[ F ]-least (family-of-lists F S [ [] ]) (_ , λ ())

   Ⅰ = only-𝟎-is-below-𝟎 F (directify₂ F S [ [] ]) †

directify₂-is-equal-to-directify F S (i ∷ is) =
 directify₂ F S [ i ∷ is ]              ＝⟨ Ⅰ    ⟩
 S [ i ] ∨[ F ] directify₂ F S [ is ]   ＝⟨ Ⅱ    ⟩
 S [ i ] ∨[ F ] directify  F S [ is ]   ＝⟨ refl ⟩
 directify F S [ i ∷ is ]               ∎
  where
   IH = directify₂-is-equal-to-directify F S is

   Ⅱ  = ap (λ - → S [ i ] ∨[ F ] -) IH
   Ⅰ  = {!!}

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
