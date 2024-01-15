Ayberk Tosun, 19 August 2023

The module contains the definition of the way below relation.

This used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan
open import UF.Logic
open import UF.SubtypeClassifier
open import Slice.Family

module Locales.WayBelowRelation.Definition (pt : propositional-truncations-exist)
                                           (fe : Fun-Ext) where

open import Locales.Frame pt fe

open AllCombinators pt fe

\end{code}

The way below relation.

\begin{code}

way-below : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
way-below {𝓤 = 𝓤} {𝓦 = 𝓦} F U V =
 Ɐ S ꞉ Fam 𝓦 ⟨ F ⟩ , is-directed F S ⇒
  V ≤ (⋁[ F ] S) ⇒ (Ǝ i ꞉ index S , (U ≤ S [ i ]) holds)
   where
    open PosetNotation (poset-of F) using (_≤_)

\end{code}

Given a frame `F`, `_≪[ F ]_` denotes its way below relation.

\begin{code}

infix 5 way-below

syntax way-below F U V = U ≪[ F ] V

\end{code}
