--------------------------------------------------------------------------------
title:          Properties of locale homeomorphisms
author:         Ayberk Tosun
date-started:   2024-04-18
--------------------------------------------------------------------------------

Some properties of locale homeomorphisms.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.ContinuousMap.Homeomorphism-Properties
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.Frame pt fe
open import Locales.SIP.FrameSIP ua pt sr
open import Slice.Family
open import UF.Equiv
open import UF.Hedberg
open import UF.Logic
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open Locale

\end{code}

Homeomorphic locales are equal.

\begin{code}

homeomorphic-locales-are-equal : (X Y : Locale (𝓤 ⁺) 𝓤 𝓤) → X ≅c≅ Y → X ＝ Y
homeomorphic-locales-are-equal X Y 𝒽 = to-locale-＝ Y X † ⁻¹
 where
  open FrameIsomorphisms

  r : 𝒪 Y ≅f≅ 𝒪 X
  r = isomorphism-to-isomorphismᵣ
       (𝒪 Y)
       (𝒪 X)
       (isomorphismᵣ-to-isomorphism (𝒪 Y) (𝒪 X) 𝒽)

  † : 𝒪 Y ＝ 𝒪 X
  † = isomorphic-frames-are-equal (𝒪 Y) (𝒪 X) r

\end{code}

Transport lemma for homeomorphic locales.

\begin{code}

≅c≅-transport : (X Y : Locale (𝓤 ⁺) 𝓤 𝓤)
              → (P : Locale (𝓤 ⁺) 𝓤 𝓤 → Ω 𝓣) → X ≅c≅ Y → P X holds → P Y holds
≅c≅-transport X Y P 𝒽 = transport (_holds ∘ P) p
 where
  p : X ＝ Y
  p = homeomorphic-locales-are-equal X Y 𝒽

\end{code}

Added on 2024-05-07.

Being homeomorphic is a symmetric relation.

\begin{code}

≅c-sym : (X Y : Locale (𝓤 ⁺) 𝓤 𝓤) → X ≅c≅ Y → Y ≅c≅ X
≅c-sym X Y 𝒽 =
 record { 𝓈 = 𝓇 ; 𝓇 = 𝓈 ; 𝓇-cancels-𝓈 = 𝓈-cancels-𝓇 ; 𝓈-cancels-𝓇 = 𝓇-cancels-𝓈 }
  where
   open FrameIsomorphisms.Isomorphismᵣ 𝒽

\end{code}
