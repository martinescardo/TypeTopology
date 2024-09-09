--------------------------------------------------------------------------------
title:          Properties of continuous maps
author:         Ayberk Tosun
date-started:   2024-04-10
--------------------------------------------------------------------------------

Factored out from the `Locales.Frame` module on 2024-04-10.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc

module Locales.ContinuousMap.Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.ContinuousMap.Definition pt fe
open import UF.Logic

open AllCombinators pt fe
open ContinuousMaps
open FrameHomomorphismProperties
open Locale

\end{code}

Lemma for showing equality of continuous maps.

\begin{code}

to-continuous-map-＝ : (X : Locale 𝓤 𝓥 𝓦) (Y : Locale 𝓤' 𝓥' 𝓦) (f g : X ─c→ Y)
                     →
                       let
                        open ContinuousMapNotation X Y
                       in
                       ((V : ⟨ 𝒪 Y ⟩) → f ⋆∙ V ＝ g ⋆∙ V)
                     → f ＝ g
to-continuous-map-＝ X Y f g φ =
 to-frame-homomorphism-＝ (𝒪 Y) (𝒪 X) (_⋆ f) (_⋆ g) φ
  where
   open ContinuousMapNotation X Y

\end{code}
