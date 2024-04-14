--------------------------------------------------------------------------------
title:          SIP for frames
author:         Ayberk Tosun
date-started:   2024-04-14
--------------------------------------------------------------------------------

Originally proved in `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.SIP.Frame
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale
open import Slice.Family
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.Logic
open import UF.Retracts
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open sip

\end{code}

\begin{code}

module SIP-For-Frames (F G : Frame (𝓤 ⁺) 𝓤 𝓤) where

\end{code}

\begin{code}

 open FrameIsomorphisms

 frame-sns-data : SNS (frame-structure 𝓤 𝓤) (𝓤 ⁺)
 frame-sns-data = ι , ρ , θ
  where
   ι : (F′ G′ : Frame (𝓤 ⁺) 𝓤 𝓤) → sip.⟨ F′ ⟩ ≃ sip.⟨ G′ ⟩ → 𝓤 ⁺  ̇
   ι F′ G′ e = is-homomorphic F′ G′ e holds

   ρ : (L : Frame (𝓤 ⁺) 𝓤 𝓤) → ι L L (≃-refl sip.⟨ L ⟩)
   ρ L = 𝔦𝔡-is-frame-homomorphism L , 𝔦𝔡-is-frame-homomorphism L

   h : {!!}
   h = {!!}

   θ : {X : 𝓤 ⁺  ̇} (str₁ str₂ : frame-structure 𝓤 𝓤 X)
     → is-equiv (canonical-map ι ρ str₁ str₂)
   θ {X} str₁ str₂ = {!!}

\end{code}
