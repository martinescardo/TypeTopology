--------------------------------------------------------------------------------
title:          SIP for distributive lattices
author:         Ayberk Tosun
date-started:   2024-05-16
--------------------------------------------------------------------------------

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.UA-FunExt
open import UF.Univalence
open import UF.Subsingletons

module Locales.SIP.DistributiveLatticeSIP
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
open import Locales.Frame pt fe
open import Slice.Family
open import UF.Base
open import UF.Equiv
open import UF.Logic
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open sip hiding (⟨_⟩)

\end{code}

\begin{code}

module SIP-For-Distributive-Lattices {A : 𝓤  ̇} where

\end{code}
