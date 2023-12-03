\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size

module Locales.Sierpinski-Properties
        (𝓤  : Universe)
        (pe : propext 𝓤)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
        where

open import Locales.Frame pt fe hiding (𝟚)
open import DomainTheory.Lifting.LiftingSet pt fe
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import Slice.Family
open import UF.SubtypeClassifier
open import UF.Subsingletons-Properties
open import Locales.Sierpinski 𝓤 pe pt fe
open import Locales.Spectrality.SpectralLocale
open import Locales.SmallBasis pt fe sr
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤

\end{code}

The Sierpiński locale is spectral.

\begin{code}

open SpectralScottLocaleConstruction {!!}

𝕊-is-spectralᴰ : spectralᴰ 𝕊
𝕊-is-spectralᴰ = {!scott-locale-spectralᴰ!}

\end{code}
