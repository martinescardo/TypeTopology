Ayberk Tosun, 13 September 2023

The module contains the definition of a spectral locale.

This used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.Spectrality.SpectralMap (pt : propositional-truncations-exist)
                                       (fe : Fun-Ext) where

open import Locales.Compactness pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe
open ContinuousMaps
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale

\end{code}

Definition of the notion of a spectral map.

\begin{code}

is-spectral-map : (Y : Locale 𝓤 𝓥 𝓥) (X : Locale 𝓤' 𝓥 𝓥)
                → (X ─c→ Y) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⁺)
is-spectral-map Y X (f , _) =
 Ɐ K ꞉ ⟨ 𝒪 Y ⟩ , is-compact-open Y K  ⇒ is-compact-open X (f K)

\end{code}

Added on 2024-03-04.

\begin{code}

Spectral-Map : (X : Locale 𝓤 𝓥 𝓥) (Y : Locale 𝓤' 𝓥 𝓥) → (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⁺) ̇
Spectral-Map X Y = Σ f ꞉ X ─c→ Y , is-spectral-map Y X f holds

continuous-map-of : (X : Locale 𝓤 𝓥 𝓥) (Y : Locale 𝓤' 𝓥 𝓥)
                  → Spectral-Map X Y → X ─c→ Y
continuous-map-of X Y (f , _) = f

spectrality-of-spectral-map : (X : Locale 𝓤 𝓥 𝓥) (Y : Locale 𝓤' 𝓥 𝓥)
                            → (fₛ : Spectral-Map X Y)
                            → is-spectral-map Y X (continuous-map-of X Y fₛ) holds
spectrality-of-spectral-map X Y (_ , 𝕤) = 𝕤

syntax Spectral-Map X Y = X ─s→ Y

\end{code}
