Ayberk Tosun, 13 September 2023

The module contains the definition of a spectral locale.

This used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.FunExt
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.SubtypeClassifier

module Locales.Spectrality.SpectralMap (pt : propositional-truncations-exist)
                                       (fe : Fun-Ext) where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe

open import UF.Logic
open AllCombinators pt fe

open Locale

\end{code}

Definition of the notion of a spectral map.

\begin{code}

is-spectral-map : (Y : Locale 𝓤 𝓥 𝓥) (X : Locale 𝓤' 𝓥 𝓥)
                → (X ─c→ Y) → Ω (𝓤 ⊔ 𝓤' ⊔ 𝓥 ⁺)
is-spectral-map Y X (f , _) =
 Ɐ K ꞉ ⟨ 𝒪 Y ⟩ , is-compact-open Y K  ⇒ is-compact-open X (f K)

\end{code}
