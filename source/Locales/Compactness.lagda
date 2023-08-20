Ayberk Tosun, 19 August 2023

The module contains the definitions of

  (1) a compact open of a locale, and
  (2) a compact locale.

These used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Base
open import UF.Subsingletons
open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan

module Locales.Compactness (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                          where

open import Locales.Frame    pt fe
open import Locales.WayBelow pt fe

open Locale

\end{code}

An open `U : 𝒪(X)` of a locale `X` is called compact if it is way below itself.

\begin{code}

is-compact-open : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open X U = U ≪[ 𝒪 X ] U

\end{code}

A locale `X` is called compact if its top element is compact.

\begin{code}

is-compact : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact X = is-compact-open X 𝟏[ 𝒪 X ]

\end{code}
