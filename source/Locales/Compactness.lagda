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
open import UF.SubtypeClassifier

module Locales.Compactness (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                          where

open import Locales.Frame       pt fe
open import Locales.WayBelow    pt fe
open import Slice.Family

open Locale

\end{code}

An open `U : 𝒪(X)` of a locale `X` is called compact if it is way below itself.

\begin{code}

is-compact-open : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open X U = U ≪[ 𝒪 X ] U

\end{code}

A locale `X` is called compact if its top element `𝟏` is compact.

\begin{code}

is-compact : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact X = is-compact-open X 𝟏[ 𝒪 X ]

\end{code}

We also define the type `𝒦 X` expressing the type of compact opens of a locale
`X`.

\begin{code}

𝒦 : Locale 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
𝒦 X = Σ U ꞉ ⟨ 𝒪 X ⟩ , is-compact-open X U holds

\end{code}

Using this, we could define a family giving the compact opens of a locale `X`:

\begin{code}

ℬ-compact : (X : Locale 𝓤 𝓥 𝓦) → Fam (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ⟨ 𝒪 X ⟩
ℬ-compact X = 𝒦 X , pr₁

\end{code}

but the index of this family lives in `𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺`. This is to say that, if one
starts with a large and locally small locale, the resulting family would live in
`𝓤 ⁺` which means it would be *too big*.

\begin{code}

ℬ-compact₀ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Fam (𝓤 ⁺) ⟨ 𝒪 X ⟩
ℬ-compact₀ = ℬ-compact

\end{code}
