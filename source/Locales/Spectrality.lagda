Ayberk Tosun, 19 August 2023

The module contains the definition of a spectral locale.

This used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])
open import MLTT.Pi
open import Slice.Family
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Logic

module Locales.Spectrality (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                          where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe

open AllCombinators pt fe

open Locale

\end{code}

The following predicate expresses what it means for a locale's compact opens to
be closed under binary meets.

\begin{code}

compacts-of-[_]-are-closed-under-binary-meets : (X : Locale 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
compacts-of-[ X ]-are-closed-under-binary-meets =
 let
  _∧ₓ_ = meet-of (𝒪 X)
 in
  Ɐ K₁ ꞉ ⟨ 𝒪 X ⟩ , Ɐ K₂ ꞉ ⟨ 𝒪 X ⟩ ,
   is-compact-open X K₁ ⇒ is-compact-open X K₂ ⇒ is-compact-open X (K₁ ∧ₓ K₂)

\end{code}

\begin{code}

compacts-closed-under-finite-meets : (X : Locale 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
compacts-closed-under-finite-meets X =
 is-compact X ∧ compacts-of-[ X ]-are-closed-under-binary-meets

\end{code}

The following predicate expresses the property of a given family to consist of
compact opens i.e. all the opens it gives being compact opens.

\begin{code}

consists-of-compact-opens : (X : Locale 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
consists-of-compact-opens X U = Ɐ i ꞉ index U , is-compact-open X (U [ i ])

\end{code}

We are now ready to define the notion of a spectral locale:

\begin{code}

is-spectral : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectral {_} {_} {𝓦} X = ⦅𝟏⦆ ∧ ⦅𝟐⦆
 where
  ⦅𝟏⦆ = compacts-closed-under-finite-meets X
  ⦅𝟐⦆ = Ɐ U ꞉ ⟨ 𝒪 X ⟩ ,
         Ǝ S ꞉ (Fam 𝓦 ⟨ 𝒪 X ⟩) ,
          consists-of-compact-opens X S holds × (U ＝ ⋁[ 𝒪 X ] S)

\end{code}
