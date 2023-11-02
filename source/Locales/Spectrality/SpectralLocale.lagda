Ayberk Tosun, 19 August 2023

The module contains the definition of a spectral locale.

This used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

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
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import UF.Logic

module Locales.Spectrality.SpectralLocale (pt : propositional-truncations-exist)
                                          (fe : Fun-Ext) where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe

open PropositionalTruncation pt

open AllCombinators pt fe

open Locale

\end{code}

The following predicate expresses what it means for a locale's compact opens to
be closed under binary meets.

\begin{code}

compacts-of-[_]-are-closed-under-binary-meets : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
compacts-of-[ X ]-are-closed-under-binary-meets =
 let
  _∧ₓ_ = meet-of (𝒪 X)
 in
  Ɐ K₁ ꞉ ⟨ 𝒪 X ⟩ , Ɐ K₂ ꞉ ⟨ 𝒪 X ⟩ ,
   is-compact-open X K₁ ⇒ is-compact-open X K₂ ⇒ is-compact-open X (K₁ ∧ₓ K₂)

\end{code}

Now we express closure under finite meets, which amounts to closure under binary
meets combined with the empty meet (i.e. the top element) being compact.

\begin{code}

compacts-of-[_]-are-closed-under-finite-meets : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
compacts-of-[ X ]-are-closed-under-finite-meets =
 is-compact X ∧ compacts-of-[ X ]-are-closed-under-binary-meets

\end{code}

The following predicate expresses the property of a given family to consist of
compact opens i.e. all the opens it gives being compact opens.

\begin{code}

consists-of-compact-opens : (X : Locale 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
consists-of-compact-opens X S = Ɐ i ꞉ index S , is-compact-open X (S [ i ])

\end{code}

We are now ready to define the notion of a spectral locale:

\begin{code}

has-a-directed-cover-of-compact-opens : (X : Locale 𝓤 𝓥 𝓦) (U : ⟨ 𝒪 X ⟩)
                                      → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
has-a-directed-cover-of-compact-opens {_} {_} {𝓦} X U =
 Ǝ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ , consists-of-compact-opens X S holds
                     × is-directed (𝒪 X) S holds
                     × (U ＝ ⋁[ 𝒪 X ] S)

is-spectral : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectral {_} {_} {𝓦} X = ⦅𝟏⦆ ∧ ⦅𝟐⦆
 where
  ⦅𝟏⦆ = compacts-of-[ X ]-are-closed-under-finite-meets
  ⦅𝟐⦆ = Ɐ U ꞉ ⟨ 𝒪 X ⟩ , has-a-directed-cover-of-compact-opens X U

\end{code}

Spectral locales are compact:

\begin{code}

spectral-locales-are-compact : (X : Locale 𝓤 𝓥 𝓦)
                             → (is-spectral X ⇒ is-compact X) holds
spectral-locales-are-compact X ((κ , _) , _) = κ

\end{code}

We define a couple of projections of the components of being a spectral locale.

We denote by `binary-coherence` the fact that that the compact opens are closed
under binary meets.

\begin{code}

binary-coherence : (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral X holds) (K₁ K₂ : ⟨ 𝒪 X ⟩)
                 → (is-compact-open X K₁
                 ⇒ is-compact-open X K₂
                 ⇒ is-compact-open X (K₁ ∧[ 𝒪 X ] K₂)) holds
binary-coherence X σ = pr₂ (pr₁ σ)

\end{code}

The fact that the top open is compact is denoted `spectral-implies-compact`.

\begin{code}

spectral-implies-compact : (X : Locale 𝓤 𝓥 𝓦) (σ : is-spectral X holds)
                         → is-compact-open X 𝟏[ 𝒪 X ] holds
spectral-implies-compact X σ = pr₁ (pr₁ σ)

\end{code}
