Ayberk Tosun, 19 August 2023

The module contains the definitions of

  (1) a compact open of a locale, and
  (2) a compact locale.

These used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import UF.Base
open import UF.Subsingletons
open import UF.PropTrunc
open import UF.FunExt
open import MLTT.Spartan
open import UF.SubtypeClassifier

module Locales.Compactness (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                          where

open import Locales.Frame     pt fe
open import Locales.WayBelowRelation.Definition  pt fe
open import UF.Logic
open import Slice.Family

open PropositionalTruncation pt
open Existential pt

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

\section{Properties of compactness}

\begin{code}

𝟎-is-compact : (X : Locale 𝓤 𝓥 𝓦) → is-compact-open X 𝟎[ 𝒪 X ] holds
𝟎-is-compact X S (∣i∣ , _) p = ∥∥-rec ∃-is-prop † ∣i∣
 where
  † : index S → ∃ i ꞉ index S , (𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] S [ i ]) holds
  † i = ∣ i , 𝟎-is-bottom (𝒪 X) (S [ i ]) ∣

\end{code}

The binary join of two compact opens is compact.

\begin{code}

compact-opens-are-closed-under-∨ : (X : Locale 𝓤 𝓥 𝓦) (K₁ K₂ : ⟨ 𝒪 X ⟩)
                                 → is-compact-open X K₁ holds
                                 → is-compact-open X K₂ holds
                                 → is-compact-open X (K₁ ∨[ 𝒪 X ] K₂) holds
compact-opens-are-closed-under-∨ X U V κ₁ κ₂ S δ p =
 ∥∥-rec₂ ∃-is-prop † (κ₁ S δ φ) (κ₂ S δ ψ)
  where
   open PosetNotation  (poset-of (𝒪 X)) using (_≤_)
   open PosetReasoning (poset-of (𝒪 X))

   † : Σ i₁ ꞉ index S , (U ≤[ poset-of (𝒪 X) ] S [ i₁ ]) holds
     → Σ i₂ ꞉ index S , (V ≤[ poset-of (𝒪 X) ] S [ i₂ ]) holds
     → ∃ i₃ ꞉ index S  , ((U ∨[ 𝒪 X ] V) ≤ S [ i₃ ]) holds
   † (i₁ , p₁) (i₂ , p₂) = ∥∥-rec ∃-is-prop ‡ (pr₂ δ i₁ i₂)
    where
     ‡ : Σ i₃ ꞉ index S , (S [ i₁ ] ≤ S [ i₃ ]) holds
                        × (S [ i₂ ] ≤ S [ i₃ ]) holds
       → ∃ i₃ ꞉ index S  , ((U ∨[ 𝒪 X ] V) ≤ S [ i₃ ]) holds
     ‡ (i₃ , q , r) = ∣ i₃ , ∨[ 𝒪 X ]-least ♠ ♣ ∣
      where
       ♠ : (U ≤[ poset-of (𝒪 X) ] (S [ i₃ ])) holds
       ♠ = U ≤⟨ p₁ ⟩ S [ i₁ ] ≤⟨ q ⟩ S [ i₃ ] ■

       ♣ : (V ≤[ poset-of (𝒪 X) ] (S [ i₃ ])) holds
       ♣ = V ≤⟨ p₂ ⟩ S [ i₂ ] ≤⟨ r ⟩ S [ i₃ ] ■

   φ : (U ≤ (⋁[ 𝒪 X ] S)) holds
   φ = U ≤⟨ ∨[ 𝒪 X ]-upper₁ U V ⟩ U ∨[ 𝒪 X ] V ≤⟨ p ⟩ ⋁[ 𝒪 X ] S ■

   ψ : (V ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
   ψ = V ≤⟨ ∨[ 𝒪 X ]-upper₂ U V ⟩ U ∨[ 𝒪 X ] V ≤⟨ p ⟩ ⋁[ 𝒪 X ] S ■

\end{code}
