--------------------------------------------------------------------------------
title:          Properties of the locale of spectra
author:         Ayberk Tosun
date-started:   2024-03-01
--------------------------------------------------------------------------------

We define the locale of spectra over a distributive lattice `L`, the defining
frame of which is the frame of ideals over `L`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DistributiveLattice.LocaleOfSpectra-Properties
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Ideal-Properties pt fe pe
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open Locale
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work with a fixed distributive lattice `L` in this module.

\begin{code}

module Spectrality (L : DistributiveLattice 𝓤) where

 open DefnOfFrameOfIdeal  L
 open DistributiveLattice L renaming (X-is-set to σ)
 open IdealNotation L
 open IdealProperties L

\end{code}

We abbreviate `locale-of-spectra` to `spec-L`.

\begin{code}

 spec-L : Locale (𝓤 ⁺) 𝓤 𝓤
 spec-L = locale-of-spectra

\end{code}

The locale of spectra of is a compact locale.

\begin{code}

 locale-of-spectra-is-compact : is-compact spec-L holds
 locale-of-spectra-is-compact S δ p =
  ∥∥-rec ∃-is-prop † (p 𝟏 (𝟏ᵈ-is-top L 𝟏))
   where
    † : Σ xs ꞉ List X , xs ◁ S × (𝟏 ＝ join-listᵈ L xs)
      → ∃ i ꞉ index S , (𝟏[ 𝒪 spec-L ] ≤[ poset-of (𝒪 spec-L) ] S [ i ]) holds
    † (xs , c , r) = ∥∥-rec ∃-is-prop ‡ (finite-subcover S xs δ c)
     where
      ‡ : Σ k ꞉ index S , join-listᵈ L xs ∈ⁱ (S [ k ])
        → ∃ i ꞉ index S , (𝟏[ 𝒪 spec-L ] ≤[ poset-of (𝒪 spec-L) ] S [ i ]) holds
      ‡ (k , p) = ∣ k , contains-𝟏-implies-above-𝟏 (S [ k ]) μ ∣
       where
        μ : 𝟏 ∈ⁱ (S [ k ])
        μ = transport (λ - → - ∈ⁱ (S [ k ])) (r ⁻¹) p

\end{code}

Added on 2024-03-13.

\begin{code}

 open PrincipalIdeals L
 open Joins _⊆ᵢ_

 family-of-principal-ideals : (I : Ideal L) → Fam 𝓤 (Ideal L)
 family-of-principal-ideals I =
  ⁅ principal-ideal u ∣ (u , _) ∶ (Σ u ꞉ ∣ L ∣ᵈ , u ∈ⁱ I) ⁆

 original-is-an-upper-bound-of-principal-ideals-within
  : (I : Ideal L)
  → (I is-an-upper-bound-of (family-of-principal-ideals I)) holds
 original-is-an-upper-bound-of-principal-ideals-within I (u , μᵢ) x μ =
  I-is-downward-closed x u μ μᵢ
   where
    open Ideal I using (I-is-downward-closed)

 decomposition₀ : Ideal L → Ideal L
 decomposition₀ I = ⋁[ 𝒪 spec-L ] family-of-principal-ideals I

 an-important-lemma : (I : Ideal L) (xs : List ∣ L ∣ᵈ)
                    → xs ◁ family-of-principal-ideals I
                    → join-listᵈ L xs ∈ⁱ I
 an-important-lemma I xs c = ideals-are-closed-under-finite-joins L I xs γ
  where
   γ : ((x , _) : type-from-list xs) → x ∈ⁱ I
   γ (x , p) = original-is-an-upper-bound-of-principal-ideals-within I (pr₁ β) x (pr₂ β)
    where
     β : Σ i ꞉ (index (family-of-principal-ideals I))
             , x ∈ⁱ (family-of-principal-ideals I [ i ])
     β = covering-lemma (family-of-principal-ideals I) xs c x p

 decomposition-implies-original : (I : Ideal L) {x : ∣ L ∣ᵈ}
                                → (x ∈ᵢ decomposition₀ I ⇒ x ∈ᵢ I) holds
 decomposition-implies-original I {x} μ = ∥∥-rec (holds-is-prop (x ∈ᵢ I)) † μ
  where
   open Ideal I using (I-is-downward-closed; I-is-closed-under-∨; I-contains-𝟎)

   † : (Σ xs ꞉ List ∣ L ∣ᵈ ,
         xs ◁ family-of-principal-ideals I  × (x ＝ join-listᵈ L xs))
     → x ∈ⁱ I
   † (xs , c , q) = transport (λ - → - ∈ⁱ I) (q ⁻¹) (an-important-lemma I xs c)

 original-implies-decomposition : (I : Ideal L) {x : ∣ L ∣ᵈ}
                                → (x ∈ᵢ I ⇒ x ∈ᵢ decomposition₀ I) holds
 original-implies-decomposition I {x} μ =
  ⋁[ 𝒪 spec-L ]-upper
   (family-of-principal-ideals I)
   (x , μ)
   x
   (≤-is-reflexive (poset-ofᵈ L) x)

 ideal-equal-to-decomposition : (I : Ideal L) → I ＝ decomposition₀ I
 ideal-equal-to-decomposition I =
  ideal-extensionality L I (decomposition₀ I) † ‡
   where
    † : (I ⊆ᵢ decomposition₀ I) holds
    † _ = original-implies-decomposition I

    ‡ : (decomposition₀ I ⊆ᵢ I) holds
    ‡ _ = decomposition-implies-original I

 finite-join-of-ideals : List ∣ L ∣ᵈ → Ideal L
 finite-join-of-ideals []       = 𝟎[ 𝒪 spec-L ]
 finite-join-of-ideals (x ∷ xs) =
  principal-ideal x ∨[ 𝒪 spec-L ] finite-join-of-ideals xs

 finite-decomposition : (I : Ideal L)
                      → is-compact-open spec-L I holds
                      → ∃ xs ꞉ List ∣ L ∣ᵈ , I ＝ finite-join-of-ideals xs
 finite-decomposition I κ = {!!}
  where
   c : I ＝ decomposition₀ I
   c = ideal-equal-to-decomposition I

   c₀ : (I ⊆ᵢ decomposition₀ I) holds
   c₀ = {!!}

\end{code}

The compact opens of the locale of spectra are closed under binary meets.

\begin{code}

 -- compacts-of-the-locale-of-spectra-are-closed-under-∧
 --  : compacts-of-[ spec-L ]-are-closed-under-binary-meets holds
 -- compacts-of-the-locale-of-spectra-are-closed-under-∧ K₁ K₂ κ₁ κ₂ = κ
 --  where
 --   κ : is-compact-open spec-L (K₁ ∧[ 𝒪 spec-L ] K₂) holds
 --   κ S δ φ = {!∥∥-rec ? ? ?!}

\end{code}
