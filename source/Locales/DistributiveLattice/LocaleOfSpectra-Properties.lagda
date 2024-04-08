--------------------------------------------------------------------------------
title:          Properties of the locale of spectra
author:         Ayberk Tosun
date-started:   2024-03-01
dates-updated:  [2024-03-27, 2024-04-08]
--------------------------------------------------------------------------------

We define the locale of spectra over a distributive lattice `L`, the defining
frame of which is the frame of ideals over `L`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Size

module Locales.DistributiveLattice.LocaleOfSpectra-Properties
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Ideal-Properties pt fe pe
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Equiv hiding (_■)
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

Every ideal `I` is the join of its principal ideals. We call this join the
_factorization_ of `I` into its join of principal ideals_, and we denote
function implementing this `factorization`.

\begin{code}

 open PrincipalIdeals L
 open Joins _⊆ᵢ_

 factorization : Ideal L → Ideal L
 factorization I = ⋁[ 𝒪 spec-L ] principal-ideals-of I

 ideal-equal-to-factorization : (I : Ideal L) → I ＝ factorization I
 ideal-equal-to-factorization I =
  ⋁[ 𝒪 spec-L ]-unique (principal-ideals-of I) I († , ‡)
   where
    † : (I is-an-upper-bound-of (principal-ideals-of I)) holds
    † = ideal-is-an-upper-bound-of-its-principal-ideals I

    ‡ : ((Iᵤ , _) : upper-bound (principal-ideals-of I)) → I ⊆ᵢ Iᵤ holds
    ‡ (Iᵤ , υ) =
     ideal-is-lowerbound-of-upperbounds-of-its-principal-ideals I Iᵤ υ

\end{code}

The family of principal ideals in an ideal is a directed family.

\begin{code}

 factorization-is-directed : (I : Ideal L)
                           → is-directed (𝒪 spec-L) (principal-ideals-of I) holds
 factorization-is-directed = principal-ideals-of-ideal-form-a-directed-family

\end{code}

Added on 2024-03-27

For every `x : L`, the principal ideal `↓x` is a compact open of the locale of
spectra.

\begin{code}

 principal-ideal-is-compact : (x : ∣ L ∣ᵈ) → is-compact-open spec-L (↓ x) holds
 principal-ideal-is-compact x S δ p = ∥∥-rec ∃-is-prop † μ
  where
   μ : x ∈ᵢ (⋁[ 𝒪 spec-L ] S) holds
   μ = p x (≤ᵈ-is-reflexive L x)

   † : Σ xs ꞉ List X , xs ◁ S × (x ＝ join-listᵈ L xs)
     → ∃ i  ꞉ index S , ↓ x ⊆ᵢ (S [ i ]) holds
   † (xs , q , r′) = ∥∥-rec ∃-is-prop ‡ β
    where
     β : ∃ i ꞉ index S , join-listᵈ L xs ∈ᵢ (S [ i ]) holds
     β = finite-subcover S xs δ q

     ‡ : Σ i ꞉ index S , join-listᵈ L xs ∈ᵢ (S [ i ]) holds
       → ∃ i  ꞉ index S , ↓ x ⊆ᵢ (S [ i ]) holds
     ‡ (i , r) = ∣ i , γ ∣
      where
       open Ideal (S [ i ]) renaming (I-is-downward-closed
                                      to Sᵢ-is-downward-closed)

       γ : (↓ x ⊆ᵢ (S [ i ])) holds
       γ y φ = Sᵢ-is-downward-closed y (join-listᵈ L xs) ϵ r
        where
         ϵ : (y ≤ᵈ[ L ] join-listᵈ L xs) holds
         ϵ = transport (λ - → (y ≤ᵈ[ L ] -) holds) r′ φ

\end{code}

Added on 2024-03-13.

Every ideal has a directed covering family consisting of compact opens.

\begin{code}

 ideal-has-directed-cover-of-compact-opens
  : (I : Ideal L)
  → has-a-directed-cover-of-compact-opens spec-L I holds
 ideal-has-directed-cover-of-compact-opens I = ∣ principal-ideals-of I , κ , δ , eq ∣
  where
   κ : consists-of-compact-opens spec-L (principal-ideals-of I) holds
   κ (x , _) =  principal-ideal-is-compact x

   δ : is-directed (𝒪 spec-L) (principal-ideals-of I) holds
   δ = principal-ideals-of-ideal-form-a-directed-family I

   eq : I ＝ ⋁[ 𝒪 spec-L ] principal-ideals-of I
   eq = ideal-equal-to-factorization I

\end{code}

Added on 2024-04-08.

We have already proved that every principal ideal is compact. We now prove
the converse of this: every compact ideal is the principal ideal on some
element `x` of the distributive lattice `L`.

\begin{code}

 compact-ideal-is-principal : (I : Ideal L)
                            → is-compact-open spec-L I holds
                            → ∃ x ꞉ ∣ L ∣ᵈ , I ＝ principal-ideal x
 compact-ideal-is-principal I κ =
  ∥∥-rec ∃-is-prop γ (κ (principal-ideals-of I) δ c₀)
   where
    c : I ＝ factorization I
    c = ideal-equal-to-factorization I

    c₀ : (I ⊆ᵢ factorization I) holds
    c₀ = reflexivity+ (poset-of (𝒪 spec-L)) c

    c₁ : (factorization I ⊆ᵢ I) holds
    c₁ = reflexivity+ (poset-of (𝒪 spec-L)) (c ⁻¹)

    δ : is-directed (𝒪 spec-L) (principal-ideals-of I) holds
    δ = factorization-is-directed I

    γ : (Σ (x , _) ꞉ index (principal-ideals-of I) , (I ⊆ᵢ ↓ x) holds)
      → ∃ x ꞉ ∣ L ∣ᵈ , I ＝ ↓ x
    γ ((x , p) , φ) = ∣ x , ≤-is-antisymmetric (poset-of (𝒪 spec-L)) q₁ q₂ ∣
     where
      open Ideal I using (I-is-downward-closed)

      q₁ : I ⊆ᵢ principal-ideal x holds
      q₁ = φ

      q₂ : principal-ideal x ⊆ᵢ I holds
      q₂ y μ = I-is-downward-closed y x μ p

\end{code}

Added on 2024-04-08.

The map `↓(-) : L → Idl(L)` preserves meets.

\begin{code}

 principal-ideal-preserves-meets : (x y : ∣ L ∣ᵈ)
                                 → ↓ (x ∧ y) ＝ ↓ x ∧[ 𝒪 spec-L ] ↓ y
 principal-ideal-preserves-meets x y =
  ≤-is-antisymmetric (poset-of (𝒪 spec-L)) † ‡
   where
    open PosetReasoning (poset-ofᵈ L)

    † : (↓ (x ∧ y) ⊆ᵢ (↓ x ∧[ 𝒪 spec-L ] ↓ y)) holds
    † z p = †₁ , †₂
     where
      †₁ : (z ≤ᵈ[ L ] x) holds
      †₁ = z ≤⟨ p ⟩ x ∧ y ≤⟨ ∧-is-a-lower-bound₁ L x y ⟩ x ■

      †₂ : (z ≤ᵈ[ L ] y) holds
      †₂ = z ≤⟨ p ⟩ x ∧ y ≤⟨ ∧-is-a-lower-bound₂ L x y ⟩ y ■

    ‡ : ((↓ x ∧[ 𝒪 spec-L ] ↓ y) ⊆ᵢ ↓ (x ∧ y)) holds
    ‡ = ∧-is-greatest L x y

\end{code}

Added on 2024-04-08.

The compact ideals form a directed basis for the locale of spectra.

\begin{code}

 𝒦-forms-a-directed-cover : (I : Ideal L)
                          → has-a-directed-cover-of-compact-opens spec-L I holds
 𝒦-forms-a-directed-cover I = ∣ principal-ideals-of I , ψ , δ , c ∣
  where
   ψ : consists-of-compact-opens spec-L (principal-ideals-of I) holds
   ψ (x , _) = principal-ideal-is-compact x

   δ : is-directed (𝒪 spec-L) (principal-ideals-of I) holds
   δ = factorization-is-directed I

   c : I ＝ ⋁[ 𝒪 spec-L ] principal-ideals-of I
   c = ideal-equal-to-factorization I

\end{code}

Added on 2024-04-08.

The binary meet of two compact ideals is compact.

\begin{code}

 compacts-of-the-locale-of-spectra-are-closed-under-∧
  : compacts-of-[ spec-L ]-are-closed-under-binary-meets holds
 compacts-of-the-locale-of-spectra-are-closed-under-∧ K₁ K₂ κ₁ κ₂ = κ
  where
   ι₁ : ∃ x₁ ꞉ ∣ L ∣ᵈ , K₁ ＝ ↓ x₁
   ι₁ = compact-ideal-is-principal K₁ κ₁

   ι₂ : ∃ x₂ ꞉ ∣ L ∣ᵈ , K₂ ＝ ↓ x₂
   ι₂ = compact-ideal-is-principal K₂ κ₂

   κ : is-compact-open spec-L (K₁ ∧[ 𝒪 spec-L ] K₂) holds
   κ =
    ∥∥-rec₂ (holds-is-prop (is-compact-open spec-L (K₁ ∧[ 𝒪 spec-L ] K₂))) † ι₁ ι₂
     where
      † : Σ x₁ ꞉ ∣ L ∣ᵈ , K₁ ＝ ↓ x₁
        → Σ x₂ ꞉ ∣ L ∣ᵈ , K₂ ＝ ↓ x₂
        → is-compact-open spec-L (K₁ ∧[ 𝒪 spec-L ] K₂) holds
      † (x₁ , p₁) (x₂ , p₂) =
       transport (λ - → is-compact-open spec-L - holds) (q ⁻¹) ‡
        where
         q : K₁ ∧[ 𝒪 spec-L ] K₂ ＝ ↓ (x₁ ∧ x₂)
         q = K₁ ∧[ 𝒪 spec-L ] K₂       ＝⟨ Ⅰ ⟩
             ↓ x₁ ∧[ 𝒪 spec-L ] K₂     ＝⟨ Ⅱ ⟩
             ↓ x₁ ∧[ 𝒪 spec-L ] ↓ x₂   ＝⟨ Ⅲ ⟩
             ↓ (x₁ ∧ x₂)               ∎
              where
               Ⅰ = ap (λ - → - ∧[ 𝒪 spec-L ] K₂) p₁
               Ⅱ = ap (λ - → ↓ x₁ ∧[ 𝒪 spec-L ] -) p₂
               Ⅲ = principal-ideal-preserves-meets x₁ x₂ ⁻¹

         ‡ : is-compact-open spec-L (↓ (x₁ ∧ x₂)) holds
         ‡ = principal-ideal-is-compact (x₁ ∧ x₂)

\end{code}

Added on 2024-04-08.

Finally, we package everything up into a proof that the locale of spectra is a
spectral locale.

\begin{code}

 spec-L-is-spectral : is-spectral spec-L holds
 spec-L-is-spectral = (κ , ν) , 𝒦-forms-a-directed-cover
  where
   κ : is-compact spec-L holds
   κ = locale-of-spectra-is-compact

   ν : compacts-of-[ spec-L ]-are-closed-under-binary-meets holds
   ν = compacts-of-the-locale-of-spectra-are-closed-under-∧

\end{code}

Furthermore, the type of compact ideals is small.

\begin{code}

 ↓ₖ_ : ∣ L ∣ᵈ → 𝒦 spec-L
 ↓ₖ_ x = ↓ x , principal-ideal-is-compact x

 r : 𝒦 spec-L → ∣ L ∣ᵈ
 r = {!!}

 compact-ideals-equivalent-to-L : ∣ L ∣ᵈ ≃ 𝒦 spec-L
 compact-ideals-equivalent-to-L = ↓ₖ_ , (r , {!!}) , {!!}

 spec-L-has-small-𝒦 : has-small-𝒦 spec-L
 spec-L-has-small-𝒦 = ∣ L ∣ᵈ , compact-ideals-equivalent-to-L

\end{code}
