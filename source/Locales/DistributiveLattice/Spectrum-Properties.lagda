---
title:          Properties of the locale of spectra
author:         Ayberk Tosun
date-started:   2024-03-01
dates-updated:  [2024-03-27, 2024-04-08, 2024-04-09, 2024-06-05]
---

We define the spectrum locale over a distributive lattice `L`, the defining
frame of which is the frame of ideals over `L`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Size

module Locales.DistributiveLattice.Spectrum-Properties
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import Locales.Compactness pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Ideal-Properties pt fe pe
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.DistributiveLattice.Spectrum fe pe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Classifiers
open import UF.Equiv renaming (_■ to _𝐐𝐄𝐃)
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Powerset-MultiUniverse hiding (𝕋)
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open Locale
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We work with a fixed distributive 𝓤-lattice `L` in this module.

\begin{code}

module Spectrality (L : DistributiveLattice 𝓤) where

 open DefnOfFrameOfIdeal  L
 open DistributiveLattice L renaming (X-is-set to σ)
 open IdealNotation L
 open IdealProperties L

\end{code}

We abbreviate the `spectrum` of `L` to `spec-L`.

\begin{code}

 private
  spec-L : Locale (𝓤 ⁺) 𝓤 𝓤
  spec-L = spectrum

\end{code}

The locale `spec-L` is a compact locale.

\begin{code}

 spectrum-is-compact : is-compact spec-L holds
 spectrum-is-compact S δ p =
  ∥∥-rec ∃-is-prop † (p 𝟏 (𝟏ᵈ-is-top L 𝟏))
   where
    † : Σ xs ꞉ List X , xs ◁ S × (𝟏 ＝ join-listᵈ L xs)
      → ∃ i ꞉ index S , (𝟏[ 𝒪 spec-L ] ⊆ᵢ (S [ i ])) holds
    † (xs , c , r) = ∥∥-rec ∃-is-prop ‡ (finite-subcover S xs δ c)
     where
      ‡ : Σ k ꞉ index S , join-listᵈ L xs ∈ⁱ (S [ k ])
        → ∃ i ꞉ index S , (𝟏[ 𝒪 spec-L ] ⊆ᵢ (S [ i ])) holds
      ‡ (k , p) = ∣ k , contains-𝟏-implies-above-𝟏 (S [ k ]) μ ∣
       where
        μ : 𝟏 ∈ⁱ (S [ k ])
        μ = transport (λ - → - ∈ⁱ (S [ k ])) (r ⁻¹) p

\end{code}

Added on 2024-03-13.

Every ideal `I` is the join of its principal ideals. We call this join the
_factorization_ of `I` into its join of principal ideals, and we denote by
`factorization` the function implementing this.

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

Added on 2024-06-05.

\begin{code}

 ↓ₖ_ : ∣ L ∣ᵈ → Σ I ꞉ Ideal L , (is-compact-open spec-L I holds)
 ↓ₖ_ x = ↓ x , principal-ideal-is-compact x

\end{code}

End of addition.

Added on 2024-03-13.

Every ideal has a directed covering family consisting of compact opens.

\begin{code}

 ideal-has-directed-cover-of-compact-opens
  : (I : Ideal L)
  → has-a-directed-cover-of-compact-opens spec-L I holds
 ideal-has-directed-cover-of-compact-opens I =
  ∣ principal-ideals-of I , κ , δ , eq ∣
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

      q₁ : I ⊆ᵢ ↓ x holds
      q₁ = φ

      q₂ : ↓ x ⊆ᵢ I holds
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

Added on 2024-06-05.

This has probably been written down somewhere else before.

\begin{code}

 principal-ideal-preserves-top : ↓ 𝟏 ＝ 𝟏[ 𝒪 spec-L ]
 principal-ideal-preserves-top = only-𝟏-is-above-𝟏 (𝒪 spec-L) (↓ 𝟏) (λ _ → id)

 principal-ideal-preserves-bottom : ↓ 𝟎 ＝ 𝟎[ 𝒪 spec-L ]
 principal-ideal-preserves-bottom = only-𝟎-is-below-𝟎 (𝒪 spec-L) (↓ 𝟎) †
  where
   † : (↓ 𝟎 ≤[ poset-of (𝒪 spec-L) ] 𝟎[ 𝒪 spectrum ]) holds
   † x μ = transport (λ - → - ∈ⁱ 𝟎[ 𝒪 spectrum ]) (p ⁻¹) ideal-𝟎-contains-𝟎
    where
     open Ideal 𝟎[ 𝒪 spectrum ] renaming (I-contains-𝟎 to ideal-𝟎-contains-𝟎)

     p : x ＝ 𝟎
     p = only-𝟎-is-below-𝟎ᵈ L x μ

\end{code}

End of addition

Added on 2024-04-08.

The binary meet of two compact ideals is compact.

\begin{code}

 compacts-of-the-spectrum-are-closed-under-∧
  : compacts-of-[ spec-L ]-are-closed-under-binary-meets holds
 compacts-of-the-spectrum-are-closed-under-∧ K₁ K₂ κ₁ κ₂ = κ
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

Finally, we package everything up into a proof that the spectrum locale is
spectral.

\begin{code}

 spec-L-is-spectral : is-spectral spec-L holds
 spec-L-is-spectral = (κ , ν) , ideal-has-directed-cover-of-compact-opens
  where
   κ : is-compact spec-L holds
   κ = spectrum-is-compact

   ν : compacts-of-[ spec-L ]-are-closed-under-binary-meets holds
   ν = compacts-of-the-spectrum-are-closed-under-∧

\end{code}

Everything after this line has been added on 2024-04-09.

To show that the type of compact ideals is small, we directly construct the
intensional specified basis for `Idl(L)` given by the family `↓(-) : L → Idl(L)`.

\begin{code}

 ℬ-spec : Fam 𝓤 ⟨ 𝒪 spec-L ⟩
 ℬ-spec = ∣ L ∣ᵈ , principal-ideal

 open classifier-single-universe

 ℬ-spec-is-directed-basis : directed-basis-forᴰ (𝒪 spec-L) ℬ-spec
 ℬ-spec-is-directed-basis ℐ = 𝕋 𝓤 ∣ L ∣ᵈ (_∈ⁱ ℐ) , † , 𝒹
  where
   c : ℐ ＝ ⋁[ 𝒪 spec-L ] ⁅ ↓ x ∣ x ε 𝕋 𝓤 ∣ L ∣ᵈ (_∈ⁱ ℐ) ⁆
   c = ideal-equal-to-factorization ℐ

   † : (ℐ is-lub-of ⁅ ↓ x ∣ x ε 𝕋 𝓤 ∣ L ∣ᵈ (_∈ⁱ ℐ) ⁆) holds
   † = transport
        (λ - → (- is-lub-of ⁅ ↓ x ∣ x ε 𝕋 𝓤 ∣ L ∣ᵈ (_∈ⁱ ℐ) ⁆) holds)
        (c ⁻¹)
        (⋁[ 𝒪 spec-L ]-upper _ , ⋁[ 𝒪 spec-L ]-least _)

   𝒹 : is-directed (𝒪 spec-L) ⁅ ↓ x ∣ x ε (𝕋 𝓤 ∣ L ∣ᵈ (_∈ⁱ ℐ)) ⁆ holds
   𝒹 = factorization-is-directed ℐ

 ℬ-spec-is-basis : basis-forᴰ (𝒪 spec-L) ℬ-spec
 ℬ-spec-is-basis =
  directed-basis-is-basis (𝒪 spec-L) ℬ-spec ℬ-spec-is-directed-basis

\end{code}

We denote by `𝒦-fam` the family corresponding to the subset of compact opens.

\begin{code}

 𝒦-fam : Fam (𝓤 ⁺) ⟨ 𝒪 spec-L ⟩
 𝒦-fam = 𝕋 (𝓤 ⁺) ⟨ 𝒪 spec-L ⟩ (_holds ∘ is-compact-open spec-L)

\end{code}

We know that the image of `↓(-) : L → Idl(L)` is equivalent to type of compact
opens of `spec-L`.

\begin{code}

 image-↓-equiv-to-𝒦 : image principal-ideal ≃ 𝒦 spec-L
 image-↓-equiv-to-𝒦 = basic-iso-to-𝒦
                       spec-L
                       (ℬ-spec , ℬ-spec-is-directed-basis)
                       principal-ideal-is-compact

\end{code}

We also know that the image of `↓(-)` is a 𝓤-small type.

\begin{code}

 image-of-↓-is-small : (image principal-ideal) is 𝓤 small
 image-of-↓-is-small =
  basic-is-small spec-L (ℬ-spec , ℬ-spec-is-directed-basis) γ
   where
    open PosetNotation (poset-of (𝒪 spec-L))

    γ : ⟨ 𝒪 spec-L ⟩ is-locally 𝓤 small
    γ I J = (I ≣ J) holds , s , (r , †) , (r , ‡)
     where
      s : (I ≣ J) holds → I ＝ J
      s (p₁ , p₂) = ≤-is-antisymmetric (poset-of (𝒪 spec-L)) p₁ p₂

      r : I ＝ J → (I ≣ J) holds
      r p = transport (λ - → (- ≣ J) holds) (p ⁻¹) (≣-is-reflexive poset-of-ideals J)

      † : s ∘ r ∼ id
      † p = carrier-of-[ poset-of-ideals ]-is-set (s (r p)) p

      ‡ : r ∘ s ∼ id
      ‡ p = holds-is-prop (I ≣ J) (r (s p)) p

\end{code}

We use the superscript `(-)⁻` to denote the small copy of the type `image ↓(-)`.

\begin{code}

 image-↓⁻ : 𝓤  ̇
 image-↓⁻ = resized (image principal-ideal) image-of-↓-is-small

\end{code}

From the previous two equivalences, we can conclude that the type of compact
opens of `spec-L` is equivalent to `image-↓⁻`.

\begin{code}

 image-↓⁻-equiv-to-𝒦 : image-↓⁻ ≃ 𝒦 spec-L
 image-↓⁻-equiv-to-𝒦 = image-↓⁻               ≃⟨ Ⅰ ⟩
                       image principal-ideal  ≃⟨ Ⅱ ⟩
                       𝒦 spec-L               𝐐𝐄𝐃
                        where
                         Ⅰ = resizing-condition image-of-↓-is-small
                         Ⅱ = image-↓-equiv-to-𝒦

\end{code}

This means that `𝒦(spec-L)` is 𝓤-small.

\begin{code}

 spec-L-has-small-𝒦 : has-small-𝒦 spec-L
 spec-L-has-small-𝒦 = image-↓⁻ , image-↓⁻-equiv-to-𝒦

\end{code}
