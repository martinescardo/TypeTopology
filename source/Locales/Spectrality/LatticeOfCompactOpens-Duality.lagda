--------------------------------------------------------------------------------
title:          Basics of duality for spectral locales
author:         Ayberk Tosun
date-completed: 2024-05-07
--------------------------------------------------------------------------------

Every spectral locale `X` is homeomorphic to the spectrum of its distributive
lattice `𝒦(X)` of compact opens. We construct a proof of this fact in this
module. The proof is implemented in the function `X-is-homeomorphic-to-spec-𝒦X`.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Spectrality.LatticeOfCompactOpens-Duality
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.AdjointFunctorTheoremForFrames pt fe
open import Locales.Compactness pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameIsomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Properties ua pt sr
open import Locales.DirectedFamily-Poset pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Ideal-Properties pt fe pe
open import Locales.DistributiveLattice.Isomorphism fe pt
open import Locales.DistributiveLattice.LocaleOfSpectra fe pe pt
open import Locales.DistributiveLattice.LocaleOfSpectra-Properties fe pe pt sr
open import Locales.DistributiveLattice.Resizing ua pt sr
open import Locales.Frame pt fe
open import Locales.GaloisConnection pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Slice.Family
open import UF.Classifiers
open import UF.Equiv hiding (_■)
open import UF.Logic
open import UF.Powerset-MultiUniverse hiding (𝕋)
open import UF.SubtypeClassifier

open AllCombinators pt fe hiding (_∨_)
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We fix a large and locally small locale `X`, assumed to be spectral with a small
type of compact opens.

\begin{code}

module 𝒦-Duality (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
                 (σ₀ : is-spectral-with-small-basis ua X holds) where

 open 𝒦-Lattice X σ₀ renaming (𝒦⁻ to 𝒦⁻X)

\end{code}

We define some shorthand notation for convenience.

We denote by `e` the equivalence between `𝒦 X`, the type of compact opens of
`X`, and its small copy which is called `𝒦⁻X`.

\begin{code}

 e : 𝒦⁻X ≃ 𝒦 X
 e = resizing-condition 𝒦⦅X⦆-is-small

 open DistributiveLatticeResizing 𝒦⦅X⦆ 𝒦⁻X (≃-sym e) renaming (Lᶜ to 𝒦-X⁻)

 𝒦⦅X⦆⁻ = 𝒦-X⁻

 open DefnOfFrameOfIdeal 𝒦-X⁻

\end{code}

We denote by `spec-𝒦⁻X` the spectrum of `𝒦⁻X`.

\begin{code}

 spec-𝒦X : Locale (𝓤 ⁺) 𝓤 𝓤
 spec-𝒦X = DefnOfFrameOfIdeal.locale-of-spectra 𝒦-X⁻

\end{code}

The map `ι` below is the inclusion of the compact opens in the small copy `𝒦⁻X`
into `𝒪(X)`.

\begin{code}

 ι : ∣ 𝒦-X⁻ ∣ᵈ → ⟨ 𝒪 X ⟩
 ι K = pr₁ (r K)

 ι-gives-compact-opens : (K : 𝒦⁻X) → is-compact-open X (ι K) holds
 ι-gives-compact-opens K = pr₂ (r K)

\end{code}

This map is quite obviously a frame homomorphism, but writin this fact down
involves some bureaucracy.

\begin{code}

 open Ideal
  hiding (I; I-is-downward-closed)
 open DistributiveLattice 𝒦-X⁻
  using ()
  renaming (𝟎 to 𝟎⁻; 𝟏 to 𝟏⁻; _∨_ to _∨⁻_; _∧_ to _∧⁻_)
 open DistributiveLattice 𝒦⦅X⦆
  using (𝟎; 𝟏; _∨_)
  renaming (_∧_ to _∧L_)

 ι-preserves-𝟎 : ι 𝟎⁻ ＝ 𝟎[ 𝒪 X ]
 ι-preserves-𝟎 = ap pr₁ (inverses-are-sections' e 𝟎)

 ι-preserves-𝟏 : ι 𝟏⁻ ＝ 𝟏[ 𝒪 X ]
 ι-preserves-𝟏 = ap pr₁ (inverses-are-sections' e 𝟏)

 open PosetReasoning (poset-of (𝒪 X))
 open OperationsOnCompactOpens X σ

 ι-preserves-∨ : (K₁ K₂ : 𝒦⁻X)
               → ι (K₁ ∨⁻ K₂) ＝ ι K₁ ∨[ 𝒪 X ] ι K₂
 ι-preserves-∨ K₁ K₂ =
  ιₖ (r (K₁ ∨⁻ K₂))                 ＝⟨ Ⅰ    ⟩
  ιₖ (r K₁ ∨ r K₂)                  ＝⟨ Ⅱ    ⟩
  pr₁ (r K₁) ∨[ 𝒪 X ] pr₁ (r K₂)    ＝⟨ refl ⟩
  ι K₁ ∨[ 𝒪 X ] ι K₂                ∎
   where
    Ⅰ = ap pr₁ (r-preserves-∨ K₁ K₂)
    Ⅱ = ιₖ-preserves-∨ (r K₁) (r K₂)

 ι-preserves-∧ : (K₁ K₂ : 𝒦⁻X) → ι (K₁ ∧⁻ K₂) ＝ ι K₁ ∧[ 𝒪 X ] ι K₂
 ι-preserves-∧ K₁ K₂ =
  ι (K₁ ∧⁻ K₂)         ＝⟨ refl                         ⟩
  pr₁ (r (K₁ ∧⁻ K₂))   ＝⟨ ap pr₁ (r-preserves-∧ K₁ K₂) ⟩
  pr₁ (r K₁ ∧L r K₂)   ＝⟨ ιₖ-preserves-∧ (r K₁) (r K₂) ⟩
  ι K₁ ∧[ 𝒪 X ] ι K₂   ∎

 ι-is-monotone : (K₁ K₂ : 𝒦⁻X)
               → (K₁ ≤ᵈ[ 𝒦-X⁻ ] K₂ ⇒ ι K₁ ≤[ poset-of (𝒪 X) ] ι K₂) holds
 ι-is-monotone K₁ K₂ p = connecting-lemma₃ (𝒪 X) †
  where
   † : ι K₂ ＝ ι K₁ ∨[ 𝒪 X ] ι K₂
   † = ι K₂               ＝⟨ Ⅰ ⟩
       ι (K₁ ∨⁻ K₂)       ＝⟨ Ⅱ ⟩
       ι K₁ ∨[ 𝒪 X ] ι K₂ ∎
        where
         Ⅰ = ap ι (orderᵈ-implies-orderᵈ-∨ 𝒦-X⁻ p ⁻¹)
         Ⅱ = ι-preserves-∨ K₁ K₂

 ιₘ : poset-ofᵈ 𝒦-X⁻ ─m→ poset-of (𝒪 X)
 ιₘ = ι , λ (K₁ , K₂) → ι-is-monotone K₁ K₂

\end{code}

Furthermore, we write down the fact that `ι` is an order embedding.

\begin{code}

 ι-is-order-embedding : (K₁ K₂ : 𝒦⁻X)
                      → (ι K₁ ≤[ poset-of (𝒪 X) ] ι K₂) holds
                      → (K₁ ≤ᵈ[ 𝒦-X⁻ ] K₂) holds
 ι-is-order-embedding K₁ K₂ p =
  s (r K₁ ∧L r K₂)   ＝⟨ Ⅰ ⟩
  s (r K₁)           ＝⟨ Ⅱ ⟩
  K₁                 ∎
   where
    ※ : pr₁ (r K₁) ∧[ 𝒪 X ] pr₁ (r K₂) ＝ ι K₁
    ※ = connecting-lemma₁ (𝒪 X) p ⁻¹

    Ⅰ = ap s (to-𝒦-＝ X _ (pr₂ (r K₁)) ※)
    Ⅱ = inverses-are-retractions' e K₁

\end{code}

Using the map `ι`, we define the map `η` below. This is essentially the
principal ideal map, but goes through the small type `𝒦⁻X` of compact opens.

\begin{code}

 ϕ₀ : ⟨ 𝒪 X ⟩ → 𝓟 𝒦⁻X
 ϕ₀ U = λ c → ι c ≤[ poset-of (𝒪 X) ] U

\end{code}

We now prove that this always gives an ideal.

\begin{code}

 η-contains-𝟎 : (U : ⟨ 𝒪 X ⟩) → 𝟎⁻ ∈ ϕ₀ U
 η-contains-𝟎 U =
  ι 𝟎⁻       ＝⟨ Ⅰ ⟩ₚ
  𝟎[ 𝒪 X ]   ≤⟨ Ⅱ ⟩
  U          ■
   where
    Ⅰ = ι-preserves-𝟎
    Ⅱ = 𝟎-is-bottom (𝒪 X) U

 η-is-downward-closed : (U : ⟨ 𝒪 X ⟩) → is-downward-closed 𝒦-X⁻ (ϕ₀ U) holds
 η-is-downward-closed U K₁ K₂ p μ =
  ιₖ (r K₁)   ≤⟨ Ⅰ ⟩
  ιₖ (r K₂)   ≤⟨ Ⅱ ⟩
  U           ■
   where
    Ⅰ = ι-is-monotone K₁ K₂ p
    Ⅱ = μ

 η-is-closed-under-∨ : (U : ⟨ 𝒪 X ⟩)
                     → is-closed-under-binary-joins 𝒦-X⁻ (ϕ₀ U) holds
 η-is-closed-under-∨ U K₁ K₂ μ₁ μ₂  =
  ι (K₁ ∨⁻ K₂)        ＝⟨ Ⅰ ⟩ₚ
  ι K₁ ∨[ 𝒪 X ] ι K₂  ≤⟨ Ⅱ ⟩
  U                   ■
   where
    Ⅰ = ι-preserves-∨ K₁ K₂
    Ⅱ =  ∨[ 𝒪 X ]-least μ₁ μ₂

\end{code}

We denote by `ϕ` the version of `ϕ₀` packaged up with the proof that it always
gives ideals.

\begin{code}

 ϕ : ⟨ 𝒪 X ⟩ → Ideal 𝒦-X⁻
 ϕ U = record
         { I                    = ϕ₀ U
         ; I-is-inhabited       = ∣ 𝟎⁻ , η-contains-𝟎 U ∣
         ; I-is-downward-closed = η-is-downward-closed U
         ; I-is-closed-under-∨  = η-is-closed-under-∨ U
         }

\end{code}

We can now show that the map `ϕ` preserves finite meets.

\begin{code}

 abstract
  ϕ-preserves-top : ϕ 𝟏[ 𝒪 X ] ＝ 𝟏[ 𝒪 spec-𝒦X ]
  ϕ-preserves-top = only-𝟏-is-above-𝟏 (𝒪 spec-𝒦X) (ϕ 𝟏[ 𝒪 X ]) †
   where
    † : (𝟏[ 𝒪 spec-𝒦X ] ⊆ᵢ ϕ 𝟏[ 𝒪 X ]) holds
    † K _ = 𝟏-is-top (𝒪 X) (ι K)

 open IdealNotation 𝒦-X⁻

 ϕ-preserves-∧ : (U V : ⟨ 𝒪 X ⟩) → ϕ (U ∧[ 𝒪 X ] V) ＝ ϕ U ∧ᵢ ϕ V
 ϕ-preserves-∧ U V = ≤-is-antisymmetric poset-of-ideals † ‡
  where
   † : ϕ (U ∧[ 𝒪 X ] V) ⊆ᵢ (ϕ U ∧ᵢ ϕ V) holds
   † K p = p₁ , p₂
    where
     p₁ : K ∈ⁱ ϕ U
     p₁ = ι K ≤⟨ p ⟩ U ∧[ 𝒪 X ] V ≤⟨ ∧[ 𝒪 X ]-lower₁ U V ⟩ U ■

     p₂ : K ∈ⁱ ϕ V
     p₂ = ι K ≤⟨ p ⟩ U ∧[ 𝒪 X ] V ≤⟨ ∧[ 𝒪 X ]-lower₂ U V ⟩ V ■

   ‡ : (ϕ U ∧ᵢ ϕ V) ⊆ᵢ ϕ (U ∧[ 𝒪 X ] V) holds
   ‡ K (p₁ , p₂) = ∧[ 𝒪 X ]-greatest U V (ι K) p₁ p₂

 ϕ-is-monotone : is-monotonic (poset-of (𝒪 X)) poset-of-ideals ϕ holds
 ϕ-is-monotone (U , V) p = connecting-lemma₂ frame-of-ideals †
  where
   q : U ＝ U ∧[ 𝒪 X ] V
   q = connecting-lemma₁ (𝒪 X) p

   † : ϕ U ＝ ϕ U ∧ᵢ ϕ V
   † = ϕ U              ＝⟨ Ⅰ ⟩
       ϕ (U ∧[ 𝒪 X ] V) ＝⟨ Ⅱ ⟩
       ϕ U ∧ᵢ ϕ V      ∎
        where
         Ⅰ = ap ϕ q
         Ⅱ = ϕ-preserves-∧ U V

 open FrameHomomorphisms

\end{code}

This map also preserves joins, but because we derive this from the fact that it
is an equivalence, we will delay its proof for a bit.

We now construct the opposite direction of the equivalence formed by `ϕ`. This
is simply the map that maps an ideal to its joins `I ↦ ⋁ I`. We denote this by
`join`.

\begin{code}

 open classifier-single-universe 𝓤
 open Directed-Families-On-Posets (poset-ofᵈ 𝒦-X⁻) (poset-of (𝒪 X))
 open IdealProperties 𝒦-X⁻

 𝒦-below : Ideal 𝒦-X⁻ → Fam 𝓤 ⟨ 𝒪 X ⟩
 𝒦-below ℐ = ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ) ⁆

 𝒦-below-is-directed : (ℐ : Ideal 𝒦-X⁻)
                     → is-directed (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ) ⁆ holds
 𝒦-below-is-directed ℐ =
  monotone-image-on-directed-set-is-directed
   ιₘ
   (𝕋 𝒦⁻X (_∈ⁱ ℐ))
   (ideals-are-directed ℐ)
    where
     open Ideal ℐ renaming (I-contains-𝟎 to I-contains-𝟎⁻)

 join : Ideal 𝒦-X⁻  → ⟨ 𝒪 X ⟩
 join ℐ = ⋁[ 𝒪 X ] (𝒦-below ℐ)

\end{code}

The map `join` preserves the top element.

\begin{code}

 join-preserves-top : join 𝟏ᵢ ＝ 𝟏[ 𝒪 X ]
 join-preserves-top = only-𝟏-is-above-𝟏 (𝒪 X) (join 𝟏ᵢ) †
  where
   ‡ : (ι (s 𝟏ₖ) ≤[ poset-of (𝒪 X)] join 𝟏ᵢ) holds
   ‡ = ⋁[ 𝒪 X ]-upper ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ 𝟏ᵢ) ⁆ (s 𝟏ₖ , 𝟏ᵈ-is-top 𝒦-X⁻ (s 𝟏ₖ))

   † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] join 𝟏ᵢ) holds
   † = transport (λ - → (- ≤[ poset-of (𝒪 X) ] join 𝟏ᵢ) holds) ι-preserves-𝟏 ‡

\end{code}

The map `join` preserves binary meets.

\begin{code}

 join-preserves-binary-meets : (ℐ 𝒥 : Ideal 𝒦-X⁻)
                             → join (ℐ ∧ᵢ 𝒥) ＝ join ℐ ∧[ 𝒪 X ] join 𝒥
 join-preserves-binary-meets ℐ 𝒥 =
  join (ℐ ∧ᵢ 𝒥)                                                            ＝⟨ refl ⟩
  ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆                                 ＝⟨ Ⅱ ⟩
  ⋁⟨ ((i , _) , (j , _)) ∶ (_ × _) ⟩ ι i ∧[ 𝒪 X ] ι j                      ＝⟨ Ⅰ ⟩
  (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X I ⁆) ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X J ⁆) ＝⟨ refl ⟩
  join ℐ ∧[ 𝒪 X ] join 𝒥 ∎
  where
   I = _∈ⁱ ℐ
   J = _∈ⁱ 𝒥

   open JoinNotation (join-of (𝒪 X))
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)


   † : ((⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆)
         ≤[ poset-of (𝒪 X) ]
        (⋁⟨ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻X (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻X (_∈ⁱ 𝒥)) ⟩ ι i ∧[ 𝒪 X ] ι j))
       holds
   † = cofinal-implies-join-covered (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆ ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻X (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻X (_∈ⁱ 𝒥)) ⁆ †₀
    where
     †₀ : cofinal-in (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆ ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻X (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻X (_∈ⁱ 𝒥)) ⁆ holds
     †₀ (K , μ₁ , μ₂) = ∣ ((K , μ₁) , (K , μ₂)) , reflexivity+ (poset-of (𝒪 X)) (∧[ 𝒪 X ]-is-idempotent (ι K)) ∣

   ‡ : ((⋁⟨ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻X (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻X (_∈ⁱ 𝒥)) ⟩ ι i ∧[ 𝒪 X ] ι j) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆)) holds
   ‡ = cofinal-implies-join-covered
        (𝒪 X)
        ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻X (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻X (_∈ⁱ 𝒥)) ⁆
        ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆
        ‡₀
        where
         ‡₀ : cofinal-in (𝒪 X) ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻X (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻X (_∈ⁱ 𝒥)) ⁆ ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆ holds
         ‡₀ ((K₁ , μ₁) , (K₂ , μ₂)) =
          ∣ (K₁ ∧⁻ K₂ , (I-is-downward-closed (K₁ ∧⁻ K₂) K₁ (∧-is-a-lower-bound₁ 𝒦-X⁻ K₁ K₂) μ₁ , J-is-downward-closed (K₁ ∧⁻ K₂) K₂ (∧-is-a-lower-bound₂ 𝒦-X⁻ K₁ K₂) μ₂)) , goal ∣
           where
            open Ideal ℐ using (I-is-downward-closed)
            open Ideal 𝒥 using () renaming (I-is-downward-closed to J-is-downward-closed)

            goal : ((ι K₁ ∧[ 𝒪 X ] ι K₂) ≤[ poset-of (𝒪 X) ] ι (K₁ ∧⁻ K₂)) holds
            goal = ι K₁ ∧[ 𝒪 X ] ι K₂ ＝⟨ ι-preserves-∧ K₁ K₂ ⁻¹ ⟩ₚ
                   ι (K₁ ∧⁻ K₂)       ■


   Ⅰ = distributivity+ (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X I ⁆ ⁅ ι K ∣ K ε 𝕋 𝒦⁻X J ⁆ ⁻¹
   Ⅱ = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡

\end{code}

The map `ϕ` is indeed the left inverse of the map `join` as promised.

\begin{code}

 ϕ-cancels-join : (ℐ : Ideal 𝒦-X⁻) → ϕ (join ℐ) ＝ ℐ
 ϕ-cancels-join ℐ = ideal-extensionality 𝒦-X⁻ (ϕ (join ℐ)) ℐ † ‡
  where
   open Ideal ℐ using (I-is-downward-closed)

   † : (ϕ (join ℐ) ⊆ᵢ ℐ) holds
   † K μ = ∥∥-rec
            (holds-is-prop (K ∈ᵢ ℐ))
            ‡
            (ι-gives-compact-opens K ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ) ⁆ (𝒦-below-is-directed ℐ) μ)
    where
     ‡ : Σ (K′ , _) ꞉ index ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ) ⁆ ,
          (ι K ≤[ poset-of (𝒪 X) ] ι K′) holds
       → K ∈ⁱ ℐ
     ‡ ((K′ , φ) , p) =
      I-is-downward-closed K K′ (ι-is-order-embedding K K′ p) φ

   ‡ : (ℐ ⊆ᵢ ϕ (join ℐ)) holds
   ‡ K μ = ⋁[ 𝒪 X ]-upper ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ ℐ) ⁆ (K , μ)

\end{code}

Furthermore, it is also the right inverse, the proof of which is given in
`join-cancels-ϕ`.

\begin{code}

 σᴰ : spectralᴰ X
 σᴰ = spectral-and-small-𝒦-implies-spectralᴰ X (pr₁ σ₀) (pr₂ σ₀)

 basis-X : basisᴰ (𝒪 X)
 basis-X = spectral-and-small-𝒦-gives-basis X (pr₁ σ₀) (pr₂ σ₀)

 basis↑-X : directed-basisᴰ (𝒪 X)
 basis↑-X = spectral-and-small-𝒦-gives-directed-basis X (pr₁ σ₀) (pr₂ σ₀)

 ℬ↑-X : Fam 𝓤 ⟨ 𝒪 X ⟩
 ℬ↑-X = pr₁ basis↑-X

 join-cancels-ϕ : (U : ⟨ 𝒪 X ⟩) → join (ϕ U) ＝ U
 join-cancels-ϕ U = transport (λ - → join (ϕ -) ＝ -) (c ⁻¹) final
  where
   J : Fam 𝓤 (index (basisₛ X σᴰ))
   J = cover-indexₛ X σᴰ U

   S : Fam 𝓤 ⟨ 𝒪 X ⟩
   S = covering-familyₛ X σᴰ U

   c : U ＝ ⋁[ 𝒪 X ] S
   c = basisₛ-covers-do-cover-eq X σᴰ U

   ψ : (i : index S) → (S [ i ] ≤[ poset-of (𝒪 X) ] U) holds
   ψ = pr₁ (basisₛ-covers-do-cover X σᴰ U)

   goal₁ : cofinal-in (𝒪 X) S ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆ holds
   goal₁ i = ∣ (s (S [ i ] , κ) , p) , † ∣
    where
     open Ideal (ϕ U) using (I-is-downward-closed)

     κ : is-compact-open X (S [ i ]) holds
     κ = basisₛ-consists-of-compact-opens X σᴰ (J [ i ])

     p : (pr₁ (r (s (S [ i ] , κ))) ≤[ poset-of (𝒪 X) ] U) holds
     p = pr₁ (r (s (S [ i ] , κ))) ＝⟨ ap pr₁ (inverses-are-sections' e (S [ i ] , κ)) ⟩ₚ S [ i ] ≤⟨ ψ i ⟩ U ■

     † : (S [ i ] ≤[ poset-of (𝒪 X) ] pr₁ (r (s (S [ i ] , κ)))) holds
     † = S [ i ] ＝⟨ ap pr₁ (inverses-are-sections' e (S [ i ] , κ) ⁻¹ ) ⟩ₚ pr₁ (r (s (S [ i ] , κ))) ■

   goal₂ : cofinal-in (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆ S holds
   goal₂ (K , p) = ∣ ((K , p) ∷ []) , † ∣
    where
     † : (pr₁ (r K) ≤[ poset-of (𝒪 X) ] S [ (K , p ∷ []) ]) holds
     † = reflexivity+ (poset-of (𝒪 X)) (𝟎-left-unit-of-∨ (𝒪 X) (pr₁ (r K)) ⁻¹)

   goal : ⋁[ 𝒪 X ] S ＝ ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆
   goal = bicofinal-implies-same-join (𝒪 X) S ((fmap-syntax (λ K → ι K)) (𝕋 𝒦⁻X (_∈ⁱ ϕ U))) goal₁ goal₂

   ♣ : (join (ϕ (⋁[ 𝒪 X ] S)) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆)) holds
   ♣ = cofinal-implies-join-covered (𝒪 X) (𝒦-below (ϕ (join-of (𝒪 X) S))) (fmap-syntax (λ K → ι K) (𝕋 𝒦⁻X (_∈ⁱ ϕ U))) γ
    where
     γ : cofinal-in (𝒪 X) (𝒦-below (ϕ (join-of (𝒪 X) S))) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆ holds
     γ (K , q) = ∣ (K , (transport (λ - → K ∈ⁱ ϕ -) (c ⁻¹) q)) , ≤-is-reflexive (poset-of (𝒪 X)) (ι K) ∣

   ♠ : ((⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆) ≤[ poset-of (𝒪 X) ] join (ϕ (⋁[ 𝒪 X ] S))) holds
   ♠ = cofinal-implies-join-covered (𝒪 X) (fmap-syntax (λ K → ι K) (𝕋 𝒦⁻X (_∈ⁱ ϕ U))) (𝒦-below (ϕ (join-of (𝒪 X) S))) γ
    where
     γ : cofinal-in (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆ (𝒦-below (ϕ (join-of (𝒪 X) S))) holds
     γ (K , q) = ∣ (K , transport (λ - → K ∈ⁱ ϕ -) c q) , ≤-is-reflexive (poset-of (𝒪 X)) (ι K) ∣

   final : join (ϕ (⋁[ 𝒪 X ] S)) ＝ ⋁[ 𝒪 X ] S
   final = join (ϕ (⋁[ 𝒪 X ] S))                   ＝⟨ ≤-is-antisymmetric (poset-of (𝒪 X)) ♣ ♠ ⟩
           ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻X (_∈ⁱ (ϕ U)) ⁆ ＝⟨ goal ⁻¹ ⟩
           ⋁[ 𝒪 X ] S ∎

\end{code}

\begin{code}

 ϕₘ : poset-of (𝒪 X) ─m→ poset-of-ideals
 ϕₘ = ϕ , ϕ-is-monotone

\end{code}

\begin{code}

 join-is-monotone : is-monotonic poset-of-ideals (poset-of (𝒪 X)) join holds
 join-is-monotone (U , V) p = connecting-lemma₂ (𝒪 X) †
  where
   † : join U ＝ join U ∧[ 𝒪 X ] join V
   † = join U ＝⟨ ap join (connecting-lemma₁ frame-of-ideals p) ⟩ join (U ∧ᵢ V) ＝⟨ join-preserves-binary-meets U V ⟩ join U ∧[ 𝒪 X ] join V ∎

 joinₘ : poset-of-ideals ─m→ poset-of (𝒪 X)
 joinₘ = join , join-is-monotone

\end{code}

\begin{code}

 open AdjointFunctorTheorem

 X-has-basis : has-basis (𝒪 X) holds
 X-has-basis = ∣ spectralᴰ-implies-basisᴰ X σᴰ ∣

 spec-𝒦X-has-basis : has-basis (𝒪 spec-𝒦X) holds
 spec-𝒦X-has-basis =
  ∣ Spectrality.ℬ-spec 𝒦-X⁻  , Spectrality.ℬ-spec-is-basis 𝒦-X⁻ ∣

 ϕ-is-left-adjoint-of-join : let
                              open GaloisConnectionBetween (poset-of (𝒪 X)) poset-of-ideals
                             in
                              (ϕₘ ⊣ joinₘ) holds
 ϕ-is-left-adjoint-of-join =
  an-important-lemma spec-𝒦X X X-has-basis joinₘ ϕₘ join-cancels-ϕ ϕ-cancels-join

 ϕ-is-right-adjoint-to-join : let
                               open GaloisConnectionBetween poset-of-ideals (poset-of (𝒪 X))
                              in
                               (joinₘ ⊣ ϕₘ) holds
 ϕ-is-right-adjoint-to-join =
  an-important-lemma X spec-𝒦X spec-𝒦X-has-basis ϕₘ joinₘ ϕ-cancels-join join-cancels-ϕ

\end{code}

\begin{code}

 ϕ-preserves-joins : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
                   → ϕ (⋁[ 𝒪 X ] S) ＝ ⋁ᵢ ⁅ ϕ U ∣ U ε S ⁆
 ϕ-preserves-joins =
  aft-forward spec-𝒦X X X-has-basis ϕₘ (joinₘ , ϕ-is-left-adjoint-of-join)

\end{code}

\begin{code}

 join-preserves-joins : (S : Fam 𝓤 (Ideal 𝒦-X⁻))
                      → join (⋁ᵢ S) ＝ ⋁[ 𝒪 X ] ⁅ join I ∣ I ε S ⁆
 join-preserves-joins = aft-forward
                         X
                         spec-𝒦X
                         spec-𝒦X-has-basis
                         joinₘ
                         (ϕₘ , ϕ-is-right-adjoint-to-join)

\end{code}

\begin{code}

 ϕ-is-a-frame-homomorphism : is-a-frame-homomorphism (𝒪 X) (𝒪 spec-𝒦X) ϕ holds
 ϕ-is-a-frame-homomorphism = ϕ-preserves-top , ϕ-preserves-∧ , †
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 spec-𝒦X) ] y)

   † : preserves-joins (𝒪 X) (𝒪 spec-𝒦X) ϕ holds
   † S =
    transport
     (λ - → (- is-lub-of ⁅ ϕ I ∣ I ε S ⁆) holds)
     (ϕ-preserves-joins S ⁻¹)
     (⋁[ 𝒪 spec-𝒦X ]-upper _ , ⋁[ 𝒪 spec-𝒦X ]-least _)

\end{code}

\begin{code}

 join-is-a-frame-homomorphism : is-a-frame-homomorphism (𝒪 spec-𝒦X) (𝒪 X) join holds
 join-is-a-frame-homomorphism =
  join-preserves-top , join-preserves-binary-meets , †
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

    † : preserves-joins (𝒪 spec-𝒦X) (𝒪 X) join holds
    † S = transport
           (λ - → (- is-lub-of ⁅ join I ∣ I ε S ⁆) holds)
           (join-preserves-joins S ⁻¹)
           (⋁[ 𝒪 X ]-upper _ , ⋁[ 𝒪 X ]-least _)

\end{code}

\begin{code}

 open FrameIsomorphisms

 𝒪X-is-equivalent-to-ideals-of-𝒦X : ⟨ 𝒪 X ⟩ ≃ Ideal 𝒦-X⁻
 𝒪X-is-equivalent-to-ideals-of-𝒦X = ϕ , ((join , †) , (join , ‡))
  where
   † : (ϕ ∘ join) ∼ id
   † = ϕ-cancels-join

   ‡ : (join ∘ ϕ) ∼ id
   ‡ = join-cancels-ϕ

 X-iso-to-spec-𝒦X : spec-𝒦X ≅c≅ X
 X-iso-to-spec-𝒦X = isomorphism₀-to-isomorphismᵣ (𝒪 X) (𝒪 spec-𝒦X) 𝒾
  where
   𝒾 : Isomorphism₀ (𝒪 X) (𝒪 spec-𝒦X)
   𝒾 = 𝒪X-is-equivalent-to-ideals-of-𝒦X
     , ϕ-is-a-frame-homomorphism
     , join-is-a-frame-homomorphism

\end{code}

\begin{code}

open DefnOfFrameOfIdeal

spectral-implies-spectral·
 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
 → is-spectral-with-small-basis ua X holds
 → ∃ L ꞉ DistributiveLattice 𝓤 , X ≅c≅ locale-of-spectra L
spectral-implies-spectral· X σ = ∣ 𝒦⦅X⦆⁻ , ≅c-sym spec-𝒦X X X-iso-to-spec-𝒦X ∣
 where
  open 𝒦-Duality X σ

\end{code}

Recall that the type of spectral locales is defined as

\begin{code}

Spectral-Locale : (𝓤 : Universe) → 𝓤 ⁺ ⁺  ̇
Spectral-Locale 𝓤 =
 Σ X ꞉ Locale (𝓤 ⁺) 𝓤 𝓤 , is-spectral-with-small-basis ua X holds

\end{code}
