--------------------------------------------------------------------------------
title:          Distributive lattice of compact opens
author:         Ayberk Tosun
date-started:   2024-02-24
date-completed: 2024-02-27
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
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

open AllCombinators pt fe hiding (_∨_)
open Locale
open PropositionalTruncation pt hiding (_∨_)

\end{code}

We fix a large and locally small locale `X`, assumed to be spectral with a small
type of compact opens.

\begin{code}

module 𝒦-Duality (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
                 (σ₀ : is-spectral-with-small-basis ua X holds) where

 open 𝒦-Lattice X σ₀

\end{code}

We define some shorthand notation to simplify the proofs.

\begin{code}

\end{code}

\begin{code}

 e : 𝒦⁻ ≃ 𝒦 X
 e = resizing-condition 𝒦⦅X⦆-is-small

 open DistributiveLatticeResizing 𝒦⦅X⦆ 𝒦⁻ (≃-sym e) renaming (Lᶜ to 𝒦-X⁻)

 𝒦⦅X⦆⁻ = 𝒦-X⁻

 𝒦-isomorphism : 𝒦⦅X⦆ ≅d≅ 𝒦-X⁻
 𝒦-isomorphism = copy-isomorphic-to-original

\end{code}

\begin{code}

 open DefnOfFrameOfIdeal 𝒦-X⁻

\end{code}

\begin{code}

 spec-𝒦-X : Locale (𝓤 ⁺) 𝓤 𝓤
 spec-𝒦-X = locale-of-spectra

 ι : ∣ 𝒦-X⁻ ∣ᵈ → ⟨ 𝒪 X ⟩
 ι K = pr₁ (r K)

 open Ideal hiding (I; I-is-downward-closed)
 open DistributiveLattice 𝒦-X⁻ using () renaming (𝟎 to 𝟎⁻; 𝟏 to 𝟏⁻; _∨_ to _∨⁻_; _∧_ to _∧⁻_)
 open DistributiveLattice 𝒦⦅X⦆ using (𝟎; 𝟏; _∨_) renaming (_∧_ to _∧L_)

 ι-preserves-𝟎 : ι 𝟎⁻ ＝ 𝟎[ 𝒪 X ]
 ι-preserves-𝟎 = ap pr₁ (inverses-are-sections' e 𝟎)

 ι-preserves-𝟏 : ι 𝟏⁻ ＝ 𝟏[ 𝒪 X ]
 ι-preserves-𝟏 = ap pr₁ (inverses-are-sections' e 𝟏)

 open PosetReasoning (poset-of (𝒪 X))
 open OperationsOnCompactOpens X σ

 ι-preserves-∨ : (K₁ K₂ : 𝒦⁻)
               → ι (K₁ ∨⁻ K₂) ＝ ι K₁ ∨[ 𝒪 X ] ι K₂
 ι-preserves-∨ K₁ K₂ =
  ιₖ (r (K₁ ∨⁻ K₂))                 ＝⟨ Ⅰ    ⟩
  ιₖ (r K₁ ∨ r K₂)                  ＝⟨ Ⅱ    ⟩
  pr₁ (r K₁) ∨[ 𝒪 X ] pr₁ (r K₂)    ＝⟨ refl ⟩
  ι K₁ ∨[ 𝒪 X ] ι K₂                ∎
   where
    Ⅰ = ap pr₁ (r-preserves-∨ K₁ K₂)
    Ⅱ = ιₖ-preserves-∨ (r K₁) (r K₂)

 ι-preserves-∧ : (K₁ K₂ : 𝒦⁻) → ι (K₁ ∧⁻ K₂) ＝ ι K₁ ∧[ 𝒪 X ] ι K₂
 ι-preserves-∧ K₁ K₂ =
  ι (K₁ ∧⁻ K₂)         ＝⟨ refl                         ⟩
  pr₁ (r (K₁ ∧⁻ K₂))   ＝⟨ ap pr₁ (r-preserves-∧ K₁ K₂) ⟩
  pr₁ (r K₁ ∧L r K₂)   ＝⟨ ιₖ-preserves-∧ (r K₁) (r K₂) ⟩
  ι K₁ ∧[ 𝒪 X ] ι K₂   ∎

 ι-is-monotone : (K₁ K₂ : 𝒦⁻)
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

 ι-is-order-embedding : (K₁ K₂ : 𝒦⁻)
                      → (ι K₁ ≤[ poset-of (𝒪 X) ] ι K₂) holds
                      → (K₁ ≤ᵈ[ 𝒦-X⁻ ] K₂) holds
 ι-is-order-embedding K₁ K₂ p =
  s (r K₁ ∧L r K₂)   ＝⟨ ap s (to-𝒦-＝ X _ (pr₂ (r K₁)) foo) ⟩
  s (r K₁)           ＝⟨ inverses-are-retractions' e K₁ ⟩
  K₁             ∎
   where
    foo : pr₁ (r K₁) ∧[ 𝒪 X ] pr₁ (r K₂) ＝ ι K₁
    foo = connecting-lemma₁ (𝒪 X) p ⁻¹

\end{code}

The map `ι` gives compact opens.

\begin{code}

 ι-gives-compact-opens : (K : 𝒦⁻) → is-compact-open X (ι K) holds
 ι-gives-compact-opens K = pr₂ (r K)

\end{code}

\begin{code}

 η : ⟨ 𝒪 X ⟩ → 𝓟 𝒦⁻
 η U = λ c → ι c ≤[ poset-of (𝒪 X) ] U

 η-contains-𝟎 : (U : ⟨ 𝒪 X ⟩) → 𝟎⁻ ∈ η U
 η-contains-𝟎 U = ι 𝟎⁻       ＝⟨ Ⅰ ⟩ₚ
                  𝟎[ 𝒪 X ]   ≤⟨ Ⅱ ⟩
                  U          ■
                   where
                    Ⅰ = ι-preserves-𝟎
                    Ⅱ = 𝟎-is-bottom (𝒪 X) U

\end{code}

\begin{code}

 η-is-downward-closed : (U : ⟨ 𝒪 X ⟩) → is-downward-closed 𝒦-X⁻ (η U) holds
 η-is-downward-closed U K₁ K₂ p μ =
  ιₖ (r K₁)   ≤⟨ Ⅰ ⟩
  ιₖ (r K₂)   ≤⟨ Ⅱ ⟩
  U           ■
   where
    Ⅰ = ι-is-monotone K₁ K₂ p
    Ⅱ = μ

\end{code}

\begin{code}

 η-is-closed-under-∨ : (U : ⟨ 𝒪 X ⟩)
                     → is-closed-under-binary-joins 𝒦-X⁻ (η U) holds
 η-is-closed-under-∨ U K₁ K₂ μ₁ μ₂  = †
  where
   foo : (ι K₁ ≤[ poset-of (𝒪 X) ] U) holds
   foo = μ₁

   baz : ((ι K₁ ∨[ 𝒪 X ] ι K₂) ≤[ poset-of (𝒪 X) ] U) holds
   baz = ∨[ 𝒪 X ]-least μ₁ μ₂

   † : (ι (K₁ ∨⁻ K₂) ≤[ poset-of (𝒪 X) ] U) holds
   † = ι (K₁ ∨⁻ K₂) ＝⟨ ι-preserves-∨ K₁ K₂ ⟩ₚ ι K₁ ∨[ 𝒪 X ] ι K₂ ≤⟨ baz ⟩ U ■

\end{code}

\begin{code}

 ϕ₀ : ⟨ 𝒪 X ⟩ → Ideal 𝒦-X⁻
 ϕ₀ U = record
         { I                    = η U
         ; I-is-inhabited       = ∣ 𝟎⁻ , η-contains-𝟎 U ∣
         ; I-is-downward-closed = η-is-downward-closed U
         ; I-is-closed-under-∨  = η-is-closed-under-∨ U
         }

\end{code}

\begin{code}

 abstract
  ϕ₀-preserves-top : ϕ₀ 𝟏[ 𝒪 X ] ＝ 𝟏[ 𝒪 spec-𝒦-X ]
  ϕ₀-preserves-top = only-𝟏-is-above-𝟏 (𝒪 spec-𝒦-X) (ϕ₀ 𝟏[ 𝒪 X ]) †
   where
    † : (𝟏[ 𝒪 spec-𝒦-X ] ≤[ poset-of frame-of-ideals ] ϕ₀ 𝟏[ 𝒪 X ]) holds
    † K _ = 𝟏-is-top (𝒪 X) (ι K)

\end{code}

\begin{code}

 open IdealNotation 𝒦-X⁻

 ϕ₀-preserves-∧ : (U V : ⟨ 𝒪 X ⟩) → ϕ₀ (U ∧[ 𝒪 X ] V) ＝ ϕ₀ U ∧ᵢ ϕ₀ V
 ϕ₀-preserves-∧ U V = ≤-is-antisymmetric poset-of-ideals † ‡
  where
   † : ϕ₀ (U ∧[ 𝒪 X ] V) ⊆ᵢ (ϕ₀ U ∧ᵢ ϕ₀ V) holds
   † K p = p₁ , p₂
    where
     p₁ : K ∈ⁱ ϕ₀ U
     p₁ = ι K ≤⟨ p ⟩ U ∧[ 𝒪 X ] V ≤⟨ ∧[ 𝒪 X ]-lower₁ U V ⟩ U ■

     p₂ : K ∈ⁱ ϕ₀ V
     p₂ = ι K ≤⟨ p ⟩ U ∧[ 𝒪 X ] V ≤⟨ ∧[ 𝒪 X ]-lower₂ U V ⟩ V ■

   ‡ : (ϕ₀ U ∧ᵢ ϕ₀ V) ⊆ᵢ ϕ₀ (U ∧[ 𝒪 X ] V) holds
   ‡ K (p₁ , p₂) = ∧[ 𝒪 X ]-greatest U V (ι K) p₁ p₂

 ϕ₀-is-monotone : is-monotonic (poset-of (𝒪 X)) poset-of-ideals ϕ₀ holds
 ϕ₀-is-monotone (U , V) p = connecting-lemma₂ frame-of-ideals †
  where
   q : U ＝ U ∧[ 𝒪 X ] V
   q = connecting-lemma₁ (𝒪 X) p

   † : ϕ₀ U ＝ ϕ₀ U ∧ᵢ ϕ₀ V
   † = ϕ₀ U              ＝⟨ Ⅰ ⟩
       ϕ₀ (U ∧[ 𝒪 X ] V) ＝⟨ Ⅱ ⟩
       ϕ₀ U ∧ᵢ ϕ₀ V      ∎
        where
         Ⅰ = ap ϕ₀ q
         Ⅱ = ϕ₀-preserves-∧ U V

\end{code}

\begin{code}

 open FrameHomomorphisms

{--

 ϕ₀-preserves-∨ : (U V : ⟨ 𝒪 X ⟩)
                → ϕ₀ (U ∨[ 𝒪 X ] V) ＝ ϕ₀ U ∨[ 𝒪 spec-𝒦-X ] ϕ₀ V
 ϕ₀-preserves-∨ U V = ≤-is-antisymmetric poset-of-ideals † ‡
  where
   † : ϕ₀ (U ∨[ 𝒪 X ] V) ⊆ᵢ (ϕ₀ U ∨[ 𝒪 spec-𝒦-X ] ϕ₀ V) holds
   † K μ = {!∨[ 𝒪 spec-𝒦-X ]-upper!}

   ‡ : (ϕ₀ U ∨[ 𝒪 spec-𝒦-X ] ϕ₀ V) ⊆ᵢ ϕ₀ (U ∨[ 𝒪 X ] V) holds
   ‡ K = ∨[ frame-of-ideals ]-least {ϕ₀ U} {ϕ₀ V} {ϕ₀ (U ∨[ 𝒪 X ] V)} क ग K
    where
     क : ϕ₀ U ⊆ᵢ ϕ₀ (U ∨[ 𝒪 X ] V) holds
     क = ϕ₀-is-monotone (U , (U ∨[ 𝒪 X ] V)) (∨[ 𝒪 X ]-upper₁ U V)

     ग : ϕ₀ V ⊆ᵢ ϕ₀ (U ∨[ 𝒪 X ] V) holds
     ग = ϕ₀-is-monotone (V , binary-join (𝒪 X) U V) (∨[ 𝒪 X ]-upper₂ U V)

--}

\end{code}

What is the map going in the opposite direction of `ϕ`? This is simply the
map that maps an ideal to its joins `I ↦ ⋁ I`. We denote this by `join`.

\begin{code}

 open classifier-single-universe 𝓤
 open Directed-Families-On-Posets (poset-ofᵈ 𝒦-X⁻) (poset-of (𝒪 X))
 open IdealProperties 𝒦-X⁻

 𝒦-below : Ideal 𝒦-X⁻ → Fam 𝓤 ⟨ 𝒪 X ⟩
 𝒦-below ℐ = ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ) ⁆

 𝒦-below-is-directed : (ℐ : Ideal 𝒦-X⁻)
                     → is-directed (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ) ⁆ holds
 𝒦-below-is-directed ℐ =
  monotone-image-on-directed-set-is-directed
   ιₘ
   (𝕋 𝒦⁻ (_∈ⁱ ℐ))
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
   foo : Σ i ꞉ index (𝕋 𝒦⁻ (_∈ⁱ 𝟏ᵢ)) , ι (pr₁ i) ＝ 𝟏[ 𝒪 X ]
   foo = (s 𝟏ₖ , 𝟏ᵈ-is-top 𝒦-X⁻ (s 𝟏ₖ)) , ι-preserves-𝟏

   eq : ι (s 𝟏ₖ) ＝ 𝟏[ 𝒪 X ]
   eq = pr₂ foo

   ‡ : (ι (s 𝟏ₖ) ≤[ poset-of (𝒪 X)] (join 𝟏ᵢ)) holds
   ‡ = ⋁[ 𝒪 X ]-upper ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ 𝟏ᵢ) ⁆ (pr₁ foo)

   † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] join 𝟏ᵢ) holds
   † = transport (λ - → (- ≤[ poset-of (𝒪 X) ] join 𝟏ᵢ) holds) eq ‡

\end{code}

Join preserves binary meets.

\begin{code}

 join-preserves-binary-meets : (ℐ 𝒥 : Ideal 𝒦-X⁻)
                             → join (ℐ ∧ᵢ 𝒥) ＝ join ℐ ∧[ 𝒪 X ] join 𝒥
 join-preserves-binary-meets ℐ 𝒥 =
  join (ℐ ∧ᵢ 𝒥)                                                            ＝⟨ refl ⟩
  ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆                                 ＝⟨ Ⅱ ⟩
  ⋁⟨ ((i , _) , (j , _)) ∶ (_ × _) ⟩ ι i ∧[ 𝒪 X ] ι j                      ＝⟨ Ⅰ ⟩
  (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ I ⁆) ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ J ⁆) ＝⟨ refl ⟩
  join ℐ ∧[ 𝒪 X ] join 𝒥 ∎
  where
   I = _∈ⁱ ℐ
   J = _∈ⁱ 𝒥

   open JoinNotation (join-of (𝒪 X))
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)


   † : ((⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆)
         ≤[ poset-of (𝒪 X) ]
        (⋁⟨ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻ (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻ (_∈ⁱ 𝒥)) ⟩ ι i ∧[ 𝒪 X ] ι j))
       holds
   † = cofinal-implies-join-covered (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆ ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻ (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻ (_∈ⁱ 𝒥)) ⁆ †₀
    where
     †₀ : cofinal-in (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆ ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻ (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻ (_∈ⁱ 𝒥)) ⁆ holds
     †₀ (K , μ₁ , μ₂) = ∣ ((K , μ₁) , (K , μ₂)) , reflexivity+ (poset-of (𝒪 X)) (∧[ 𝒪 X ]-is-idempotent (ι K)) ∣

   ‡ : ((⋁⟨ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻ (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻ (_∈ⁱ 𝒥)) ⟩ ι i ∧[ 𝒪 X ] ι j) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆)) holds
   ‡ = cofinal-implies-join-covered
        (𝒪 X)
        ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻ (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻ (_∈ⁱ 𝒥)) ⁆
        ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆
        ‡₀
        where
         ‡₀ : cofinal-in (𝒪 X) ⁅ ι i ∧[ 𝒪 X ] ι j ∣ ((i , _) , (j , _)) ∶ index (𝕋 𝒦⁻ (_∈ⁱ ℐ)) × index (𝕋 𝒦⁻ (_∈ⁱ 𝒥)) ⁆ ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ ∧ᵢ 𝒥) ⁆ holds
         ‡₀ ((K₁ , μ₁) , (K₂ , μ₂)) =
          ∣ (K₁ ∧⁻ K₂ , (I-is-downward-closed (K₁ ∧⁻ K₂) K₁ (∧-is-a-lower-bound₁ 𝒦-X⁻ K₁ K₂) μ₁ , J-is-downward-closed (K₁ ∧⁻ K₂) K₂ (∧-is-a-lower-bound₂ 𝒦-X⁻ K₁ K₂) μ₂)) , goal ∣
           where
            open Ideal ℐ using (I-is-downward-closed)
            open Ideal 𝒥 using () renaming (I-is-downward-closed to J-is-downward-closed)

            goal : ((ι K₁ ∧[ 𝒪 X ] ι K₂) ≤[ poset-of (𝒪 X) ] ι (K₁ ∧⁻ K₂)) holds
            goal = ι K₁ ∧[ 𝒪 X ] ι K₂ ＝⟨ ι-preserves-∧ K₁ K₂ ⁻¹ ⟩ₚ
                   ι (K₁ ∧⁻ K₂)       ■


   Ⅰ = distributivity+ (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ I ⁆ ⁅ ι K ∣ K ε 𝕋 𝒦⁻ J ⁆ ⁻¹
   Ⅱ = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡

\end{code}

\begin{code}

 ϕ-cancels-join : (ℐ : Ideal 𝒦-X⁻) → ϕ₀ (join ℐ) ＝ ℐ
 ϕ-cancels-join ℐ = ideal-extensionality 𝒦-X⁻ (ϕ₀ (join ℐ)) ℐ † ‡
  where
   open Ideal ℐ using (I-is-downward-closed)

   † : (ϕ₀ (join ℐ) ⊆ᵢ ℐ) holds
   † K μ = ∥∥-rec
            (holds-is-prop (K ∈ᵢ ℐ))
            ‡
            (ι-gives-compact-opens K ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ) ⁆ (𝒦-below-is-directed ℐ) μ)
    where
     ‡ : Σ (K′ , _) ꞉ index ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ) ⁆ ,
          (ι K ≤[ poset-of (𝒪 X) ] ι K′) holds
       → K ∈ⁱ ℐ
     ‡ ((K′ , φ) , p) =
      I-is-downward-closed K K′ (ι-is-order-embedding K K′ p) φ

   ‡ : (ℐ ⊆ᵢ ϕ₀ (join ℐ)) holds
   ‡ K μ = ⋁[ 𝒪 X ]-upper ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ ℐ) ⁆ (K , μ)

\end{code}

\begin{code}

 X-spectralᴰ : spectralᴰ X
 X-spectralᴰ = spectral-and-small-𝒦-implies-spectralᴰ X (pr₁ σ₀) (pr₂ σ₀)

 basis-X : basisᴰ (𝒪 X)
 basis-X = spectral-and-small-𝒦-gives-basis X (pr₁ σ₀) (pr₂ σ₀)

 basis↑-X : directed-basisᴰ (𝒪 X)
 basis↑-X = spectral-and-small-𝒦-gives-directed-basis X (pr₁ σ₀) (pr₂ σ₀)

 ℬ↑-X : Fam 𝓤 ⟨ 𝒪 X ⟩
 ℬ↑-X = pr₁ basis↑-X

 join-cancels-ϕ : (U : ⟨ 𝒪 X ⟩) → join (ϕ₀ U) ＝ U
 join-cancels-ϕ U = transport (λ - → join (ϕ₀ -) ＝ -) (c ⁻¹) final
  where
   J : Fam 𝓤 (index (basisₛ X X-spectralᴰ))
   J = cover-indexₛ X X-spectralᴰ U

   S : Fam 𝓤 ⟨ 𝒪 X ⟩
   S = covering-familyₛ X X-spectralᴰ U

   c : U ＝ ⋁[ 𝒪 X ] S
   c = basisₛ-covers-do-cover-eq X X-spectralᴰ U

   ψ : (i : index S) → (S [ i ] ≤[ poset-of (𝒪 X) ] U) holds
   ψ = pr₁ (basisₛ-covers-do-cover X X-spectralᴰ U)

   goal₁ : cofinal-in (𝒪 X) S ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆ holds
   goal₁ i = ∣ (s (S [ i ] , κ) , p) , † ∣
    where
     open Ideal (ϕ₀ U) using (I-is-downward-closed)

     κ : is-compact-open X (S [ i ]) holds
     κ = basisₛ-consists-of-compact-opens X X-spectralᴰ (J [ i ])

     p : (pr₁ (r (s (S [ i ] , κ))) ≤[ poset-of (𝒪 X) ] U) holds
     p = pr₁ (r (s (S [ i ] , κ))) ＝⟨ ap pr₁ (inverses-are-sections' e (S [ i ] , κ)) ⟩ₚ S [ i ] ≤⟨ ψ i ⟩ U ■

     † : (S [ i ] ≤[ poset-of (𝒪 X) ] pr₁ (r (s (S [ i ] , κ)))) holds
     † = S [ i ] ＝⟨ ap pr₁ (inverses-are-sections' e (S [ i ] , κ) ⁻¹ ) ⟩ₚ pr₁ (r (s (S [ i ] , κ))) ■

   goal₂ : cofinal-in (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆ S holds
   goal₂ (K , p) = ∣ ((K , p) ∷ []) , † ∣
    where
     † : (pr₁ (r K) ≤[ poset-of (𝒪 X) ] S [ (K , p ∷ []) ]) holds
     † = reflexivity+ (poset-of (𝒪 X)) (𝟎-left-unit-of-∨ (𝒪 X) (pr₁ (r K)) ⁻¹)

   goal : ⋁[ 𝒪 X ] S ＝ ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆
   goal = bicofinal-implies-same-join (𝒪 X) S ((fmap-syntax (λ K → ι K)) (𝕋 𝒦⁻ (_∈ⁱ ϕ₀ U))) goal₁ goal₂

   ♣ : (join (ϕ₀ (⋁[ 𝒪 X ] S)) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆)) holds
   ♣ = cofinal-implies-join-covered (𝒪 X) (𝒦-below (ϕ₀ (join-of (𝒪 X) S))) (fmap-syntax (λ K → ι K) (𝕋 𝒦⁻ (_∈ⁱ ϕ₀ U))) γ
    where
     γ : cofinal-in (𝒪 X) (𝒦-below (ϕ₀ (join-of (𝒪 X) S))) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆ holds
     γ (K , q) = ∣ (K , (transport (λ - → K ∈ⁱ ϕ₀ -) (c ⁻¹) q)) , ≤-is-reflexive (poset-of (𝒪 X)) (ι K) ∣

   ♠ : ((⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆) ≤[ poset-of (𝒪 X) ] join (ϕ₀ (⋁[ 𝒪 X ] S))) holds
   ♠ = cofinal-implies-join-covered (𝒪 X) (fmap-syntax (λ K → ι K) (𝕋 𝒦⁻ (_∈ⁱ ϕ₀ U))) (𝒦-below (ϕ₀ (join-of (𝒪 X) S))) γ
    where
     γ : cofinal-in (𝒪 X) ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆ (𝒦-below (ϕ₀ (join-of (𝒪 X) S))) holds
     γ (K , q) = ∣ (K , transport (λ - → K ∈ⁱ ϕ₀ -) c q) , ≤-is-reflexive (poset-of (𝒪 X)) (ι K) ∣

   final : join (ϕ₀ (⋁[ 𝒪 X ] S)) ＝ ⋁[ 𝒪 X ] S
   final = join (ϕ₀ (⋁[ 𝒪 X ] S))                   ＝⟨ ≤-is-antisymmetric (poset-of (𝒪 X)) ♣ ♠ ⟩
           ⋁[ 𝒪 X ] ⁅ ι K ∣ K ε 𝕋 𝒦⁻ (_∈ⁱ (ϕ₀ U)) ⁆ ＝⟨ goal ⁻¹ ⟩
           ⋁[ 𝒪 X ] S ∎

\end{code}

\begin{code}

 ϕₘ : poset-of (𝒪 X) ─m→ poset-of-ideals
 ϕₘ = ϕ₀ , ϕ₀-is-monotone

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
 X-has-basis = ∣ spectralᴰ-implies-basisᴰ X X-spectralᴰ ∣

 spec-𝒦-X-has-basis : has-basis (𝒪 spec-𝒦-X) holds
 spec-𝒦-X-has-basis =
  ∣ Spectrality.ℬ-spec 𝒦-X⁻  , Spectrality.ℬ-spec-is-basis 𝒦-X⁻ ∣

 ϕ-is-left-adjoint-of-join : let
                              open GaloisConnectionBetween (poset-of (𝒪 X)) poset-of-ideals
                             in
                              (ϕₘ ⊣ joinₘ) holds
 ϕ-is-left-adjoint-of-join =
  an-important-lemma spec-𝒦-X X X-has-basis joinₘ ϕₘ join-cancels-ϕ ϕ-cancels-join

 ϕ-is-right-adjoint-to-join : let
                               open GaloisConnectionBetween poset-of-ideals (poset-of (𝒪 X))
                              in
                               (joinₘ ⊣ ϕₘ) holds
 ϕ-is-right-adjoint-to-join =
  an-important-lemma X spec-𝒦-X spec-𝒦-X-has-basis ϕₘ joinₘ ϕ-cancels-join join-cancels-ϕ

\end{code}

\begin{code}

 ϕ-preserves-joins : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
                   → ϕ₀ (⋁[ 𝒪 X ] S) ＝ ⋁ᵢ ⁅ ϕ₀ U ∣ U ε S ⁆
 ϕ-preserves-joins =
  aft-forward spec-𝒦-X X X-has-basis ϕₘ (joinₘ , ϕ-is-left-adjoint-of-join)

\end{code}

\begin{code}

 join-preserves-joins : (S : Fam 𝓤 (Ideal 𝒦-X⁻))
                      → join (⋁ᵢ S) ＝ ⋁[ 𝒪 X ] ⁅ join I ∣ I ε S ⁆
 join-preserves-joins = aft-forward
                         X
                         spec-𝒦-X
                         spec-𝒦-X-has-basis
                         joinₘ
                         (ϕₘ , ϕ-is-right-adjoint-to-join)

\end{code}

\begin{code}

 ϕ-is-a-frame-homomorphism : is-a-frame-homomorphism (𝒪 X) (𝒪 spec-𝒦-X) ϕ₀ holds
 ϕ-is-a-frame-homomorphism = ϕ₀-preserves-top , ϕ₀-preserves-∧ , †
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 spec-𝒦-X) ] y)

   † : preserves-joins (𝒪 X) (𝒪 spec-𝒦-X) ϕ₀ holds
   † S =
    transport
     (λ - → (- is-lub-of ⁅ ϕ₀ I ∣ I ε S ⁆) holds)
     (ϕ-preserves-joins S ⁻¹)
     (⋁[ 𝒪 spec-𝒦-X ]-upper _ , ⋁[ 𝒪 spec-𝒦-X ]-least _)

\end{code}

\begin{code}

 join-is-a-frame-homomorphism : is-a-frame-homomorphism (𝒪 spec-𝒦-X) (𝒪 X) join holds
 join-is-a-frame-homomorphism =
  join-preserves-top , join-preserves-binary-meets , †
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

    † : preserves-joins (𝒪 spec-𝒦-X) (𝒪 X) join holds
    † S = transport
           (λ - → (- is-lub-of ⁅ join I ∣ I ε S ⁆) holds)
           (join-preserves-joins S ⁻¹)
           (⋁[ 𝒪 X ]-upper _ , ⋁[ 𝒪 X ]-least _)

\end{code}

\begin{code}

 open FrameIsomorphisms

 𝒪X-is-equivalent-to-ideals-of-𝒦X : ⟨ 𝒪 X ⟩ ≃ Ideal 𝒦-X⁻
 𝒪X-is-equivalent-to-ideals-of-𝒦X = ϕ₀ , ((join , †) , (join , ‡))
  where
   † : (ϕ₀ ∘ join) ∼ id
   † = ϕ-cancels-join

   ‡ : (join ∘ ϕ₀) ∼ id
   ‡ = join-cancels-ϕ

 X-iso-to-spec-𝒦-X : spec-𝒦-X ≅c≅ X
 X-iso-to-spec-𝒦-X = isomorphism₀-to-isomorphismᵣ (𝒪 X) (𝒪 spec-𝒦-X) 𝒾
  where
   𝒾 : Isomorphism₀ (𝒪 X) (𝒪 spec-𝒦-X)
   𝒾 = 𝒪X-is-equivalent-to-ideals-of-𝒦X
     , ϕ-is-a-frame-homomorphism
     , join-is-a-frame-homomorphism

\end{code}

Recall that the type of spectral locales is defined as

\begin{code}

Spectral-Locale : (𝓤 : Universe) → 𝓤 ⁺ ⁺  ̇
Spectral-Locale 𝓤 =
 Σ X ꞉ Locale (𝓤 ⁺) 𝓤 𝓤 , is-spectral-with-small-basis ua X holds

\end{code}

Put this in the `LatticeOfCompactOpens-Duality` module.

\begin{todo}

spec-dlat-equivalence : (𝓤 : Universe) → Spectral-Locale 𝓤 ≃ DistributiveLattice 𝓤
spec-dlat-equivalence 𝓤 = s , (r , †) , r , ‡
 where
  open 𝒦-Duality
  open 𝒦-Lattice

  s : Spectral-Locale 𝓤 → DistributiveLattice 𝓤
  s (X , σ) = 𝒦⦅X⦆⁻ X σ

  open DefnOfFrameOfIdeal

  r : DistributiveLattice 𝓤 → Spectral-Locale 𝓤
  r L = locale-of-spectra L , Spectrality.spec-L-is-spectral sr L , Spectrality.spec-L-has-small-𝒦 sr L

  foo : (L : DistributiveLattice 𝓤) → L ≅d≅ s (r L)
  foo = {!!}

  bar : ((X , σ) : Spectral-Locale 𝓤) → spec-𝒦-X X σ ≅c≅ X
  bar (X , σ)= record { 𝓈 = (ϕ₀ X σ) , {!!} ; 𝓇 = join X σ , {!!} ; 𝓇-cancels-𝓈 = join-cancels-ϕ X σ ; 𝓈-cancels-𝓇 = ϕ-cancels-join X σ }

  † : s ∘ r ∼ id
  † L = {!!}

  ‡ : r ∘ s ∼ id
  ‡ (X , σ) =
   to-subtype-＝
    (holds-is-prop ∘ is-spectral-with-small-basis ua)
    (homeomorphic-locales-are-equal (locale-of-spectra (s (X , σ))) X (bar (X , σ)))

\end{todo}
