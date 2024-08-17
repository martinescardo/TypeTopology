---
title:         Stone duality for spectral locales
author:        Ayberk Tosun
date-started:  2024-04-12
dates-updated: [2024-05-08, 2024-06-20]
---

This module will eventually contain the proof of Stone duality for spectral
locales. It currently contains the type equivalence, which will be extended to
the categorical equivalence in the future.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚; ₀; ₁)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Locales.StoneDuality.ForSpectralLocales
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Locales.Compactness pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.ContinuousMap.Homeomorphism-Definition pt fe
open import Locales.ContinuousMap.Homeomorphism-Properties ua pt sr
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.DistributiveLattice.Isomorphism fe pt
open import Locales.DistributiveLattice.Isomorphism-Properties ua pt sr
open import Locales.DistributiveLattice.Resizing ua pt sr
open import Locales.DistributiveLattice.Spectrum fe pe pt
open import Locales.DistributiveLattice.Spectrum-Properties fe pe pt sr
open import Locales.Frame pt fe
open import Locales.SIP.DistributiveLatticeSIP ua pt sr
open import Locales.SIP.FrameSIP
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.LatticeOfCompactOpens-Duality ua pt sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Slice.Family
open import UF.Equiv
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale

\end{code}

We denote by `spec L` the spectrum (the locale defined by the frame of ideals)
of a distributive lattice `L`.

\begin{code}

open DefnOfFrameOfIdeal

spec : DistributiveLattice 𝓤 → Locale (𝓤 ⁺) 𝓤 𝓤
spec = spectrum

\end{code}

Recall that a locale `X` is called `spectral·` if it is homeomorphic to the
spectrum of some distributive lattice `L `.

\begin{code}

_ : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
  → is-spectral· X ＝ (Ǝ L ꞉ DistributiveLattice 𝓤 , X ≅c≅ spec L)
_ = λ _ → refl

\end{code}

This definition uses `∃` instead of `Σ`, because even though the distributive
lattice of compact opens is unique, the homeomorphism involved need not be.

Because `spec L` is a spectral locale (with a small basis), any locale `X` that
is homeomorphic to `spec L` for some distributive lattice `L` must be spectral.

\begin{code}

spectral·-implies-spectral-with-small-basis
 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
 → is-spectral· X holds
 → is-spectral-with-small-basis ua X holds
spectral·-implies-spectral-with-small-basis {𝓤} X =
 ∥∥-rec (holds-is-prop (is-spectral-with-small-basis ua X)) †
  where
   open PropositionalTruncation pt

   † : (Σ L ꞉ DistributiveLattice 𝓤 , X ≅c≅ spec L)
     → is-spectral-with-small-basis ua X holds
   † (L , 𝒽) = transport (_holds ∘ is-spectral-with-small-basis ua) q 𝕤
    where
     open Spectrality L

     p : 𝒪 (spec L) ＝ 𝒪 X
     p = isomorphic-frames-are-equal ua pt sr (𝒪 (spec L)) (𝒪 X) 𝒽

     q : spec L ＝ X
     q = to-locale-＝ (spec L) X p

     𝕤 : is-spectral-with-small-basis ua (spec L) holds
     𝕤 = spec-L-is-spectral , spec-L-has-small-𝒦

\end{code}

Added on 2024-05-12.

The converse of this implication is proved in the module
`LatticeOfCompactOpens-Duality`.

\begin{code}

spectral-with-small-basis-implies-spectral·
 : {𝓤 : Universe} (X : Locale (𝓤 ⁺) 𝓤 𝓤)
 → (is-spectral-with-small-basis ua X ⇒ is-spectral· X) holds
spectral-with-small-basis-implies-spectral· X σ = spectral-implies-spectral· X σ

\end{code}

We now explicitly record this logical equivalence.

\begin{code}

spectral-with-small-basis-iff-spectral·
 : {𝓤 : Universe} (X : Locale (𝓤 ⁺) 𝓤 𝓤)
 → (is-spectral-with-small-basis ua X ⇔ is-spectral· X) holds
spectral-with-small-basis-iff-spectral· X = † , ‡
 where
  † = spectral-with-small-basis-implies-spectral· X
  ‡ = spectral·-implies-spectral-with-small-basis X

\end{code}

Added on 2024-06-20.

We now show that the type `Spectral-Locale 𝓤` is equivalent to the type
`DistributiveLattice 𝓤`.

Recall that the type of spectral locales is defined as:

\begin{code}

Spectral-Locale : (𝓤 : Universe) → 𝓤 ⁺⁺  ̇
Spectral-Locale 𝓤 =
 Σ X ꞉ Locale (𝓤 ⁺) 𝓤 𝓤 , is-spectral-with-small-basis ua X holds

\end{code}

For any universe `𝓤`, the type `Spectral-Locale 𝓤` is equivalent to the type
`DistributiveLattice 𝓤`.

\begin{code}

spec-dlat-equivalence : (𝓤 : Universe) → Spectral-Locale 𝓤 ≃ DistributiveLattice 𝓤
spec-dlat-equivalence 𝓤 = sec , qinvs-are-equivs sec γ
 where
  open 𝒦-Duality₁
  open 𝒦-Lattice
  open DefnOfFrameOfIdeal

  sec : Spectral-Locale 𝓤 → DistributiveLattice 𝓤
  sec = uncurry ⦅_⦆ᶜ

  ret : DistributiveLattice 𝓤 → Spectral-Locale 𝓤
  ret L = spectrum L
        , Spectrality.spec-L-is-spectral L
        , Spectrality.spec-L-has-small-𝒦 L

  † : ret ∘ sec ∼ id
  † (X , σ) =
   to-subtype-＝
    (holds-is-prop ∘ is-spectral-with-small-basis ua)
    (homeomorphic-locales-are-equal (spec 𝒦X⁻) X 𝒽)
     where
      𝒦X⁻ : DistributiveLattice 𝓤
      𝒦X⁻ = ⦅_⦆ᶜ X σ

      𝒽 : spec 𝒦X⁻ ≅c≅ X
      𝒽 = X-is-homeomorphic-to-spec-𝒦⁻X X σ

  ‡ : sec ∘ ret ∼ id
  ‡ L = isomorphic-distributive-lattices-are-equal (sec (ret L)) L iso
   where
    open 𝒦-Duality₂ L

    iso : 𝒦⁻-spec-L ≅d≅ L
    iso = ≅d-sym L 𝒦⁻-spec-L L-is-isomorphic-to-𝒦⁻-spec-L

  γ : qinv sec
  γ = ret , † , ‡

\end{code}

\section{Morphisms}

\begin{code}

module spec-stone-duality-morphisms
        (X : Locale (𝓤 ⁺) 𝓤 𝓤)
        (Y : Locale (𝓤 ⁺) 𝓤 𝓤)
        (σ₁ : is-spectral-with-small-basis ua X holds)
        (σ₂ : is-spectral-with-small-basis ua Y holds)
       where

 open ContinuousMaps
 open 𝒦-Lattice X σ₁ renaming (𝒦⁻ to 𝒦⁻X)
 open 𝒦-Lattice Y σ₂ renaming (𝒦⦅X⦆-is-small to 𝒦⦅Y⦆-is-small; 𝒦⦅X⦆ to 𝒦⦅Y⦆; 𝒦⁻ to 𝒦⁻Y)

 e₁ : 𝒦⁻X ≃ 𝒦 X
 e₁ = resizing-condition 𝒦⦅X⦆-is-small

 s₁ : 𝒦⁻X → 𝒦 X
 s₁ = ⌜ e₁ ⌝

 r₁ : 𝒦 X → 𝒦⁻X
 r₁ = ⌜ ≃-sym e₁ ⌝

 e₂ : 𝒦⁻Y ≃ 𝒦 Y
 e₂ = resizing-condition 𝒦⦅Y⦆-is-small

 r₂ : 𝒦 Y → 𝒦⁻Y
 r₂ = ⌜ ≃-sym e₂ ⌝

 s₂ = ⌜ e₂ ⌝

 open DistributiveLatticeResizing 𝒦⦅X⦆ 𝒦⁻X (≃-sym e₁) using () renaming (Lᶜ to 𝒦⦅X⦆⁻; 𝟏ᶜ to 𝟏⁻X)
 open DistributiveLatticeResizing 𝒦⦅Y⦆ 𝒦⁻Y (≃-sym e₂) using () renaming (Lᶜ to 𝒦⦅Y⦆⁻; 𝟏ᶜ to 𝟏⁻𝒦Y)


 to-spectral-map : Spectral-Map X Y → (𝒦⦅Y⦆⁻ ─d→ 𝒦⦅X⦆⁻)
 to-spectral-map (𝒻@(f , _) , σ) =
  record { h = h ; h-is-homomorphism = α , β , {!!} }
   where
    open 𝒦-Duality₁ Y σ₂ using (ι; ι-gives-compact-opens; ι-preserves-𝟏)
    open DistributiveLattice 𝒦⦅X⦆ hiding (X) renaming (𝟏 to 𝟏ₓ; _∧_ to _∧ₓ_)
    open DistributiveLattice 𝒦⦅Y⦆ hiding (X) renaming (𝟏 to 𝟏y; _∧_ to _∧y_)
    open PropositionalTruncation pt

    h : 𝒦⁻Y → 𝒦⁻X
    h K = r₁ (f (ι K) , σ (ι K) κ)
     where
      κ : is-compact-open Y (ι K) holds
      κ = ι-gives-compact-opens K

    α : preserves-𝟏 𝒦⦅Y⦆⁻ 𝒦⦅X⦆⁻ h holds
    α = h 𝟏⁻𝒦Y      ＝⟨ refl ⟩
        h (r₂ 𝟏y)   ＝⟨ refl   ⟩
        r₁ (f (ι (r₂ 𝟏y)) , σ (ι (r₂ 𝟏y)) (ι-gives-compact-opens (r₂ 𝟏y)))   ＝⟨ †   ⟩
        r₁ 𝟏ₓ       ＝⟨ refl ⟩
        𝟏⁻X         ∎
         where
          p : f (ι (r₂ 𝟏y)) ＝ 𝟏[ 𝒪 X ]
          p = f (ι (r₂ 𝟏y)) ＝⟨ refl ⟩
              f (ι 𝟏⁻𝒦Y)    ＝⟨ ap f ι-preserves-𝟏 ⟩
              f 𝟏[ 𝒪 Y ]    ＝⟨ frame-homomorphisms-preserve-top (𝒪 Y) (𝒪 X) 𝒻  ⟩
              𝟏[ 𝒪 X ] ∎

          † = ap r₁ (to-𝒦-＝ X (σ (ι (r₂ 𝟏y)) (ι-gives-compact-opens (r₂ 𝟏y))) (𝒦-Lattice.𝟏-is-compact X σ₁) p)

    β : preserves-∧ 𝒦⦅Y⦆⁻ 𝒦⦅X⦆⁻ h holds
    β x y = h (r₂ (s₂ x ∧y s₂ y))       ＝⟨ {!!} ⟩
            h {!!}                      ＝⟨ {!!} ⟩
            r₁ (s₁ (h x) ∧ₓ s₁ (h y))   ∎

 σᴰ₁ : spectralᴰ X
 σᴰ₁ = ssb-implies-spectralᴰ ua X σ₁

 σᴰ₂ : spectralᴰ Y
 σᴰ₂ = ssb-implies-spectralᴰ ua Y σ₂

 ℬY : Fam 𝓤 ⟨ 𝒪 Y ⟩
 ℬY = basisₛ Y σᴰ₂

 ℬYₖ : Fam 𝓤 ∣ 𝒦⦅Y⦆⁻ ∣ᵈ
 ℬYₖ = index ℬY , λ i → r₂ (ℬY [ i ] , basisₛ-consists-of-compact-opens Y σᴰ₂ i)

 to-dlat-map : (𝒦⦅Y⦆⁻ ─d→ 𝒦⦅X⦆⁻) → Spectral-Map X Y
 to-dlat-map 𝒽 = 𝒻 , 𝕤
  where
   open PropositionalTruncation pt
   open 𝒦-Duality₁ X σ₁ using (ι)

   open Homomorphismᵈᵣ 𝒽 using (h)

   𝒥 = cover-indexₛ Y σᴰ₂

   f : ⟨ 𝒪 Y ⟩ → ⟨ 𝒪 X ⟩
   f U = ⋁[ 𝒪 X ] ⁅ ι (h (ℬYₖ [ j ])) ∣ j ε cover-indexₛ Y σᴰ₂ U ⁆


   lemma : (𝒦@(K , _) : 𝒦 Y) → f K ＝ ι (h (r₂ 𝒦))
   lemma 𝒦@(K , κ) = ∥∥-rec carrier-of-[ poset-of (𝒪 X) ]-is-set γ †₀
    where
     T : Fam 𝓤 ⟨ 𝒪 Y ⟩
     T = ⁅ ℬY [ j ] ∣ j ε cover-indexₛ Y σᴰ₂ K ⁆

     † : K ＝ ⋁[ 𝒪 Y ] T
     † = basisₛ-covers-do-cover-eq Y σᴰ₂ K

     †₀ : (Ǝ j ꞉ index (cover-indexₛ Y σᴰ₂ K) , (K ≤[ poset-of (𝒪 Y) ] ℬY [ 𝒥 K [ j ] ]) holds) holds
     †₀ = κ
           ⁅ ℬY [ j ] ∣ j ε cover-indexₛ Y σᴰ₂ K ⁆
           (basisₛ-covers-are-directed Y σᴰ₂ K)
           (reflexivity+ (poset-of (𝒪 Y)) †)


     γ : (Σ j ꞉ index (cover-indexₛ Y σᴰ₂ K) , (K ≤[ poset-of (𝒪 Y) ] ℬY [ 𝒥 K [ j ] ]) holds)
       → f K ＝ ι (h (r₂ 𝒦))
     γ (j , q) = f K                   ＝⟨ ap f r ⟩
                 f (ℬY [ 𝒥 K [ j ] ])  ＝⟨ {!!} ⟩
                 ι (h (r₂ 𝒦))          ∎
      where
       open PosetReasoning (poset-of (𝒪 Y)) renaming (_■ to _𝒬ℰ𝒟)

       q₀ : (ℬY [ 𝒥 K [ j ] ] ≤[ poset-of (𝒪 Y) ] K) holds
       q₀ = ℬY [ 𝒥 K [ j ] ]    ≤⟨ ⋁[ 𝒪 Y ]-upper T j ⟩
            ⋁[ 𝒪 Y ] T          ＝⟨ † ⁻¹ ⟩ₚ
            K                   𝒬ℰ𝒟

       r : K ＝ ℬY [ 𝒥 K [ j ] ]
       r = ≤-is-antisymmetric (poset-of (𝒪 Y)) q q₀

   α : preserves-top (𝒪 Y) (𝒪 X) f holds
   α = {!!}

   β : {!!}
   β = {!!}

   γ : {!!}
   γ = {!!}

   𝒻 : X ─c→ Y
   𝒻 = f , α , β , γ

   𝕤 : is-spectral-map Y X 𝒻 holds
   𝕤 K κ S δ p = {!!}

\end{code}
