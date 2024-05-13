--------------------------------------------------------------------------------
title:          Lattice homomorphism given by a spectral map
author:         Ayberk Tosun
date-started:   2024-03-03
date-completed: 2024-03-04
--------------------------------------------------------------------------------

Any spectral map `f : X → Y` of spectral locales gives a lattice homomorphism
`𝒦(Y) → 𝒦(X)`. We prove this fact in this module.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.Logic
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UA-FunExt
open import UF.Univalence

module Locales.Spectrality.SpectralMapToLatticeHomomorphism
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

fe : Fun-Ext
fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

open import Locales.Compactness pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Homomorphism fe pt
open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.LatticeOfCompactOpens ua pt sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import UF.EquivalenceExamples

open AllCombinators pt fe
open ContinuousMaps
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

\end{code}

We fix large and locally small locales `X` and `Y` which we assume to be
spectral. We also fix a spectral map `f : X → Y`.

\begin{code}

module FunctorialAction
        (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
        (Y  : Locale (𝓤 ⁺) 𝓤 𝓤)
        (σ₁ : is-spectral-with-small-basis ua X holds)
        (σ₂ : is-spectral-with-small-basis ua Y holds)
        (f  : X ─c→ Y)
        (𝕤  : is-spectral-map Y X f holds)
       where

\end{code}

We denote by `𝒦⦅X⦆` and `𝒦⦅Y⦆` the distributive lattices of compact opens of
locales `X` and `Y` respectively.

\begin{code}

 open ContinuousMapNotation X Y
 open 𝒦-Lattice X σ₁ renaming (𝟏ₖ to 𝟏ₖ-X;
                               𝟏-is-compact to 𝟏-X-is-compact)
 open 𝒦-Lattice Y σ₂ renaming (𝟏ₖ to 𝟏ₖ-Y;
                               𝒦⦅X⦆ to 𝒦⦅Y⦆;
                               𝟏-is-compact to 𝟏-Y-is-compact)
 open OperationsOnCompactOpens X (pr₁ σ₁) renaming (_∨ₖ_ to _∨₂_; _∧ₖ_ to _∧₂_)
 open OperationsOnCompactOpens Y (pr₁ σ₂) renaming (_∨ₖ_ to _∨₁_; _∧ₖ_ to _∧₁_)

\end{code}

We denote by `𝒦-map₀` the underlying function of the lattice homomorphism
between the lattices of compact opens.

\begin{code}

 𝒦-map₀ : 𝒦 Y → 𝒦 X
 𝒦-map₀ (K , κ) = f ⋆∙ K , 𝕤 K κ

\end{code}

The proof that this is a lattice homomorphism is easy.

\begin{code}

 𝒦-map₀-preserves-𝟎 : 𝒦-map₀ 𝟎ₖ[ Y  ] ＝ 𝟎ₖ[ X ]
 𝒦-map₀-preserves-𝟎 =
  to-𝒦-＝
   X
   (𝕤 𝟎[ 𝒪 Y ] (𝟎-is-compact Y))
   (𝟎-is-compact X)
   (frame-homomorphisms-preserve-bottom (𝒪 Y) (𝒪 X) f)

 𝒦-map₀-preserves-𝟏 : 𝒦-map₀ 𝟏ₖ-Y ＝ 𝟏ₖ-X
 𝒦-map₀-preserves-𝟏 =
  to-𝒦-＝
   X
   (𝕤 𝟏[ 𝒪 Y ] 𝟏-Y-is-compact)
   𝟏-X-is-compact
   (frame-homomorphisms-preserve-top (𝒪 Y) (𝒪 X) f)

 𝒦-map₀-preserves-∨ : (K₁ K₂ : 𝒦 Y) → 𝒦-map₀ (K₁ ∨₁ K₂) ＝ 𝒦-map₀ K₁ ∨₂ 𝒦-map₀ K₂
 𝒦-map₀-preserves-∨ 𝔎₁@(K₁ , κ₁) 𝔎₂@(K₂ , κ₂) =
  to-𝒦-＝ X (𝕤 (K₁ ∨[ 𝒪 Y ] K₂) κ) κ′ †
   where
    κ : is-compact-open Y (K₁ ∨[ 𝒪 Y ] K₂) holds
    κ = compact-opens-are-closed-under-∨ Y K₁ K₂ κ₁ κ₂

    κ′ : is-compact-open X (f ⋆∙ K₁ ∨[ 𝒪 X ] f ⋆∙ K₂) holds
    κ′ = compact-opens-are-closed-under-∨ X (f ⋆∙ K₁) (f ⋆∙ K₂) (𝕤 K₁ κ₁) (𝕤 K₂ κ₂)

    † : f ⋆∙ (K₁ ∨[ 𝒪 Y ] K₂) ＝ f ⋆∙ K₁ ∨[ 𝒪 X ] f ⋆∙ K₂
    † = frame-homomorphisms-preserve-binary-joins (𝒪 Y) (𝒪 X) f K₁ K₂

 𝒦-map₀-preserves-∧ : (K₁ K₂ : 𝒦 Y) → 𝒦-map₀ (K₁ ∧₁ K₂) ＝ 𝒦-map₀ K₁ ∧₂ 𝒦-map₀ K₂
 𝒦-map₀-preserves-∧ (K₁ , κ₁) (K₂ , κ₂) =
  to-𝒦-＝ X (𝕤 (K₁ ∧[ 𝒪 Y ] K₂) κ) κ′ †
   where
    κ : is-compact-open Y (K₁ ∧[ 𝒪 Y ] K₂) holds
    κ = binary-coherence Y (ssb-implies-spectral ua Y σ₂) K₁ K₂ κ₁ κ₂

    κ′ : is-compact-open X (f ⋆∙ K₁ ∧[ 𝒪 X ] f ⋆∙ K₂) holds
    κ′ = binary-coherence
          X
          (ssb-implies-spectral ua X σ₁)
          (f ⋆∙ K₁)
          (f ⋆∙ K₂)
          (𝕤 K₁ κ₁)
          (𝕤 K₂ κ₂)

    † : f ⋆∙ (K₁ ∧[ 𝒪 Y ] K₂) ＝ f ⋆∙ K₁ ∧[ 𝒪 X ] f ⋆∙ K₂
    † = frame-homomorphisms-preserve-meets (𝒪 Y) (𝒪 X) f K₁ K₂

 𝒦-map₀-is-lattice-homomorphism : is-homomorphismᵈ 𝒦⦅Y⦆ 𝒦⦅X⦆ 𝒦-map₀ holds
 𝒦-map₀-is-lattice-homomorphism = 𝒦-map₀-preserves-𝟏
                                , 𝒦-map₀-preserves-∧
                                , 𝒦-map₀-preserves-𝟎
                                , 𝒦-map₀-preserves-∨

\end{code}

We package `𝒦-map₀` together with the proof that it is a lattice homomorphism
and call this `𝒦-map`.

\begin{code}

 𝒦-map : Homomorphismᵈᵣ 𝒦⦅Y⦆ 𝒦⦅X⦆
 𝒦-map = record
          { h                 = 𝒦-map₀
          ; h-is-homomorphism = 𝒦-map₀-is-lattice-homomorphism
          }

\end{code}

Finally, we put everything together to define a function `to-𝒦-map` that maps a
spectral map `f : X → Y` of spectral locales to a homomorphism `𝒦 Y → 𝒦 X` of
distributive lattices.

\begin{code}

module _ (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
         (Y  : Locale (𝓤 ⁺) 𝓤 𝓤)
         (σ₁ : is-spectral-with-small-basis ua X holds)
         (σ₂ : is-spectral-with-small-basis ua Y holds) where

 open FunctorialAction X Y σ₁ σ₂
 open 𝒦-Lattice X σ₁ renaming (𝟏ₖ to 𝟏ₖ-X;
                               𝟏-is-compact to 𝟏-X-is-compact)
 open 𝒦-Lattice Y σ₂ renaming (𝟏ₖ to 𝟏ₖ-Y; 𝒦⦅X⦆ to 𝒦⦅Y⦆;
                               𝟏-is-compact to 𝟏-Y-is-compact)

 to-𝒦-map : (X ─s→ Y) → 𝒦⦅Y⦆ ─d→ 𝒦⦅X⦆
 to-𝒦-map (f , 𝕤) = 𝒦-map f 𝕤

\end{code}
