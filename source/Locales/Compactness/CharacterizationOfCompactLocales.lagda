---
title:        Characterization of compact locales
author:       Ayberk Tosun
date-started: 2025-04-23
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.Classifiers
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

module Locales.Compactness.CharacterizationOfCompactLocales
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (sr : Set-Replacement pt)
       where

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.CompactRegular pt fe
 using (clopens-are-compact-in-compact-frames;
        is-clopen;
        compacts-are-clopen-in-zero-dimensional-locales;
        frame-homomorphisms-preserve-complements;
        complementation-is-symmetric; is-complement-of)
open import Locales.Compactness.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe renaming (⟨_⟩ to ⟨_⟩∙) hiding (∅)
open import Locales.GaloisConnection pt fe
open import Locales.InitialFrame pt fe
open import Locales.PerfectMaps pt fe
open import Locales.Spectrality.SpectralityOfOmega pt fe sr
open import Locales.TerminalLocale.Properties pt fe sr
open import Notation.UnderlyingType
open import Slice.Family
open import UF.Logic

open AllCombinators pt fe
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

instance
 underlying-type-of-frame : Underlying-Type (Frame 𝓤 𝓥 𝓦) (𝓤  ̇ )
 ⟨_⟩ {{underlying-type-of-frame}} (A , _) = A

\end{code}

\section{Preliminaries}

The universal property of the inital frame gives that there is a unique frame
homomorphism `Ω → 𝒪(X)`, for every locale `X`. We denote this by `‼`. We also
define the shorthand notation `‼⁺` for the underlying function of the frame
homomorphism in consideration.

\begin{code}

‼_ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → 𝟎-𝔽𝕣𝕞 pe ─f→ 𝒪 X
‼ X = center (𝟎-𝔽𝕣𝕞-initial pe (𝒪 X))

‼⁺[_]_ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Ω 𝓤 → ⟨ 𝒪 X ⟩
‼⁺[_]_ X = fun (𝟎-𝔽𝕣𝕞 pe) (𝒪 X) (‼ X)

\end{code}

We also define some shorthand notation for the right adjoint of this map. We
know that this exists since the initial frame has a small base.

\begin{code}

‼₊[_]_ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → ⟨ 𝒪 X ⟩ → Ω 𝓤
‼₊[_]_ {𝓤} X = ‼ X ⁎·_
 where
  open Spectrality-of-𝟎 𝓤 pe
  open AdjointFunctorTheorem pt fe X (𝟏Loc pe) ∣ ℬ𝟎↑ , ℬ𝟎↑-is-basis ∣

\end{code}

\section{Characterization of compactness}

The subscript `_⁺` is intended to approximate the right adjoint notation `_^*`.
Unfortunately, however, there is no superscript asterisk in unicode, so we use
the superscript plus instead.

We work in a module parameterized by a locale `X`, being the locale whose
compactness we are interested in.

\begin{code}

module CharacterizationOfCompactLocales (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open Spectrality-of-𝟎 𝓤 pe

 open AdjointFunctorTheorem pt fe X (𝟏Loc pe) ∣ ℬ𝟎↑ , ℬ𝟎↑-is-basis ∣
 open PerfectMaps X (𝟏Loc pe) ∣ ℬ𝟎↑ , ℬ𝟎↑-is-basis ∣
 open SpectralMaps X (𝟏Loc pe)


\end{code}

An alternative way to express that a locale `X` is compact is by asserting that
the map `‼ X` is perfect, which is to say that its right adjoint is Scott
continuous.

\begin{code}

 is-compact' : Ω (𝓤 ⁺)
 is-compact' = is-perfect-map (‼ X)

\end{code}

Because a map into a spectral locale is perfect if and only if it reflects
compact opens (i.e. is “spectral”), this could also be formulated as:

\begin{code}

 is-compact'' : Ω (𝓤 ⁺)
 is-compact'' = is-spectral-map (‼ X)

 compact'-implies-compact'' : (is-compact' ⇒ is-compact'') holds
 compact'-implies-compact'' = perfect-maps-are-spectral (‼ X)

 compact''-implies-compact' : (is-compact'' ⇒ is-compact') holds
 compact''-implies-compact' φ =
  spectral-maps-are-perfect (𝟎-𝔽𝕣𝕞-is-spectral 𝓤 pe) (‼ X) φ

\end{code}

We now prove that this alternative formulation of compactness implies the
standard one.

The proof is quite simple:

  - We have to show that the top `𝟏[ 𝒪 X ]` is compact.
  - Because `‼⁺[ X ]` is a frame homomorphism, we have that `𝟏 = ‼⁺[ X ] ⊤`,
    so it suffices to show that `‼⁺[ X ] ⊤` is compact.
  - Since we are given that `‼⁺[ X ] ⊤` preserves compact opens, we just
    have to show that `⊤` is compact, which we know since the terminal locale
    is compact.

\begin{code}

 compact-implies-compact' : (is-compact' ⇒ is-compact X) holds
 compact-implies-compact' κ =
  transport (λ - → is-compact-open X - holds) (q ⁻¹) †
   where
    open Spectrality-of-𝟎 𝓤 pe

    q : 𝟏[ 𝒪 X ] ＝ ‼⁺[ X ] ⊤
    q = frame-homomorphisms-preserve-top (𝟎-𝔽𝕣𝕞 pe) (𝒪 X) (‼ X) ⁻¹

    𝕤 : SpectralMaps.is-spectral-map X (𝟏Loc pe) (‼ X) holds
    𝕤 = perfect-maps-are-spectral (‼ X) κ

    † : is-compact-open X (‼⁺[ X ] ⊤) holds
    † = 𝕤 𝟏[ 𝟎-𝔽𝕣𝕞 pe ] (𝟎Frm-is-compact 𝓤 pe)

\end{code}

We now tackle the other direction.

- Suppose `X` is compact in the standard sense.
- Let `K : Ω` be a compact open of the terminal locale.
- We need to show that `‼⁺[ X ] K` is compact.
- Since `X` is and clopens are compact in compact frames, we simply have to
  show that `‼⁺[ X ] K`.
- This is easy since we already know that `K` is a clopen in `Ω` (since `Ω` is
  a Stone locale) and frame homomorphisms preserve complements.

\begin{code}

 compact'-implies-compact : (is-compact X ⇒ is-compact') holds
 compact'-implies-compact κ = compact''-implies-compact' †
   where
    † : is-spectral-map (‼ X) holds
    † P 𝕔 = clopens-are-compact-in-compact-frames (𝒪 X) κ (‼⁺[ X ] P) ‡
     where
      ψ : is-clopen (𝟎-𝔽𝕣𝕞 pe) P holds
      ψ = compact-implies-clopen pe P 𝕔

      P′ : Ω 𝓤
      P′ = pr₁ ψ

      ν : is-complement-of (𝒪 X) (‼⁺[ X ] P′) (‼⁺[ X ] P)
      ν = frame-homomorphisms-preserve-complements
           (𝟎-𝔽𝕣𝕞 pe)
           (𝒪 X)
           (‼ X)(complementation-is-symmetric (𝟎-𝔽𝕣𝕞 pe) _ _ (pr₂ ψ))

      ‡ : is-clopen (𝒪 X) (‼⁺[ X ] P) holds
      ‡ = (‼⁺[ X ] P′) , ν

\end{code}
