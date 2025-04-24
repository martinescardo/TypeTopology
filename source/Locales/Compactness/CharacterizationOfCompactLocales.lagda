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
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

module Locales.Compactness.CharacterizationOfCompactLocales
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Compactness.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.Frame pt fe renaming (⟨_⟩ to ⟨_⟩∙) hiding (∅)
open import Locales.GaloisConnection pt fe
open import Slice.Family
open import Locales.InitialFrame pt fe
open import Locales.PerfectMaps pt fe
open import Locales.TerminalLocale.Properties pt fe
open import Notation.UnderlyingType
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
homomorphism `Ω → 𝒪(X)`, for every locale `X`. We denote this by `‼`

\begin{code}

‼_ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → 𝟎-𝔽𝕣𝕞 pe ─f→ 𝒪 X
‼ X = center (𝟎-𝔽𝕣𝕞-initial pe (𝒪 X))

\end{code}

We also define some shorthand notation for the right adjoint of this map, which
we know to exist since the initial frame has a small base.

\begin{code}

‼₊[_]_ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → ⟨ 𝒪 X ⟩ → Ω 𝓤
‼₊[_]_ {𝓤} X = ‼ X ⁎·_
 where
  open Spectrality-of-𝟎 𝓤 pe
  open AdjointFunctorTheorem pt fe X (𝟏Loc pe) ∣ ℬ𝟎↑ , ℬ𝟎↑-is-basis ∣

\end{code}

\section{Characterization of compactness}

An alternative way to express that a locale `X` is compact is by asserting that
the map `‼ X` is perfect.

\begin{code}

is-compact' : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Ω (𝓤 ⁺)
is-compact' {𝓤} X =
 PerfectMaps.is-perfect-map X (𝟏Loc pe) ∣ ℬ𝟎↑ , ℬ𝟎↑-is-basis ∣ (‼ X)
  where
   open Spectrality-of-𝟎 𝓤 pe

\end{code}

We now prove that this implies the standard definition of compact locale.

\begin{code}

compact-implies-compact' : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                         → (is-compact' X ⇒ is-compact X) holds
compact-implies-compact' X κ S δ p =
 ∥∥-rec ∃-is-prop γ (directedness-entails-inhabitation (𝒪 X) S δ)
  where
   † : ‼₊[ X ] (⋁[ 𝒪 X ] S) ＝ ⋁[ 𝟎-𝔽𝕣𝕞 pe ] ⁅ ‼₊[ X ] U ∣ U ε S ⁆
   † = ⋁[ 𝟎-𝔽𝕣𝕞 pe ]-unique ⁅ ‼₊[ X ] U ∣ U ε S ⁆
        (‼₊[ X ] (⋁[ 𝒪 X ] S))
        (κ S δ)

   γ : index S →
        ∃ (λ i → (poset-of (𝒪 X) PosetNotation.≤ 𝟏[ 𝒪 X ]) (S [ i ]) holds)
   γ i = {! !}

\end{code}
