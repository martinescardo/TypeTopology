Ayberk Tosun, 24 January 2024

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Size
open import UF.Univalence

module Locales.NewTerminology (pt : propositional-truncations-exist)
                              (fe : Fun-Ext)
                              (sr : Set-Replacement pt)
                              (ua : Univalence) where

open import UF.FunExt
open import UF.Subsingletons
open import UF.Logic
open import MLTT.Spartan
open import UF.Size
open import UF.Base
open import UF.EquivalenceExamples using (Σ-assoc)
open import UF.SubtypeClassifier
open import UF.Logic

open AllCombinators pt fe

open import Locales.Frame pt fe
open import Locales.SmallBasis pt fe sr

open PropositionalTruncation pt

\end{code}

\begin{code}

has-specified-intensional-spectral-basis : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → 𝓤 ⁺  ̇
has-specified-intensional-spectral-basis X = spectralᴰ X

\end{code}

\begin{code}

has-unspecified-intensional-spectral-basis : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Ω (𝓤 ⁺)
has-unspecified-intensional-spectral-basis X =
 ∥ has-specified-intensional-spectral-basis X ∥Ω

\end{code}

\begin{code}

split-support-result : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                     → has-unspecified-intensional-spectral-basis X holds
                     → has-specified-intensional-spectral-basis X
split-support-result = truncated-spectralᴰ-implies-spectralᴰ ua

\end{code}
