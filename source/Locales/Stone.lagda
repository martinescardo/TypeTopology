Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Size

module Locales.Stone (pt : propositional-truncations-exist)
                     (fe : Fun-Ext)
                     (sr : Set-Replacement pt)               where

\end{code}

Importation of foundational UF stuff.

\begin{code}

open import Slice.Family
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

Importations of other locale theory modules.

\begin{code}

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Frame            pt fe
open import Locales.WayBelowRelation.Definition pt fe
open import Locales.Compactness      pt fe
open import Locales.Complements      pt fe
open import Locales.GaloisConnection pt fe
open import Locales.InitialFrame     pt fe
open import Locales.ZeroDimensionality pt fe sr

open Locale

\end{code}

\begin{code}

stoneᴰ : (X : Locale 𝓤 𝓥 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
stoneᴰ X = is-compact X holds × zero-dimensionalᴰ (𝒪 X)

\end{code}

\begin{code}

is-stone : (X : Locale 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-stone X = is-compact X ∧ is-zero-dimensional (𝒪 X)

\end{code}

\begin{code}

stoneᴰ-implies-stone : (X : Locale 𝓤 𝓥 𝓦) → stoneᴰ X → is-stone X holds
stoneᴰ-implies-stone X σᴰ@(κ , zd) = κ , ∣ zd ∣

\end{code}
