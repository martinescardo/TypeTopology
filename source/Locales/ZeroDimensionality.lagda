Ayberk Tosun, 11 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt

module Locales.ZeroDimensionality (pt : propositional-truncations-exist)
                                  (fe : Fun-Ext)                           where

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
open import Locales.WayBelow         pt fe
open import Locales.Compactness      pt fe
open import Locales.Complements      pt fe
open import Locales.GaloisConnection pt fe
open import Locales.InitialFrame     pt fe
open import Locales.Clopen           pt fe

open Locale

\end{code}

\begin{code}

zero-dimensionalᴰ : Frame 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
zero-dimensionalᴰ {𝓦 = 𝓦} F =
 Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , is-directed-basis F ℬ
                   × consists-of-clopens F ℬ holds

\end{code}

\begin{code}

basis-of-zero-dimensionalᴰ-frame : (L : Frame 𝓤 𝓥 𝓦)
                                 → zero-dimensionalᴰ L
                                 → Σ ℬ ꞉ Fam 𝓦 ⟨ L ⟩ , is-basis-for L ℬ
basis-of-zero-dimensionalᴰ-frame L (ℬ , (β , _) , _) = ℬ , β

is-zero-dimensional : Frame 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-zero-dimensional {𝓦 = 𝓦} F = ∥ zero-dimensionalᴰ F ∥Ω

\end{code}
