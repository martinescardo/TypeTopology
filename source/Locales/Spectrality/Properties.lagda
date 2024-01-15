Ayberk Tosun, 13 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])
open import MLTT.Pi
open import Slice.Family
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Subsingletons-FunExt
open import UF.Logic

module Locales.Spectrality.Properties (pt : propositional-truncations-exist)
                                      (fe : Fun-Ext) where

open import Locales.Frame                      pt fe
open import Locales.Compactness                pt fe
open import Locales.Spectrality.SpectralLocale pt fe

open PropositionalTruncation pt

open AllCombinators pt fe

open Locale

\end{code}

Let `X` be a locale and let `U` and `V` be two opens of it. Consider the
following ordering:

    ∀ K : 𝒦(X). K ≤ U ⇒ K ≤ V

which says any compact open below `U` is also below `V`.

\begin{code}

compact-rel-syntax : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
compact-rel-syntax X U V = Ɐ (K , _) ꞉ 𝒦 X , K ≤ U ⇒ K ≤ V
 where
  open PosetNotation (poset-of (𝒪 X))

syntax compact-rel-syntax X U V = U ≤ₖ[ X ] V

\end{code}

We denote this `_≤ₖ_`

\begin{code}

spectral-yoneda : (X : Locale 𝓤 𝓥 𝓦)
                → is-spectral X holds
                → (U V : ⟨ 𝒪 X ⟩)
                → (U ≤ₖ[ X ] V) holds
                → (U ≤[ poset-of (𝒪 X) ] V) holds
spectral-yoneda {_} {_} {𝓦} X (_ , c) U V φ =
 ∥∥-rec (holds-is-prop (U ≤[ poset-of (𝒪 X) ] V)) † (c U)
  where
   open PosetReasoning (poset-of (𝒪 X))
   open PosetNotation  (poset-of (𝒪 X))
   open Joins _≤_

   † : Σ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ , consists-of-compact-opens X S holds
                           × is-directed (𝒪 X) S holds × (U ＝ ⋁[ 𝒪 X ] S)
     → (U ≤[ poset-of (𝒪 X) ] V) holds
   † (S , κ , d , c) = U ≤⟨ Ⅰ ⟩ ⋁[ 𝒪 X ] S ≤⟨ Ⅱ ⟩ V ■
     where
      ψ : (i : index S) → (S [ i ] ≤ U) holds
      ψ i = S [ i ] ≤⟨ ⋁[ 𝒪 X ]-upper S i ⟩ ⋁[ 𝒪 X ] S ＝⟨ c ⁻¹ ⟩ₚ U ■

      ‡ : (V is-an-upper-bound-of S) holds
      ‡ i = φ (S [ i ] , κ i) (ψ i)

      Ⅰ = reflexivity+ (poset-of (𝒪 X)) c
      Ⅱ = ⋁[ 𝒪 X ]-least S (V , ‡)

\end{code}
