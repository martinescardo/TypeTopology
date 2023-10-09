\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.PatchJournalIndex (pt : propositional-truncations-exist)
                                 (fe : Fun-Ext)                          where

open import MLTT.Spartan           hiding (𝟚)
open import UF.SubtypeClassifier

open import Locales.Frame                      pt fe

\end{code}

The definition of compactness

\begin{code}

open import Locales.Compactness pt fe

defn∶compact-locale : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
defn∶compact-locale = is-compact

\end{code}

The definition of spectral locale.

\begin{code}

open import Locales.Spectrality.SpectralLocale pt fe

defn∶spectral-locale : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
defn∶spectral-locale = is-spectral

\end{code}
