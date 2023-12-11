\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.PatchJournalIndex (pt : propositional-truncations-exist)
                                 (fe : Fun-Ext)                          where

open import Locales.Frame pt fe
open import Locales.Nucleus pt fe
open import MLTT.Spartan hiding (𝟚)
open import UF.Embeddings
open import UF.Size
open import UF.SubtypeClassifier

open Locale

\end{code}

𝓥-small type.

\begin{code}

defn∶vsmall : (𝓥 : Universe) → 𝓤  ̇ → 𝓤 ⊔ 𝓥 ⁺  ̇
defn∶vsmall 𝓥 A = A is 𝓥 small

\end{code}

Being small is a proposition.

\begin{code}

-- prop∶being-small-is-prop

\end{code}

\begin{code}

defn∶local-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺  ̇
defn∶local-resizing 𝓤 𝓥 = propositional-resizing 𝓤 𝓥

\end{code}

\begin{code}

defn∶global-resizing : 𝓤ω
defn∶global-resizing = Propositional-Resizing

\end{code}

\begin{code}

open import Slice.Family

defn∶family : (𝓦 : Universe) → 𝓤  ̇ → 𝓤 ⊔ 𝓦 ⁺  ̇
defn∶family = Fam

\end{code}

\begin{code}

defn∶embedding : {X : 𝓤  ̇} {Y : 𝓥  ̇} → (X → Y) → 𝓤 ⊔ 𝓥  ̇
defn∶embedding = is-embedding

\end{code}

\begin{code}

defn∶nucleus : Frame 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥  ̇
defn∶nucleus = Nucleus

\end{code}

Definition of the way below relation.

\begin{code}

open import Locales.WayBelowRelation.Definition pt fe

defn∶way-below : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
defn∶way-below X = way-below (𝒪 X)

\end{code}

Definition of compactness.

\begin{code}

open import Locales.Compactness pt fe

defn∶compact-locale : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
defn∶compact-locale = is-compact

\end{code}

Definition of spectral locale.

\begin{code}

open import Locales.Spectrality.SpectralLocale pt fe

defn∶spectral-locale : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
defn∶spectral-locale = is-spectral

\end{code}
