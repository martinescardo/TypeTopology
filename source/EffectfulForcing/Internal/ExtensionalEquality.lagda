---
authors:
  - Bruno da Rocha Paiva
  - Vincent Rahli
date-started: 2023-11-08
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EffectfulForcing.Internal.ExtensionalEquality where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type ; ι ; _⇒_ ; 〖_〗)

\end{code}

Extensional equality of System T terms.

\begin{code}

_≡_ : {A : type} → 〖 A 〗 → 〖 A 〗 → 𝓤₀ ̇
_≡_ {ι}     n₁ n₂ = n₁ ＝ n₂
_≡_ {σ ⇒ τ} f₁ f₂ = {x₁ x₂ : 〖 σ 〗} → x₁ ≡ x₂ → f₁ x₁ ≡ f₂ x₂

\end{code}

The following explicit version is used to define a nice syntax for the
extensional equality operation.

\begin{code}

≡-syntax : (A : type) → 〖 A 〗 → 〖 A 〗 → 𝓤₀ ̇
≡-syntax A f g = f ≡ g

syntax ≡-syntax A f g = f ≡[ A ] g

\end{code}
