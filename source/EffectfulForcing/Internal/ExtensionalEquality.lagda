---
authors:
  - Bruno da Rocha Paiva
  - Vincent Rahli
date: 2023-11-08
---

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.ExtensionalEquality where

open import MLTT.Spartan hiding (rec ; _^_) renaming (⋆ to 〈〉)
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type ; ι ; _⇒_ ; 〖_〗)

\end{code}

\begin{code}

_≡_ : {A : type} (f g : 〖 A 〗) → 𝓤₀  ̇
_≡_ {ι}     n₁ n₂ = n₁ ＝ n₂
_≡_ {σ ⇒ τ} f₁ f₂ = {x₁ x₂ : 〖 σ 〗} → x₁ ≡ x₂ → f₁ x₁ ≡ f₂ x₂

≡T : (A : type) (f g : 〖 A 〗) → Type
≡T A f g = f ≡ g

syntax ≡T A f g = f ≡[ A ] g

\end{code}
