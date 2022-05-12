Two-point type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Two where

open import Universes

data 𝟚 : 𝓤₀ ̇ where
 ₀ : 𝟚
 ₁ : 𝟚

𝟚-induction : {A : 𝟚 → 𝓤 ̇ } → A ₀ → A ₁ → (x : 𝟚) → A x
𝟚-induction r s ₀ = r
𝟚-induction r s ₁ = s

𝟚-cases : {A : 𝓤 ̇ } → A → A → 𝟚 → A
𝟚-cases = 𝟚-induction

\end{code}
