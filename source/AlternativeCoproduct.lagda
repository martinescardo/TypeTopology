
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module AlternativeCoproduct where

open import SpartanMLTT
open import Two

_+'_ : ∀ {U} → U ̇ → U ̇ → U ̇
X₀ +' X₁ = Σ \(i : 𝟚) → X i
 where
  X : 𝟚 → _ ̇
  X ₀ = X₀
  X ₁ = X₁

\end{code}
