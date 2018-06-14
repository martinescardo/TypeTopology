Martin Escardo 20-21 December 2012

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module InfSearchable {U} {X : U ̇} (_≤_ : X → X → U ̇) where

conditional-root : (X → 𝟚) → X → U ̇
conditional-root p x₀ = (Σ \x → p x ≡ ₀) → p x₀ ≡ ₀

root-lower-bound : (X → 𝟚) → X → U ̇
root-lower-bound p l = ∀ x → p x ≡ ₀ → l ≤ x

upper-bound-of-root-lower-bounds : (X → 𝟚) → X → U ̇
upper-bound-of-root-lower-bounds p u = ∀ l → root-lower-bound p l → l ≤ u

roots-infimum : (X → 𝟚) → X → U ̇
roots-infimum p x = root-lower-bound p x × upper-bound-of-root-lower-bounds p x

inf-searchable : U ̇
inf-searchable = (p : X → 𝟚) → Σ \(x : X) → conditional-root p x × roots-infimum p x

\end{code}
