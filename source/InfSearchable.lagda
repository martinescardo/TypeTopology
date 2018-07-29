Martin Escardo 20-21 December 2012

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module InfSearchable {U V} {X : U ̇} (_≤_ : X → X → V ̇) where

conditional-root : (X → 𝟚) → X → U ̇
conditional-root p x₀ = (Σ \(x : X) → p x ≡ ₀) → p x₀ ≡ ₀

root-lower-bound : (X → 𝟚) → X → U ⊔ V ̇
root-lower-bound p l = (x : X) → p x ≡ ₀ → l ≤ x

upper-bound-of-root-lower-bounds : (X → 𝟚) → X → U ⊔ V ̇
upper-bound-of-root-lower-bounds p u = (l : X) → root-lower-bound p l → l ≤ u

roots-infimum : (X → 𝟚) → X → U ⊔ V ̇
roots-infimum p x = root-lower-bound p x × upper-bound-of-root-lower-bounds p x

inf-searchable : U ⊔ V ̇
inf-searchable = (p : X → 𝟚) → Σ \(x : X) → conditional-root p x × roots-infimum p x

\end{code}
