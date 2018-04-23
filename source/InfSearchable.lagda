Martin Escardo 20-21 December 2012

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module InfSearchable where

open import SpartanMLTT

putative-root : ∀ {U} {X : U ̇} → (X → 𝟚) → X → U ̇
putative-root p x₀ = (Σ \x → p x ≡ ₀) → p x₀ ≡ ₀

root-lower-bound : ∀ {U} {X : U ̇} → (X → X → U ̇) → (X → 𝟚) → X → U ̇
root-lower-bound R p l = ∀ x → p x ≡ ₀ → R l x

upper-bound-of-root-lower-bounds : ∀ {U} {X : U ̇} → (X → X → U ̇) → (X → 𝟚) → X → U ̇
upper-bound-of-root-lower-bounds R p u = ∀ l → root-lower-bound R p l → R l u

inf-searchable : ∀ {U} (X : U ̇) → (X → X → U ̇) → U ̇
inf-searchable X R = (p : X → 𝟚) 
                         → Σ \(x₀ : X) → putative-root p x₀ 
                                        × root-lower-bound R p x₀ 
                                        × upper-bound-of-root-lower-bounds R p x₀

\end{code}
