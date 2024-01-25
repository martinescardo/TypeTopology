Martin Escardo, 29 June 2018

The subtype Ordinalsᵀ of ordinals with a top element.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Ordinals.ToppedType
        (fe : FunExt)
       where

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Sets
open import UF.Subsingletons

\end{code}

To get closure under sums constructively, we need to restrict to
particular kinds of ordinals. Having a top element is a simple
sufficient condition, which holds in the applications we have in mind
(for compact ordinals).  Classically, the topped ordinals are the
successor ordinals. Constructively, ℕ∞ is an example of an ordinal
with a top element which is not a successor ordinal, as its top
element is not isolated.

\begin{code}

Ordinalᵀ : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinalᵀ 𝓤 = Σ α ꞉ Ordinal 𝓤 , has-top (underlying-order α)

instance
 canonical-map-Ordinalᵀ-Ordinal : Canonical-Map (Ordinalᵀ 𝓤) (Ordinal 𝓤)
 ι {{canonical-map-Ordinalᵀ-Ordinal}} (α , _) = α

instance
 underlying-type-of-topped-ordinal : Underlying (Ordinalᵀ 𝓤)
 ⟨_⟩ {{underlying-type-of-topped-ordinal}} (α , _) = ⟨ α ⟩
 underlying-order {{underlying-type-of-topped-ordinal}} (α , _) = underlying-order α

underlying-type-is-setᵀ : FunExt
                        → (β : Ordinalᵀ 𝓤)
                        → is-set ⟨ β ⟩
underlying-type-is-setᵀ fe (α , t) = underlying-type-is-set fe α

\end{code}

Topped ordinals are ranged over by τ,υ.

\begin{code}

tis-well-ordered : (τ : Ordinalᵀ 𝓤) → is-well-order (underlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

≾-prop-valued : (τ : Ordinalᵀ 𝓤) (x y : ⟨ τ ⟩) → is-prop (x ≾⟨ τ ⟩ y)
≾-prop-valued {𝓤} τ = ≾-is-prop-valued
                       (underlying-order τ)
                       (fe 𝓤 𝓤₀)
                       (Prop-valuedness [ τ ])

topped : (τ : Ordinalᵀ 𝓤) → has-top (underlying-order τ)
topped (α , t) = t

top : (τ : Ordinalᵀ 𝓤) → ⟨ τ ⟩
top (α , (x , i)) = x

top-is-top : (τ : Ordinalᵀ 𝓤) → is-top (underlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

open import TypeTopology.InfProperty

has-infs-of-complemented-subsets : Ordinalᵀ 𝓤 → 𝓤 ̇
has-infs-of-complemented-subsets τ = has-inf (underlying-weak-order τ)

\end{code}
