Martin Escardo, 29 June 2018

The subtype Ordinalsᵀ of ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.FunExt

module Ordinals.ToppedType
        (fe : FunExt)
       where

open import MLTT.Spartan
open import Notation.UnderlyingType
open import Ordinals.Notions
open import Ordinals.Type

open import UF.Base
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
 underlying-type-of-topped-ordinal : Underlying-Type (Ordinalᵀ 𝓤) (𝓤 ̇)
 ⟨_⟩ {{underlying-type-of-topped-ordinal}} (α , _) = ⟨ α ⟩


underlying-type-is-setᵀ : FunExt
                        → (β : Ordinalᵀ 𝓤)
                        → is-set ⟨ β ⟩
underlying-type-is-setᵀ fe (α , t) = underlying-type-is-set fe α

\end{code}

Topped ordinals are ranged over by τ,υ.

\begin{code}

tunderlying-order : (τ : Ordinalᵀ 𝓤) → ⟨ τ ⟩ → ⟨ τ ⟩ → 𝓤 ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟨ τ ⟩ y

tunderlying-rorder : (τ : Ordinalᵀ 𝓤) → ⟨ τ ⟩ → ⟨ τ ⟩ → 𝓤 ̇
tunderlying-rorder τ x y = ¬ (y ≺⟨ τ ⟩ x)

syntax tunderlying-rorder τ x y = x ≼⟨ τ ⟩ y

≼-prop-valued : (τ : Ordinalᵀ 𝓤) (x y : ⟨ τ ⟩) → is-prop (x ≼⟨ τ ⟩ y)
≼-prop-valued {𝓤} τ x y l m = dfunext (fe 𝓤 𝓤₀) (λ x → 𝟘-elim (m x))

topped : (τ : Ordinalᵀ 𝓤) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordinalᵀ 𝓤) → ⟨ τ ⟩
top (α , (x , i)) = x

top-is-top : (τ : Ordinalᵀ 𝓤) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordinalᵀ 𝓤) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

open import TypeTopology.InfProperty

has-infs-of-complemented-subsets : Ordinalᵀ 𝓤 → 𝓤 ̇
has-infs-of-complemented-subsets α = has-inf (λ x y → x ≼⟨ α ⟩ y)

\end{code}
