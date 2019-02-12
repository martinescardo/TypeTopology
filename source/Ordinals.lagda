Martin Escardo, 29 June 2018

The type Ordinals of ordinals in a universe U, and the subtype Ordinalsᵀ of
ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Negation
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import OrdinalNotions hiding (_≤_)
open import UF-Embeddings

module Ordinals
       (fe : FunExt)
       where

OrdinalStructure : 𝓤 ̇ → 𝓤 ⁺ ̇
OrdinalStructure {𝓤} X = Σ \(_<_ : X → X → 𝓤 ̇) → is-well-order _<_

Ordinal : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinal 𝓤 = Σ \(X : 𝓤 ̇) → OrdinalStructure X

\end{code}

An ordinal is a type equipped with ordinal structure. Such a type is
automatically a set.

NB. Perhaps we will eventually need to have two parameters U (the
universe where the underlying type X lives) and V (the universe where
_<_ takes values in) for Ordinal.

Ordinals are ranged over by α,β,γ.

The underlying type of an ordinal (which happens to be necessarily a
set):

\begin{code}

⟨_⟩ : Ordinal 𝓤 → 𝓤 ̇
⟨ X , _<_ , o ⟩ = X

structure : (α : Ordinal 𝓤) → OrdinalStructure ⟨ α ⟩
structure (X , s) = s

underlying-order : (α : Ordinal 𝓤) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
underlying-order (X , _<_ , o) = _<_

underlying-porder : (α : Ordinal 𝓤) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
underlying-porder (X , _<_ , o) = _≼_ _<_

syntax underlying-order  α x y = x ≺⟨ α ⟩ y
syntax underlying-porder α x y = x ≼⟨ α ⟩ y

is-well-ordered : (α : Ordinal 𝓤) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : (α : Ordinal 𝓤) → is-prop-valued (underlying-order α)
Prop-valuedness α = prop-valuedness (underlying-order α) (is-well-ordered α)

Transitivity : (α : Ordinal 𝓤) → is-transitive (underlying-order α)
Transitivity α = transitivity (underlying-order α) (is-well-ordered α)

Well-foundedness : (α : Ordinal 𝓤) (x : ⟨ α ⟩) → is-accessible (underlying-order α) x
Well-foundedness α = well-foundedness (underlying-order α) (is-well-ordered α)

Extensionality : (α : Ordinal 𝓤) → is-extensional (underlying-order α)
Extensionality α = extensionality (underlying-order α) (is-well-ordered α)

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for compact
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordinalᵀ : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinalᵀ 𝓤 = Σ \(α : Ordinal 𝓤) → has-top (underlying-order α)

[_] : Ordinalᵀ 𝓤 → Ordinal 𝓤
[ α , t ] = α

⟪_⟫ : Ordinalᵀ 𝓤 → 𝓤 ̇
⟪ (X , _<_ , o) , t ⟫ = X

\end{code}

Topped ordinals are ranged over by τ,υ.

\begin{code}

tunderlying-order : (τ : Ordinalᵀ 𝓤) → ⟪ τ ⟫ → ⟪ τ ⟫ → 𝓤 ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : (τ : Ordinalᵀ 𝓤) → ⟪ τ ⟫ → ⟪ τ ⟫ → 𝓤 ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : (τ : Ordinalᵀ 𝓤) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued {𝓤} τ x y l m = dfunext (fe 𝓤 𝓤₀) (λ x → 𝟘-elim (m x))

topped : (τ : Ordinalᵀ 𝓤) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordinalᵀ 𝓤) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : (τ : Ordinalᵀ 𝓤) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordinalᵀ 𝓤) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

\end{code}
