Martin Escardo, 29 June 2018

The type Ordinals of ordinals in a universe U, and the subtype Ordinalsᵀ of
ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import OrdinalNotions hiding (_≤_)
open import UF-Embedding

module Ordinals
       (fe : ∀ U V → funext U V)
       where

OrdinalStructure : U ̇ → U ⁺ ̇
OrdinalStructure {U} X = Σ \(_<_ : X → X → U ̇) → is-well-order _<_

Ordinal : ∀ U → U ⁺ ̇
Ordinal U = Σ \(X : U ̇) → OrdinalStructure X

\end{code}

An ordinal is a type equipped with ordinal structure. Such a type is
automatically a set.

NB. Perhaps we will eventually need to have two parameters U (the
universe where the underlying type X lives) and V (the universe where
_<_ takes values in) for Ordinal.

Ordinals are ranged over by α,β,γ.

The underlying type of an ordinal (which happens to to be necessarily
a set):

\begin{code}

⟨_⟩ : Ordinal U → U ̇
⟨ X , _<_ , o ⟩ = X

structure : (α : Ordinal U) → OrdinalStructure ⟨ α ⟩
structure (X , s) = s

underlying-order : (α : Ordinal U) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

underlying-porder : (α : Ordinal U) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-porder (X , _<_ , o) = _≼_ _<_

syntax underlying-order  α x y = x ≺⟨ α ⟩ y
syntax underlying-porder α x y = x ≼⟨ α ⟩ y

is-well-ordered : (α : Ordinal U) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : (α : Ordinal U) → is-prop-valued (underlying-order α)
Prop-valuedness α = prop-valuedness (underlying-order α) (is-well-ordered α)

Transitivity : (α : Ordinal U) → is-transitive (underlying-order α)
Transitivity α = transitivity (underlying-order α) (is-well-ordered α)

Well-foundedness : (α : Ordinal U) (x : ⟨ α ⟩) → is-accessible (underlying-order α) x
Well-foundedness α = well-foundedness (underlying-order α) (is-well-ordered α)

Extensionality : (α : Ordinal U) → is-extensional (underlying-order α)
Extensionality α = extensionality (underlying-order α) (is-well-ordered α)

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for compact
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordinalᵀ : ∀ U → U ⁺ ̇
Ordinalᵀ U = Σ \(α : Ordinal U) → has-top (underlying-order α)

[_] : Ordinalᵀ U → Ordinal U
[ α , t ] = α

⟪_⟫ : Ordinalᵀ U → U ̇
⟪ (X , _<_ , o) , t ⟫ = X

\end{code}

Topped ordinals are ranged over by τ,υ.

\begin{code}

tunderlying-order : (τ : Ordinalᵀ U) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : (τ : Ordinalᵀ U) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : (τ : Ordinalᵀ U) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued {U} τ x y l m = dfunext (fe U U₀) (λ x → 𝟘-elim (m x))

topped : (τ : Ordinalᵀ U) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordinalᵀ U) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : (τ : Ordinalᵀ U) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordinalᵀ U) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

\end{code}
