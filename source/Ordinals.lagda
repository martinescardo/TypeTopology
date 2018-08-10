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

Ordinal : ∀ U → U ′ ̇
Ordinal U = Σ \(X : U ̇) → Σ \(_<_ : X → X → U ̇) → is-well-order _<_

\end{code}

The underlying type of an ordinal (which happens to to be necessarily
a set):

\begin{code}

⟨_⟩ : ∀ {U} → Ordinal U → U ̇
⟨ X , _<_ , o ⟩ = X

underlying-order : ∀ {U} → (α : Ordinal U) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

underlying-porder : ∀ {U} → (α : Ordinal U) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-porder (X , _<_ , o) = _≼_ _<_

syntax underlying-order  α x y = x ≺⟨ α ⟩ y
syntax underlying-porder α x y = x ≼⟨ α ⟩ y

is-well-ordered : ∀ {U} → (α : Ordinal U) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : ∀ {U} (τ : Ordinal U) → is-prop-valued (underlying-order τ)
Prop-valuedness τ = prop-valuedness (underlying-order τ) (is-well-ordered τ)

Transitivity : ∀ {U} (τ : Ordinal U) → is-transitive (underlying-order τ)
Transitivity τ = transitivity (underlying-order τ) (is-well-ordered τ)

Well-foundedness : ∀ {U} (τ : Ordinal U) (x : ⟨ τ ⟩) → is-accessible (underlying-order τ) x
Well-foundedness τ = well-foundedness (underlying-order τ) (is-well-ordered τ)

Extensionality : ∀ {U} (τ : Ordinal U) → is-extensional (underlying-order τ)
Extensionality τ = extensionality (underlying-order τ) (is-well-ordered τ)

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for searchable
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordinalᵀ : ∀ U → U ′ ̇
Ordinalᵀ U = Σ \(α : Ordinal U) → has-top (underlying-order α)

[_] : ∀ {U} → Ordinalᵀ U → Ordinal U
[ α , t ] = α

⟪_⟫ : ∀ {U} → Ordinalᵀ U → U ̇
⟪ (X , _<_ , o) , t ⟫ = X

tunderlying-order : ∀ {U} → (τ : Ordinalᵀ U) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : ∀ {U} → (τ : Ordinalᵀ U) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : ∀ {U} → (τ : Ordinalᵀ U) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued {U} τ x y l m = dfunext (fe U U₀) (λ x → 𝟘-elim (m x))

topped : ∀ {U} → (τ : Ordinalᵀ U) → has-top (tunderlying-order τ)
topped (α , t) = t

top : ∀ {U} → (τ : Ordinalᵀ U) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : ∀ {U} → (τ : Ordinalᵀ U) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : ∀ {U} → (τ : Ordinalᵀ U) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

\end{code}
