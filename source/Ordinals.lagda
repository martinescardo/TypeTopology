Martin Escardo, 29 June 2018

The type Ord of ordinals in a universe U, and the subtype Ordᵀ of
ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons
open import OrdinalNotions hiding (_≤_)

module Ordinals
        (U : Universe)
        (fe : funext U U₀)
       where

Ord : U ′ ̇
Ord = Σ \(X : U ̇) → Σ \(_<_ : X → X → U ̇) → is-well-order _<_

⟨_⟩ : Ord → U ̇
⟨ X , _<_ , o ⟩ = X

underlying-order : (α : Ord) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

syntax underlying-order α x y = x ≺⟨ α ⟩ y

is-well-ordered : (α : Ord) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for searchable
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordᵀ : U ′ ̇
Ordᵀ = Σ \(α : Ord) → has-top (underlying-order α)

[_] : Ordᵀ → Ord
[ α , t ] = α

⟪_⟫ : Ordᵀ → U ̇
⟪ (X , _<_ , o) , t ⟫ = X

tunderlying-order : (τ : Ordᵀ) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : (τ : Ordᵀ) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : (τ : Ordᵀ) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued τ x y l m = dfunext fe (λ x → 𝟘-elim (m x))

topped : (τ : Ordᵀ) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordᵀ) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : (τ : Ordᵀ) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordᵀ) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

\end{code}
