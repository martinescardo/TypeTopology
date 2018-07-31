Martin Escardo, 29 June 2018

Some operations and constructions on ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module Ordinals
        (fe : ∀ U V → funext U V)
       where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Subsingletons
open import OrdinalNotions hiding (_≤_)
open import WellOrderArithmetic
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder hiding (_≤_) renaming (_<_ to _≺[ℕ]_)
open import UF-Embedding
open import UF-InjectiveTypes fe
open import SquashedSum fe

U = U₀
V = U₁

Ord : V ̇
Ord = Σ \(X : U ̇) → Σ \(_<_ : X → X → U ̇) → is-well-order _<_

⟨_⟩ : Ord → U ̇
⟨ X , _<_ , o ⟩ = X

underlying-order : (α : Ord) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

syntax underlying-order α x y = x ≺⟨ α ⟩ y

is-well-ordered : (α : Ord) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

subsingleton-ordinal : (P : U ̇) → is-prop P → Ord
subsingleton-ordinal P isp = P , subsingleton.order P isp , subsingleton.well-order P isp

𝟘ₒ 𝟙ₒ ℕₒ ℕ∞ₒ : Ord
𝟘ₒ = subsingleton-ordinal 𝟘 𝟘-is-prop
𝟙ₒ = subsingleton-ordinal 𝟙 𝟙-is-prop
ℕₒ = (ℕ , _≺[ℕ]_ , ℕ-ordinal)
ℕ∞ₒ = (ℕ∞ , _≺[ℕ∞]_ , ℕ∞-ordinal fe₀)

_+ₒ_ : Ord → Ord → Ord
(X , _<_ , o) +ₒ (Y , _≺_ , p) = (X + Y) ,
                                 plus.order _<_ _≺_ ,
                                 plus.well-order _<_ _≺_ o p

_×ₒ_ : Ord → Ord → Ord
(X , _<_ , o) ×ₒ (Y , _≺_ , p) = (X × Y) ,
                                 times.order _<_ _≺_ ,
                                 times.well-order _<_ _≺_ fe o p

prop-indexed-product : {P : U ̇} → is-prop P → (P → Ord) → Ord
prop-indexed-product {P} isp α = Π X ,
                                 _≺_ ,
                                 pip.well-order fe₀ P isp X _<_ (λ p → is-well-ordered (α p))
 where
  X : P → U ̇
  X p = ⟨ α p ⟩
  _<_ : {p : P} → X p → X p → U ̇
  _<_ {p} x y = x ≺⟨ α p ⟩ y
  _≺_ : Π X → Π X → U ̇
  f ≺ g = Σ \(p : P) → f p < g p

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for searchable
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordᵀ : V ̇
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
≼-prop-valued τ x y l m = dfunext fe₀ (λ x → 𝟘-elim (m x))

topped : (τ : Ordᵀ) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordᵀ) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : (τ : Ordᵀ) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordᵀ) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

succₒ : Ord → Ordᵀ
succₒ α = α +ₒ 𝟙ₒ  ,
          plus.top-preservation
           (underlying-order α)
           (underlying-order 𝟙ₒ)
           (subsingleton.topped 𝟙 𝟙-is-prop *)

𝟙ᵒ 𝟚ᵒ ℕ∞ᵒ : Ordᵀ
𝟙ᵒ = 𝟙ₒ , subsingleton.topped 𝟙 𝟙-is-prop *
𝟚ᵒ = succₒ 𝟙ₒ
ℕ∞ᵒ = (ℕ∞ₒ , ∞ , ∞-top)

\end{code}

Sum of an ordinal indexed family of ordinals:

\begin{code}

∑ : (τ : Ordᵀ) → (⟪ τ ⟫ → Ordᵀ) → Ordᵀ
∑ ((X , _<_ , o) , t) υ = ((Σ \(x : X) → ⟪ υ x ⟫) ,
                           Sum.order ,
                           Sum.well-order o (λ x → tis-well-ordered (υ x))) ,
                          Sum.top-preservation t
 where
  _≺_ : {x : X} → ⟪ υ x ⟫ → ⟪ υ x ⟫ → U ̇
  y ≺ z = y ≺⟪ υ _ ⟫ z
  module Sum = sum-top fe _<_ _≺_ (λ x → top (υ x)) (λ x → top-is-top (υ x))

\end{code}

Addition and multiplication can be reduced to ∑, given the ordinal 𝟚ᵒ
defined above:

\begin{code}

_+ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ +ᵒ υ = ∑ 𝟚ᵒ (cases (λ _ → τ) (λ _ → υ))

_×ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ ×ᵒ υ = ∑ τ \(_ : ⟪ τ ⟫) → υ

\end{code}

Extension of a family X → Ordᵀ along an embedding j : X → A to get a
family A → Ordᵀ. (This can also be done for Ord-valued families.)
This uses the module UF-InjectiveTypes to calculate Y / j.

\begin{code}

_↗_ : {X A : U ̇} → (X → Ordᵀ) → (Σ \(j : X → A) → is-embedding j) → (A → Ordᵀ)
τ ↗ (j , e) = λ a → ((Y / j) a ,
                     Extension.order a ,
                     Extension.well-order a (λ x → tis-well-ordered (τ x))) ,
                    Extension.top-preservation a (λ x → topped (τ x))
 where
  Y : dom τ → U ̇
  Y x = ⟪ τ x ⟫
  module Extension = extension fe Y j e (λ {x} → tunderlying-order (τ x))

\end{code}

Sum of a countable family with an added non-isolated top element. We
first extend the family to ℕ∞ and then take the ordinal-indexed sum of
ordinals defined above.

\begin{code}

∑¹ : (ℕ → Ordᵀ) → Ordᵀ
∑¹ τ = ∑ ℕ∞ᵒ (τ ↗ (under , under-embedding fe₀))

\end{code}

And now with an isolated top element:

\begin{code}

∑₁ : (ℕ → Ordᵀ) → Ordᵀ
∑₁ τ = ∑ (succₒ ℕₒ) (τ ↗ (over , over-embedding))

\end{code}
