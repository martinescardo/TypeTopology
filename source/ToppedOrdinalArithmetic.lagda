Martin Escardo, 29 June 2018

To get closure under sums constructively, we need to restrict to
particular kinds of ordinals. Having a top element is a simple
sufficient condition, which holds in the applications we have in mind
(for compact ordinals).  Classically, ordinals with a top element are
precisely the successor ordinals. Constructively, ℕ∞ is an example of
an ordinal with a top element, which "is not" a successor ordinal, as
its top element is not isolated.

TODO. Generalize this from 𝓤₀ to an arbitrary universe. The
(practical) problem is that the type of natural numbers is defined at
𝓤₀. We could (1) either using universe lifting, or (2) define the type
in any universe (like we did for the the types 𝟘 and 𝟙). But (1) is
cumbersome and (2) requires much work in other modules.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module ToppedOrdinalArithmetic
        (fe : FunExt)
       where

open import SpartanMLTT
open import OrdinalsType
open import OrdinalArithmetic fe
open import OrdinalsWellOrderArithmetic
open import ToppedOrdinalsType fe
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder hiding (_≤_) renaming (_<_ to _≺[ℕ]_)
open import InjectiveTypes fe
open import SquashedSum fe

open import UF-Subsingletons
open import UF-Embeddings

Ordᵀ = Ordinalᵀ 𝓤₀

succₒ : Ord → Ordᵀ
succₒ α = α +ₒ 𝟙ₒ  ,
          plus.top-preservation
           (underlying-order α)
           (underlying-order 𝟙ₒ)
           (prop.topped 𝟙 𝟙-is-prop *)

𝟙ᵒ 𝟚ᵒ ℕ∞ᵒ : Ordᵀ
𝟙ᵒ  = 𝟙ₒ , prop.topped 𝟙 𝟙-is-prop *
𝟚ᵒ  = succₒ 𝟙ₒ
ℕ∞ᵒ = (ℕ∞ₒ , ∞ , ∞-top)

\end{code}

Sum of an ordinal-indexed family of ordinals:

\begin{code}

∑ : (τ : Ordᵀ) → (⟪ τ ⟫ → Ordᵀ) → Ordᵀ
∑ ((X , _<_ , o) , t) υ = ((Σ x ꞉ X , ⟪ υ x ⟫) ,
                              Sum.order ,
                              Sum.well-order o (λ x → tis-well-ordered (υ x))) ,
                          Sum.top-preservation t
 where
  _≺_ : {x : X} → ⟪ υ x ⟫ → ⟪ υ x ⟫ → 𝓤₀ ̇
  y ≺ z = y ≺⟪ υ _ ⟫ z

  module Sum = sum-top fe _<_ _≺_ (λ x → top (υ x)) (λ x → top-is-top (υ x))

\end{code}

Addition and multiplication can be reduced to ∑, given the ordinal 𝟚ᵒ
defined above:

\begin{code}

_+ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ +ᵒ υ = ∑ 𝟚ᵒ (cases (λ _ → τ) (λ _ → υ))

_×ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ ×ᵒ υ = ∑ τ  (λ (_ : ⟪ τ ⟫) → υ)

\end{code}

Extension of a family X → Ordᵀ along an embedding j : X → A to get a
family A → Ordᵀ. (This can also be done for Ord-valued families.)
This uses the module 𝓤₀F-InjectiveTypes to calculate Y / j.

\begin{code}

_↗_ : {X A : 𝓤₀ ̇ } → (X → Ordᵀ) → (Σ j ꞉ (X → A), is-embedding j) → (A → Ordᵀ)
τ ↗ (j , e) = λ a → ((Y / j) a ,
                     Extension.order a ,
                     Extension.well-order a (λ x → tis-well-ordered (τ x))) ,
                     Extension.top-preservation a (λ x → topped (τ x))
 where
  Y : domain τ → 𝓤₀ ̇
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
