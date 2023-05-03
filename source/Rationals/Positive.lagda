Andrew Sneap

This file defines positive rationals, which are useful for metric spaces.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Rationals.Type
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Order

module Rationals.Positive where

ℚ₊ : 𝓤₀ ̇
ℚ₊ = Σ q ꞉ ℚ , 0ℚ < q

_<ℚ₊_ : (p q : ℚ₊) → 𝓤₀ ̇
(p , _) <ℚ₊ (q , _) = p < q

_≤ℚ₊_ : (p q : ℚ₊) → 𝓤₀ ̇
(p , _) ≤ℚ₊ (q , _) = p ≤ q

instance
 Strict-Order-ℚ₊-ℚ₊ : Strict-Order ℚ₊ ℚ₊
 _<_ {{Strict-Order-ℚ₊-ℚ₊}} = _<ℚ₊_

instance
 Order-ℚ₊-ℚ₊ : Order ℚ₊ ℚ₊
 _≤_ {{Order-ℚ₊-ℚ₊}} = _≤ℚ₊_

_+_ : ℚ₊ → ℚ₊ → ℚ₊
(p , ε₁) + (q , ε₂) = p ℚ+ q , ℚ<-adding-zero p q ε₁ ε₂

\end{code}
