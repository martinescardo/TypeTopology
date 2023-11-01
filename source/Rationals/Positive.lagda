Andrew Sneap

This file defines positive rationals, which are useful for metric spaces.

\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.Order
open import UF.Base

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

 Order-ℚ₊-ℚ₊ : Order ℚ₊ ℚ₊
 _≤_ {{Order-ℚ₊-ℚ₊}} = _≤ℚ₊_

 Strict-Order-ℚ₊-ℚ : Strict-Order ℚ₊ ℚ
 _<_ {{Strict-Order-ℚ₊-ℚ}} (p , _) q = p < q

 Strict-Order-ℚ-ℚ₊ : Strict-Order ℚ ℚ₊
 _<_ {{Strict-Order-ℚ-ℚ₊}} p (q , _) = p < q

_+_ : ℚ₊ → ℚ₊ → ℚ₊
(p , 0<p) + (q , 0<q) = p ℚ+ q , ℚ<-adding-zero p q 0<p 0<q

1ℚ₊ : ℚ₊
1ℚ₊ = 1ℚ , 0<1

_*_ : ℚ₊ → ℚ₊ → ℚ₊
(p , 0<p) * (q , 0<q)
 = p ℚ* q , ℚ<-pos-multiplication-preserves-order p q 0<p 0<q

1/2*_ : ℚ₊ → ℚ₊
1/2* p = (1/2 , 0<1/2) * p

1/4*_ : ℚ₊ → ℚ₊
1/4* p = (1/4 , 0<1/4) * p

\end{code}
