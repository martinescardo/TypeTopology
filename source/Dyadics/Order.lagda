\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Exponents
open import Dyadics.Rationals
open import Integers.Integers
open import Integers.Multiplication
open import Integers.Order
open import Notation.Order

module Dyadics.Order where

_<ℤ[1/2]_ _≤ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
((x , m) , _) <ℤ[1/2] ((y , n) , _) = x * pos (2^ n) < y * pos (2^ m)
((x , m) , _) ≤ℤ[1/2] ((y , n) , _) = x * pos (2^ n) ≤ y * pos (2^ m)

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _≤ℤ[1/2]_

 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _<ℤ[1/2]_

\end{code}

Transivity of order proof:

Since (x , a) ≤  (y , b) ≤ (z , c), we have that

1) x * pos (2^ b) < y * pos (2^ a)
2) y * pos (2^ c) < z * pos (2^ b)

Multiplication of 1) by pos (2^ c)
                  2) by pos (2^ a)

gives that x * pos (2^ b) * pos (2^ c)
            ≤ y * pos (2^ a) * pos (2^ c)
             ≤ z * pos (2^ b) * pos (2^ a).

It follows by transitivity of integer order and multiplicative
cancellation that x * pos (2^ c) ≤ z * pos (2^ a).

ℤ[1/2]≤-trans : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
ℤ[1/2]≤-trans ((x , a) , _) ((y , b) , _) ((z , c) , _) l₁ l₂ = {!!}
 where
  I : {!!}
  I = {!!}

-- x * pos (2^ n) ≤ y * (2^ m)

\end{code}
