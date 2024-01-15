Andrew Sneap, 17 February 2022

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Exponentiation
open import Dyadics.Type
open import Integers.Type
open import Integers.Exponentiation
open import Integers.Multiplication
open import Integers.Order
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Notation.Order
open import UF.Base

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

\begin{code}

ℤ[1/2]<-trans : (x y z : ℤ[1/2]) → x < y → y < z → x < z
ℤ[1/2]<-trans ((x , a) , _) ((y , b) , _) ((z , c) , _) l₁ l₂ = γ
 where
  I : x * pos (2^ b) * pos (2^ c) < y * pos (2^ a) * pos (2^ c)
  I = positive-multiplication-preserves-order
      (x * pos (2^ b))
       (y * pos (2^ a))
        (pos (2^ c))
         (exponents-of-two-positive c) l₁

  II : y * pos (2^ c) * pos (2^ a) < z * pos (2^ b) * pos (2^ a)
  II = positive-multiplication-preserves-order
       (y * pos (2^ c))
        (z * pos (2^ b))
         (pos (2^ a))
          (exponents-of-two-positive a) l₂

  III : x * pos (2^ b) * pos (2^ c) ＝ x * pos (2^ c) * pos (2^ b)
  III = ℤ-mult-rearrangement x (pos (2^ b)) (pos (2^ c))

  IV : z * pos (2^ b) * pos (2^ a) ＝ z * pos (2^ a) * pos (2^ b)
  IV = ℤ-mult-rearrangement z (pos (2^ b)) (pos (2^ a))

  V : y * pos (2^ a) * pos (2^ c) ＝ y * pos (2^ c) * pos (2^ a)
  V = ℤ-mult-rearrangement y (pos (2^ a)) (pos (2^ c))

  VI : y * pos (2^ a) * pos (2^ c) < z * pos (2^ a) * pos (2^ b)
  VI = transport₂ _<_ (V ⁻¹) IV II

  VII : x * pos (2^ c) * pos (2^ b) < y * pos (2^ a) * pos (2^ c)
  VII = transport (_<  y * pos (2^ a) * pos (2^ c)) III I

  VIII : x * pos (2^ c) * pos (2^ b) < z * pos (2^ a) * pos (2^ b)
  VIII = ℤ<-trans
          (x * pos (2^ c) * pos (2^ b))
           (y * pos (2^ a) * pos (2^ c))
            (z * pos (2^ a) * pos (2^ b))
             VII VI

  γ : x * pos (2^ c) < z * pos (2^ a)
  γ = ordering-right-cancellable
       (x * pos (2^ c))
        (z * pos (2^ a))
         (pos (2^ b))
          (exponents-of-two-positive b)
           VIII

ℤ[1/2]≤-trans : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
ℤ[1/2]≤-trans ((x , a) , _) ((y , b) , _) ((z , c) , _) l₁ l₂ = γ
 where
  I : x * pos (2^ b) * pos (2^ c) ≤ y * pos (2^ a) * pos (2^ c)
  I = positive-multiplication-preserves-order'
      (x * pos (2^ b))
       (y * pos (2^ a))
        (pos (2^ c))
         (exponents-of-two-positive c) l₁

  II : y * pos (2^ c) * pos (2^ a) ≤ z * pos (2^ b) * pos (2^ a)
  II = positive-multiplication-preserves-order'
       (y * pos (2^ c))
        (z * pos (2^ b))
         (pos (2^ a))
          (exponents-of-two-positive a) l₂

  III : x * pos (2^ b) * pos (2^ c) ＝ x * pos (2^ c) * pos (2^ b)
  III = ℤ-mult-rearrangement x (pos (2^ b)) (pos (2^ c))

  IV : z * pos (2^ b) * pos (2^ a) ＝ z * pos (2^ a) * pos (2^ b)
  IV = ℤ-mult-rearrangement z (pos (2^ b)) (pos (2^ a))

  V : y * pos (2^ a) * pos (2^ c) ＝ y * pos (2^ c) * pos (2^ a)
  V = ℤ-mult-rearrangement y (pos (2^ a)) (pos (2^ c))

  VI : y * pos (2^ a) * pos (2^ c) ≤ z * pos (2^ a) * pos (2^ b)
  VI = transport₂ _≤_ (V ⁻¹) IV II

  VII : x * pos (2^ c) * pos (2^ b) ≤ y * pos (2^ a) * pos (2^ c)
  VII = transport (_≤  y * pos (2^ a) * pos (2^ c)) III I

  VIII : x * pos (2^ c) * pos (2^ b) ≤ z * pos (2^ a) * pos (2^ b)
  VIII = ℤ≤-trans
          (x * pos (2^ c) * pos (2^ b))
           (y * pos (2^ a) * pos (2^ c))
            (z * pos (2^ a) * pos (2^ b))
             VII VI

  γ : x * pos (2^ c) ≤ z * pos (2^ a)
  γ = ℤ≤-ordering-right-cancellable
      (x * pos (2^ c))
       (z * pos (2^ a))
        (pos (2^ b))
         (exponents-of-two-positive b) VIII

ℤ[1/2]≤-refl : (p : ℤ[1/2]) → p ≤ p
ℤ[1/2]≤-refl ((z , a) , α)  = ℤ≤-refl (z * pos (2^ a))

\end{code}
