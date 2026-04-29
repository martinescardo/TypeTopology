\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import MLTT.Spartan hiding (_+_) renaming (_^_ to _^^_)
open import Naturals.Addition
open import Naturals.Properties
open import Naturals.Multiplication

module Naturals.Exponentiation where

_^_ : ℕ → ℕ → ℕ
a ^ b = ((a *_) ^^ b) 1

infixl 33 _^_

2^ : ℕ → ℕ
2^ = 2 ^_

zero-base : (a : ℕ) → a ^ 0 ＝ 1
zero-base a = refl

prod-of-powers : (n a b : ℕ) → (n ^ a) * (n ^ b) ＝ n ^ (a + b)
prod-of-powers n a 0        = refl
prod-of-powers n a (succ b) = I
 where
  I : (n ^ a) * (n ^ succ b) ＝ (n ^ (a + succ b))
  I = (n ^ a) * (n ^ succ b)  ＝⟨refl⟩
      (n ^ a) * (n * (n ^ b)) ＝⟨ i    ⟩
      (n ^ a) * n * (n ^ b)   ＝⟨ ii   ⟩
      n * n ^ a * n ^ b       ＝⟨ iii  ⟩
      n * (n ^ a * n ^ b)     ＝⟨ iv   ⟩
      n ^ (a + succ b)         ∎
   where
    i   = mult-associativity (n ^ a) n (n ^ b) ⁻¹
    ii  = ap (_* (n ^ b)) (mult-commutativity (n ^ a) n)
    iii = mult-associativity n (n ^ a) (n ^ b)
    iv  = ap (n *_) (prod-of-powers n a b)

power-of-power : (n a b : ℕ) → (n ^ a) ^ b ＝ n ^ (a * b)
power-of-power n a 0        = refl
power-of-power n a (succ b) = I
 where
  IH : n ^ a ^ b ＝ n ^ (a * b)
  IH = power-of-power n a b
  I : n ^ a ^ succ b ＝ n ^ (a * succ b)
  I = n ^ a ^ succ b       ＝⟨ refl                       ⟩
      n ^ a * (n ^ a) ^ b ＝⟨ ap (n ^ a *_) IH          ⟩
      n ^ a * n ^ (a * b)  ＝⟨ prod-of-powers n a (a * b) ⟩
      n ^ (a + a * b)       ＝⟨ refl                       ⟩
      n ^ (a * succ b)      ∎

exponents-not-zero : (n : ℕ) → ¬ (2^ n ＝ 0)
exponents-not-zero 0        e = positive-not-zero 0 e
exponents-not-zero (succ n) e = exponents-not-zero n I
 where
  I : 2^ n ＝ 0
  I = mult-left-cancellable (2^ n) 0 1 e

\end{code}

Added 11 October 2025 by Fredrik Nordvall Forsberg.

\begin{code}

open import Naturals.Order
open import Notation.Order

exponential-positive-if-base-positive : (n m : ℕ) → 0 < n → 0 < n ^ m
exponential-positive-if-base-positive n zero _ = ⋆
exponential-positive-if-base-positive n@(succ n') (succ m) l = II
 where
  IH : 0 < (n ^ m)
  IH = exponential-positive-if-base-positive n m l

  I : 0 < (n ^ m) * n
  I = less-than-pos-mult 0 (n ^ m) n' IH

  II : 0 < n * (n ^ m)
  II = transport (0 <_) (mult-commutativity (n ^ m) n) I

exponent-smaller-than-exponential-for-base-at-least-two : (n k : ℕ)
                                                        → 2 ≤ k
                                                        → n ≤ (k ^ n)
exponent-smaller-than-exponential-for-base-at-least-two zero k _ = ⋆
exponent-smaller-than-exponential-for-base-at-least-two
 (succ n) k@(succ (succ k')) l = ≤-<-trans n (1 * k ^ n) (k * (k ^ n)) I III
  where
   IH : n ≤ (k ^ n)
   IH = exponent-smaller-than-exponential-for-base-at-least-two n k l

   I : n ≤ 1 * k ^ n
   I = transport⁻¹ (n ≤_) (mult-left-id (k ^ n)) IH

   II : 0 < k ^ n
   II = exponential-positive-if-base-positive k n ⋆

   III : 1 * (k ^ n) < k * (k ^ n)
   III = multiplication-preserves-strict-order' 1 k (k ^ n) ⋆ II

\end{code}
