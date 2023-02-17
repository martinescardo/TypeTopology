Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Integers.Addition
open import Integers.Multiplication
open import Integers.Type
open import Naturals.Exponents

module Integers.Exponents where

\end{code}

 Integers exponentiation is defined in the same way as natural number
 exponentiation. Note that (pos 1) is used as the base element, and
 that we allow positive exponents, since exponentiation is not closed
 for negative exponents. 

\begin{code}

_pos^_ : ℤ → ℕ → ℤ
a pos^ b = ((a *_) ^ b) (pos 1)

ℤ-exp-zero-base : (a : ℤ) → a pos^ 0 ＝ pos 1
ℤ-exp-zero-base a = refl

ℤ-exp-addition : (n : ℤ) (a b : ℕ) → (n pos^ (a ℕ+ b)) ＝ (n pos^ a) * (n pos^ b)
ℤ-exp-addition n a 0        = refl
ℤ-exp-addition n a (succ b) = γ
 where
  γ : (n pos^ (a ℕ+ succ b)) ＝ (n pos^ a) * (n pos^ succ b)
  γ = (n pos^ (a ℕ+ succ b))        ＝⟨ ap (n *_) (ℤ-exp-addition n a b)          ⟩
      n * ((n pos^ a) * (n pos^ b)) ＝⟨ ℤ*-assoc n (n pos^ a) (n pos^ b) ⁻¹       ⟩
      n * (n pos^ a) * (n pos^ b)   ＝⟨ ap (_* (n pos^ b)) (ℤ*-comm n (n pos^ a)) ⟩
      (n pos^ a) * n * (n pos^ b)   ＝⟨ ℤ*-assoc (n pos^ a) n (n pos^ b)          ⟩
      (n pos^ a) * (n pos^ succ b)   ∎

exponents-not-zero' : (m : ℕ) → not-zero (pos (2^ m))
exponents-not-zero' m iz = exponents-not-zero m (pos-lc I)
 where
  I : pos (2^ m) ＝ pos 0
  I = from-is-zero (pos (2^ m)) iz

exponents-of-two-positive : (k : ℕ) → is-pos-succ (pos (2^ k))
exponents-of-two-positive 0        = ⋆
exponents-of-two-positive (succ k) = γ
 where
  I : is-pos-succ (pos (2^ k))
  I = exponents-of-two-positive k

  II : is-pos-succ (pos 2 * pos (2^ k))
  II = is-pos-succ-mult (pos 2) (pos (2^ k)) ⋆ I

  III : pos 2 * pos (2^ k) ＝ pos (2 ℕ* 2^ k)
  III = pos-multiplication-equiv-to-ℕ 2 (2^ k)

  γ : is-pos-succ (pos (2 ℕ* 2^ k))
  γ = transport is-pos-succ III II

\end{code}
