\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Multiplication
-- open import Integers.Negation renaming (-_ to ℤ-_)
-- open import Integers.Parity
open import Naturals.Exponents
open import UF.Base hiding (_≈_)
-- open import UF.Subsingletons

module Dyadics.Addition where

\end{code}

TODO: Comment on strategy.

\begin{code}

_+'_ : ℤ × ℕ → ℤ × ℕ → ℤ × ℕ
(p , a) +' (q , b) = p * pos (2^ b) ℤ+ q * pos (2^ a) , a ℕ+ b

_+_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
(p , _) + (q , _) = normalise-pos (p +' q)

ℤ[1/2]+'-comm : (p q : ℤ × ℕ) → p +' q ＝ q +' p
ℤ[1/2]+'-comm (p , a) (q , b) = ap₂ _,_ I II
 where
  I : p * pos (2^ b) ℤ+ q * pos (2^ a) ＝ q * pos (2^ a) ℤ+ p * pos (2^ b)
  I = ℤ+-comm (p * pos (2^ b)) (q * pos (2^ a))
  II : a ℕ+ b ＝ b ℕ+ a
  II = addition-commutativity a b

{-

ℤ[1/2]+-comm : (p q : ℤ[1/2]) → p + q ＝ q + p
ℤ[1/2]+-comm (p , _) (q , _) = ap normalise-pos (ℤ[1/2]+'-comm p q)

ℤ[1/2]+'-≈' : (p q r : ℤ × ℕ) → p ≈' q → (p +' r) ≈' (q +' r)
ℤ[1/2]+'-≈' (p , a) (q , b) (r , c) e = γ
 where
  e' : p * pos (2^ b) ＝ q * pos (2^ a)
  e' = e

  rearrangement₁ : {!!} 
  rearrangement₁ = {!!}

  rearrangement₂ : (a b c d : ℤ) → a * b ℤ+ c * d ＝ a * d ℤ+ c * b
  rearrangement₂ = {!!}
  
  γ : (p * pos (2^ c) ℤ+ r * pos (2^ a)) * pos (2^ (b ℕ+ c)) -- lhs of unfolded type
    ＝ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ (a ℕ+ c)) -- rhs of unfolded type
  γ = (p * pos (2^ c) ℤ+ r * pos (2^ a)) * pos (2^ (b ℕ+ c)) ＝⟨ {!!} ⟩
           
      (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ (a ℕ+ c)) ∎

ℤ[1/2]+-normalise-pos : (p q : ℤ × ℕ) → normalise-pos (p +' q) ＝ (normalise-pos p) + (normalise-pos q)
ℤ[1/2]+-normalise-pos (p , a) (q , b) = {!γ!}
 where
  I : {!!}
  I = {!ℤ[1/2]-to-normalise-pos !}
 
  γ : {!!}
  γ = {!!}

-}

\end{code}
