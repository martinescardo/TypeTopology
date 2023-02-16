\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
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

ℤ[1/2]+-comm : (p q : ℤ[1/2]) → p + q ＝ q + p
ℤ[1/2]+-comm (p , _) (q , _) = ap normalise-pos (ℤ[1/2]+'-comm p q)

ℤ[1/2]+'-≈' : (p q r : ℤ × ℕ) → p ≈' q → (p +' r) ≈' (q +' r)
ℤ[1/2]+'-≈' (p , a) (q , b) (r , c) e = γ
 where
  e' : p * pos (2^ b) ＝ q * pos (2^ a)
  e' = e

  rearrangement₁ : (a : ℤ) (b c d : ℕ) → a * pos (2^ b) * pos (2^ (c ℕ+ d)) ＝ a * pos (2^ c) * pos (2^ (b ℕ+ d))
  rearrangement₁ a b c d = a * pos (2^ b) * pos (2^ (c ℕ+ d))         ＝⟨ ap (λ - → a * pos (2^ b) * pos -) (prod-of-powers 2 c d ⁻¹) ⟩
                           a * pos (2^ b) * pos (2^ c ℕ* 2^ d)        ＝⟨ ap (a * pos (2^ b) *_) (pos-multiplication-equiv-to-ℕ (2^ c) (2^ d) ⁻¹) ⟩
                           a * pos (2^ b) * (pos (2^ c) * pos (2^ d)) ＝⟨ ℤ*-assoc (a * pos (2^ b)) (pos (2^ c)) (pos (2^ d)) ⁻¹ ⟩
                           a * pos (2^ b) * pos (2^ c) * pos (2^ d)   ＝⟨ ap (_* pos (2^ d)) (ℤ*-assoc a (pos (2^ b)) (pos (2^ c))) ⟩
                           a * (pos (2^ b) * pos (2^ c)) * pos (2^ d) ＝⟨ ap (λ - → a * - * pos (2^ d)) (ℤ*-comm (pos (2^ b)) (pos (2^ c))) ⟩
                           a * (pos (2^ c) * pos (2^ b)) * pos (2^ d) ＝⟨ ap (_* pos (2^ d)) (ℤ*-assoc a (pos (2^ c)) (pos (2^ b)) ⁻¹) ⟩
                           a * pos (2^ c) * pos (2^ b) * pos (2^ d)   ＝⟨ ℤ*-assoc (a * pos (2^ c)) (pos (2^ b)) (pos (2^ d)) ⟩
                           a * pos (2^ c) * (pos (2^ b) * pos (2^ d)) ＝⟨ ap (a * pos (2^ c) *_) (pos-multiplication-equiv-to-ℕ (2^ b) (2^ d)) ⟩
                           a * pos (2^ c) * pos (2^ b ℕ* 2^ d)        ＝⟨ ap (λ - → a * pos (2^ c) * pos - ) (prod-of-powers 2 b d) ⟩
                           a * pos (2^ c) * pos (2^ (b ℕ+ d)) ∎

  I : p * pos (2^ c) * pos (2^ (b ℕ+ c)) ＝ q * pos (2^ c) * pos (2^ (a ℕ+ c))
  I = p * pos (2^ c) * pos (2^ (b ℕ+ c))   ＝⟨ rearrangement₁ p c b c ⟩
      p * pos (2^ b) * pos (2^ (c ℕ+ c))   ＝⟨ ap (_* pos (2^ (c ℕ+ c))) e ⟩
      q * pos (2^ a) * pos (2^ (c ℕ+ c))   ＝⟨ rearrangement₁ q a c c ⟩
      q * pos (2^ c) * pos (2^ (a ℕ+ c))      ∎
  
  γ : (p * pos (2^ c) ℤ+ r * pos (2^ a)) * pos (2^ (b ℕ+ c)) -- lhs of unfolded type
    ＝ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ (a ℕ+ c)) -- rhs of unfolded type
  γ = (p * pos (2^ c) ℤ+ r * pos (2^ a)) * pos (2^ (b ℕ+ c))                   ＝⟨ distributivity-mult-over-ℤ (p * pos (2^ c)) (r * pos (2^ a)) (pos (2^ (b ℕ+ c))) ⟩
      p * pos (2^ c) * pos (2^ (b ℕ+ c)) ℤ+ r * pos (2^ a) * pos (2^ (b ℕ+ c)) ＝⟨ ap (p * pos (2^ c) * pos (2^ (b ℕ+ c)) ℤ+_) (rearrangement₁ r a b c) ⟩
      p * pos (2^ c) * pos (2^ (b ℕ+ c)) ℤ+ r * pos (2^ b) * pos (2^ (a ℕ+ c)) ＝⟨ ap (_ℤ+ r * pos (2^ b) * pos (2^ (a ℕ+ c))) I ⟩
      q * pos (2^ c) * pos (2^ (a ℕ+ c)) ℤ+ r * pos (2^ b) * pos (2^ (a ℕ+ c)) ＝⟨ distributivity-mult-over-ℤ (q * pos (2^ c)) (r * pos (2^ b)) (pos (2^ (a ℕ+ c))) ⁻¹ ⟩       
      (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ (a ℕ+ c))                   ∎

{-
ℤ[1/2]+-normalise-pos : (p q : ℤ × ℕ) → normalise-pos (p +' q) ＝ (normalise-pos p) + (normalise-pos q)
ℤ[1/2]+-normalise-pos (p , a) (q , b) = {!γ!}
 where
  I : {!!}
  I = {!ℤ[1/2]-to-normalise-pos !}
 
  γ : {!!}
  γ = {!!}
-}

\end{code}
