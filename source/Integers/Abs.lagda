Andrew Sneap, 26 November 2021

In this file I define absolute values of integers and some properties
of abs, along with positive and negative properties of integers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.AbsoluteDifference
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Integers.Addition
open import Integers.Multiplication
open import Integers.Negation
open import Integers.Type

module Integers.Abs where

\end{code}

The absolute value function which maps integers to natural numbers are
defined in same file as integers. It is also useful to have an
absolute value function which maps integers to integers. This function
is defined now, and for both versions of the functions it is trivial
to prove that the absolute value of x and (- x) are equal.

\begin{code}

absℤ : ℤ → ℤ
absℤ (pos x)     = pos x
absℤ (negsucc x) = pos (succ x)

abs-removes-neg-sign : (x : ℤ) → abs x ＝ abs (- x)
abs-removes-neg-sign (pos zero)     = refl
abs-removes-neg-sign (pos (succ x)) = refl
abs-removes-neg-sign (negsucc x)    = refl

absℤ-removes-neg-sign : (x : ℤ) → absℤ x ＝ absℤ (- x)
absℤ-removes-neg-sign (pos zero)     = refl
absℤ-removes-neg-sign (pos (succ x)) = refl
absℤ-removes-neg-sign (negsucc x)    = refl

pos-abs-is-equal : (x : ℕ) → absℤ (pos x) ＝ pos x
pos-abs-is-equal x = refl

\end{code}

A standard result with absolute values is that it distributes over
multiplication, for both versions of the function. Of course, the same
is not true of addition (instead, the main results involving absolute
values and addition is the triangle inequality).

The proof is by case analysis on each argument. The given proofs are
lengthy, and a more elegant solution should be found.

\begin{code}

abs-over-mult : (x y : ℤ) → abs (x * y) ＝ abs x ℕ* abs y
abs-over-mult (pos x) (pos y) = ap abs (pos-multiplication-equiv-to-ℕ x y)
abs-over-mult (pos 0) (negsucc b) = I
 where
  I : abs (pos 0 * negsucc b) ＝ abs (pos 0) ℕ* abs (negsucc b)
  I = abs (pos 0 * negsucc b)        ＝⟨ ap abs (ℤ-zero-left-base (negsucc b)) ⟩
      abs (pos 0)                    ＝⟨ zero-left-base (abs (negsucc b)) ⁻¹   ⟩
      abs (pos 0) ℕ* abs (negsucc b) ∎
abs-over-mult (pos (succ x)) (negsucc b) = I
 where
  I : abs (pos (succ x) * negsucc b) ＝ abs (pos (succ x)) ℕ* abs (negsucc b)
  I = abs (pos (succ x) * negsucc b)           ＝⟨ i    ⟩
      abs (- ((pos (succ x) * pos (succ b))))  ＝⟨ ii   ⟩
      abs (- pos (succ x ℕ* succ b))           ＝⟨ iii  ⟩
      abs (pos (succ x ℕ* succ b))             ＝⟨ refl ⟩
      succ x ℕ* succ b                         ＝⟨ refl ⟩
      abs (pos (succ x)) ℕ* abs (negsucc b)    ∎
   where
    iiₐₚ : pos (succ x) * pos (succ b) ＝ pos (succ x ℕ* succ b)
    iiₐₚ = pos-multiplication-equiv-to-ℕ (succ x) (succ b)
    i = ap abs (negation-dist-over-mult (pos (succ x)) (pos (succ b)))
    ii = ap (λ z → (abs (- z))) iiₐₚ
    iii = abs-removes-neg-sign ( pos (succ x ℕ* succ b)) ⁻¹
abs-over-mult (negsucc x) (pos b) = I
 where
  I : abs (negsucc x * pos b) ＝ abs (negsucc x) ℕ* abs (pos b)
  I = abs (negsucc x * pos b)        ＝⟨ i    ⟩
      abs (- pos (succ x) * pos b)   ＝⟨ ii   ⟩
      abs (- pos (succ x ℕ* b))      ＝⟨ iii  ⟩
      (succ x) ℕ* b                  ＝⟨ refl ⟩
      abs (negsucc x) ℕ* abs (pos b) ∎
   where
    i   = ap abs (negation-dist-over-mult' (pos (succ x)) (pos b))
    ii  = ap (λ z → abs (- z)) (pos-multiplication-equiv-to-ℕ (succ x) b)
    iii = abs-removes-neg-sign (pos (succ x ℕ* b)) ⁻¹
abs-over-mult (negsucc x) (negsucc b) = I
 where
  I : abs (negsucc x * negsucc b) ＝ abs (negsucc x) ℕ* abs (negsucc b)
  I = abs (negsucc x * negsucc b)             ＝⟨ i    ⟩
      abs (- negsucc x * pos (succ b) )       ＝⟨ ii   ⟩
      abs (- (- pos (succ x) * pos (succ b))) ＝⟨ iii  ⟩
      abs (pos (succ x) * pos (succ b))       ＝⟨ iv   ⟩
      (succ x) ℕ* (succ b)                    ＝⟨ refl ⟩
      abs (negsucc x) ℕ* abs (negsucc b)      ∎
   where
    iiₐₚ : (- pos (succ x)) * pos (succ b) ＝ - pos (succ x) * pos (succ b)
    iiₐₚ = negation-dist-over-mult' (pos (succ x)) (pos (succ b))

    i   = ap abs (negation-dist-over-mult (negsucc x) (pos (succ b)))
    ii  = ap (λ z → abs (- z)) iiₐₚ
    iii = ap abs (minus-minus-is-plus (pos (succ x) * pos (succ b)))
    iv  = ap abs (pos-multiplication-equiv-to-ℕ (succ x) (succ b))

abs-over-mult' : (x y : ℤ) → absℤ (x * y) ＝ absℤ x * absℤ y
abs-over-mult' (pos x) (pos y) = I
 where
  I : absℤ (pos x * pos y) ＝ absℤ (pos x) * absℤ (pos y)
  I = absℤ (pos x * pos y)        ＝⟨ i    ⟩
      absℤ (pos (x ℕ* y))         ＝⟨ refl ⟩
      pos (x ℕ* y)                ＝⟨ ii   ⟩
      pos x * pos y               ＝⟨ refl ⟩
      absℤ (pos x) * absℤ (pos y) ∎
   where
    i = ap absℤ (pos-multiplication-equiv-to-ℕ x y)
    ii = pos-multiplication-equiv-to-ℕ x y ⁻¹
abs-over-mult' (pos x) (negsucc y) = I
 where
  I : absℤ (pos x * negsucc y) ＝ absℤ (pos x) * absℤ (negsucc y)
  I = absℤ (pos x * negsucc y)        ＝⟨ i    ⟩
      absℤ (- pos x * pos (succ y))   ＝⟨ ii   ⟩
      absℤ (- pos (x ℕ* succ y))      ＝⟨ iii  ⟩
      absℤ (pos (x ℕ* succ y))        ＝⟨ refl ⟩
      pos (x ℕ* succ y)               ＝⟨ iv   ⟩
      pos x * pos (succ y)            ＝⟨ refl ⟩
      absℤ (pos x) * absℤ (negsucc y) ∎
   where
    i = ap absℤ (negation-dist-over-mult (pos x) (pos (succ y)))
    ii = ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ x (succ y))
    iii = absℤ-removes-neg-sign (pos (x ℕ* succ y)) ⁻¹
    iv = pos-multiplication-equiv-to-ℕ x (succ y) ⁻¹
abs-over-mult' (negsucc x) (pos y) = I
 where
  I : absℤ (negsucc x * pos y) ＝ absℤ (negsucc x) * absℤ (pos y)
  I = absℤ (negsucc x * pos y)      ＝⟨ i    ⟩
      absℤ (pos y * negsucc x)      ＝⟨ ii   ⟩
      absℤ (- pos y * pos (succ x)) ＝⟨ iii  ⟩
      absℤ (- pos (y ℕ* succ x))    ＝⟨ iv   ⟩
      absℤ (pos (y ℕ* succ x))      ＝⟨ refl ⟩
      pos (y ℕ* succ x)             ＝⟨ v    ⟩
      pos y * pos (succ x)          ＝⟨ vi   ⟩
      pos (succ x) * pos y          ＝⟨ refl ⟩
      absℤ (negsucc x) * absℤ (pos y) ∎
   where
    i   = ap absℤ (ℤ*-comm (negsucc x) (pos y))
    ii  = ap absℤ (negation-dist-over-mult (pos y) (pos (succ x)))
    iii = ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ y (succ x))
    iv  = absℤ-removes-neg-sign (pos (y ℕ* succ x)) ⁻¹
    v   = pos-multiplication-equiv-to-ℕ y (succ x) ⁻¹
    vi  = ℤ*-comm (pos y) (pos (succ x))
abs-over-mult' (negsucc x) (negsucc y) = I
 where
  I : absℤ (negsucc x * negsucc y) ＝ absℤ (negsucc x) * absℤ (negsucc y)
  I = absℤ (negsucc x * negsucc y)        ＝⟨ i    ⟩
      absℤ (pos (succ x) * pos (succ y))  ＝⟨ ii   ⟩
      absℤ (pos (succ x ℕ* succ y))       ＝⟨ refl ⟩
      pos (succ x ℕ* succ y)              ＝⟨ iii  ⟩
      pos (succ x) * pos (succ y)         ＝⟨ refl ⟩
      absℤ (negsucc x) * absℤ (negsucc y) ∎
   where
    i   = ap absℤ (minus-times-minus-is-positive (pos (succ x)) (pos (succ y)))
    ii  = ap absℤ (pos-multiplication-equiv-to-ℕ (succ x) (succ y))
    iii = pos-multiplication-equiv-to-ℕ (succ x) (succ y) ⁻¹

\end{code}

Lane Biocini, 07 September 2023

In this section I prove a convenience lemma about the Absolute Value
operation, then go on to prove a lemma regarding the equivalence of the
addition of a positive and negative Integer to the Absolute Difference
operation in the Naturals, which will help us when we prove the triangle
inequality in the Integers.

\begin{code}

pos-abs-is-absℤ : (x : ℤ) → pos (abs x) ＝ absℤ x
pos-abs-is-absℤ (pos x) = refl
pos-abs-is-absℤ (negsucc x) = refl

abs-pos-plus-negsucc : (x y : ℕ) → abs (pos x +negsucc y) ＝ ∣ x - succ y ∣
abs-pos-plus-negsucc zero y = ap abs (ℤ+-comm (pos 0) (negsucc y))
abs-pos-plus-negsucc (succ x) zero = refl
abs-pos-plus-negsucc (succ x) (succ y) =
 abs (predℤ (pos (succ x) +negsucc y)) ＝⟨ i ⟩
 abs (pos x +negsucc y) ＝⟨ abs-pos-plus-negsucc x y ⟩
 ∣ x - succ y ∣          ∎
  where
   i : abs (predℤ (pos (succ x) +negsucc y)) ＝ abs (pos x +negsucc y)
   i = ap abs (ℤ-left-pred (pos (succ x)) (negsucc y)) ⁻¹

\end{code}
