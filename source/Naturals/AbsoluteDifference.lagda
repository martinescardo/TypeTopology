Lane Biocini, 07 September 2023

This module defines the Absolute Difference operation, where we take two
numbers and return the absolute value of the remainder left over after
subtracting one from the other. It also defines some useful lemmas that
will come in handy when we tackle the triangle inequality in the Integers,
and also to prove the Natural Number analog for the triangle inequality.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Naturals.AbsoluteDifference where

open import MLTT.Spartan hiding (_+_)
open import Naturals.Addition renaming (_+_ to _+_)

∣_-_∣ : ℕ → ℕ → ℕ
∣ x - zero ∣ = x
∣ zero - succ y ∣ = succ y
∣ succ x - succ y ∣ = ∣ x - y ∣

minus-nothing : (x : ℕ) → ∣ 0 - x ∣ ＝ x
minus-nothing zero = refl
minus-nothing (succ x) = refl

exact-difference-is-zero : (x : ℕ) → ∣ x - x ∣ ＝ 0
exact-difference-is-zero zero = refl
exact-difference-is-zero (succ x) = exact-difference-is-zero x

diff-commutative : (x y : ℕ) → ∣ x - y ∣ ＝ ∣ y - x ∣
diff-commutative zero y = minus-nothing y
diff-commutative (succ x) zero = refl
diff-commutative (succ x) (succ y) = diff-commutative x y

diff-sum : (x y : ℕ) → ∣ x + y - y ∣ ＝ x
diff-sum zero zero = refl
diff-sum zero (succ y) = ap (λ u → ∣ u - y ∣) (zero-left-neutral y)
                       ∙ exact-difference-is-zero y
diff-sum (succ x) zero = refl
diff-sum (succ x) (succ y) = diff-sum (succ x) y

\end{code}
