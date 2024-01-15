Lane Biocini, 07 September 2023

This module defines the Absolute Difference operation, where we take two
numbers and return the absolute value of the remainder left over after
subtracting one from the other. It also defines some useful lemmas that
will come in handy when we tackle the triangle inequality in the Integers,
and also to prove the Natural Number analog for the triangle inequality.

Expanded and refactored on 12 October 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.AbsoluteDifference where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.Plus-Properties using (+functor)

open import Naturals.Addition using (_+_; zero-left-neutral; succ-left;
 addition-commutativity; sum-to-zero-gives-zero; addition-left-cancellable;
 addition-associativity)
open import Naturals.Multiplication using (_*_)
open import Naturals.Properties using (zero-not-positive)

open import UF.Base using (transport₂)

∣_-_∣ : ℕ → ℕ → ℕ
∣ x - zero ∣ = x
∣ zero - succ y ∣ = succ y
∣ succ x - succ y ∣ = ∣ x - y ∣

minus-nothing : (x : ℕ) → ∣ 0 - x ∣ ＝ x
minus-nothing zero = refl
minus-nothing (succ x) = refl

difference-is-zero : (x : ℕ) → ∣ x - x ∣ ＝ 0
difference-is-zero zero = refl
difference-is-zero (succ x) = difference-is-zero x

diff-succ-left : (x : ℕ) → ∣ succ x - x ∣ ＝ 1
diff-succ-left zero = refl
diff-succ-left (succ x) = diff-succ-left x

diff-succ-right : (x : ℕ) → ∣ x - succ x ∣ ＝ 1
diff-succ-right zero = refl
diff-succ-right (succ x) = diff-succ-right x

diff-commutative : (x y : ℕ) → ∣ x - y ∣ ＝ ∣ y - x ∣
diff-commutative zero y = minus-nothing y
diff-commutative (succ x) zero = refl
diff-commutative (succ x) (succ y) = diff-commutative x y

equal-if-difference-is-zero : (x y : ℕ)
                         → ∣ x - y ∣ ＝ 0
                         → x ＝ y
equal-if-difference-is-zero x zero p = p
equal-if-difference-is-zero (succ x) (succ y) p =
 ap succ (equal-if-difference-is-zero x y p)

subtract-cancellable-left : (x y : ℕ) → ∣ x + y - y ∣ ＝ x
subtract-cancellable-left x zero = refl
subtract-cancellable-left x (succ y) = subtract-cancellable-left x y

subtract-cancellable-right : (x y : ℕ) → ∣ x - x + y ∣ ＝ y
subtract-cancellable-right zero y = ap ∣ 0 -_∣ (zero-left-neutral y) ∙ minus-nothing y
subtract-cancellable-right (succ x) y = ap (λ u → ∣ succ x - u ∣) (succ-left x y)
                                      ∙ subtract-cancellable-right x y

diff-addition-cancel : (a x y : ℕ) → ∣ a + x - a + y ∣ ＝ ∣ x - y ∣
diff-addition-cancel zero x y =
 transport₂ (λ u v → ∣ u - v ∣ ＝ ∣ x - y ∣)
  (zero-left-neutral x ⁻¹) (zero-left-neutral y ⁻¹) refl
diff-addition-cancel (succ a) x y =
 transport₂ (λ u v →  ∣ u - v ∣ ＝ ∣ x - y ∣)
   (succ-left a x ⁻¹) (succ-left a y ⁻¹) (diff-addition-cancel a x y)

diff-equals-remainder : (a x y : ℕ) → x + y ＝ a → ∣ a - x ∣ ＝ y
diff-equals-remainder a x y p = γ ∙ subtract-cancellable-left y x
  where
    γ : ∣ a - x ∣ ＝ ∣ y + x - x ∣
    γ = ap ∣_- x ∣ (addition-commutativity y x ∙ p) ⁻¹

diff-mult-distributivity : (a x y : ℕ) → ∣ a * x - a * y ∣ ＝ a * ∣ x - y ∣
diff-mult-distributivity a x zero = refl
diff-mult-distributivity a zero (succ y) = minus-nothing (a + a * y)
diff-mult-distributivity a (succ x) (succ y) = diff-addition-cancel a (a * x) (a * y)
                                             ∙ diff-mult-distributivity a x y

diff-equals-constant : (a x y : ℕ) → ∣ x - y ∣ ＝ a → (x ＝ a + y) ∔ (y ＝ a + x)
diff-equals-constant a x zero p = inl p
diff-equals-constant a zero (succ y) p = inr p
diff-equals-constant a (succ x) (succ y) p =
 +functor (ap succ) (ap succ) (diff-equals-constant a x y p)

diff-equals-sum : (x y : ℕ) → ∣ x - y ∣ ＝ x + y → (x ＝ 0) ∔ (y ＝ 0)
diff-equals-sum x y p = cases I II (diff-equals-constant (x + y) x y p)
 where
  I : x ＝ x + y + y → (x ＝ 0) ∔ (y ＝ 0)
  I l = inr (sum-to-zero-gives-zero y y
   (addition-left-cancellable zero (y + y) x
    (l ∙ addition-associativity x y y) ⁻¹))

  II : y ＝ x + y + x → (x ＝ 0) ∔ (y ＝ 0)
  II l = inl (sum-to-zero-gives-zero x x
   (addition-left-cancellable zero (x + x) y
   (l ∙ (ap (_+ x) (addition-commutativity x y)
    ∙ addition-associativity y x x)) ⁻¹))

subtract-even : (x y : ℕ) → ∣ x - y ∣ ＝ x → (y ＝ 0) ∔ (y ＝ x + x)
subtract-even x y p =
 +functor (_⁻¹ ∘ addition-left-cancellable zero y x) id
       (diff-equals-constant x x y p)

subtract-odd : (x y : ℕ) → ∣ x - y ∣ ＝ succ x → y ＝ succ (x + x)
subtract-odd x y p =
 cases (𝟘-elim ∘ ϕ) (λ u → u ∙ succ-left x x)
  (diff-equals-constant (succ x) x y p)
   where
    ϕ : ¬ (x ＝ succ x + y)
    ϕ e = zero-not-positive y
     (addition-left-cancellable zero (succ y) x (e ∙ succ-left x y))

-- This is equivalent to the lemma: (x y ꞉ ℕ) → x ≤ y ∔ y ≤ x
diff-cancellable : (x y : ℕ) → (y ＝ ∣ y - x ∣ + x) ∔ (x ＝ ∣ x - y ∣ + y)
diff-cancellable zero y = inl refl
diff-cancellable (succ x) zero = inr refl
diff-cancellable (succ x) (succ y) = +functor
 (ap succ) (ap succ) (diff-cancellable x y)

\end{code}
