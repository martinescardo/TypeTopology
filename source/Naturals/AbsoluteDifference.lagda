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

open import Naturals.Addition
 using (_+_;
        zero-left-neutral;
        succ-left;
        addition-commutativity;
        sum-to-zero-gives-zero;
        addition-left-cancellable;
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

Added by Lane Biocini, 07 September 2023

Here we define some order lemmas for the Absolute Difference operation
and then prove the analog of the triangle inequality for the Natural
Numbers under it.

Slight refactoring on 12 October 2023

\begin{code}

open import Naturals.Order
open import Notation.Order

≤-diff : (x y : ℕ) → ∣ x - y ∣ ≤ x + y
≤-diff x        0        = ≤-refl x
≤-diff 0        (succ y) = ≤-+' 0    y
≤-diff (succ x) (succ y) = γ
 where
  Γ : (x + y) ≤ (succ x + y)
  Γ = ≤-trans (x + y) (succ (x + y)) (succ x + y)
       (≤-succ (x + y))
       (equal-gives-less-than-or-equal (succ (x + y)) (succ x + y)
         (succ-left x y ⁻¹))

  γ : ∣ x - y ∣ ≤ succ (succ x + y)
  γ = ≤-trans₂ ∣ x - y ∣ (x + y) (succ x + y) (succ (succ x + y))
       (≤-diff x y) Γ (≤-succ (succ x + y))

≤-diff-minus : (x y : ℕ) → x ≤ y + ∣ y - x ∣
≤-diff-minus 0    y = ⋆
≤-diff-minus (succ x) 0    = ≤-+' 0    x
≤-diff-minus (succ x) (succ y) = γ
 where
  Γ : x ≤ (y + ∣ y - x ∣)
  Γ = ≤-diff-minus x y

  γ : succ x ≤ (succ y + ∣ y - x ∣)
  γ = ≤-trans (succ x) (succ (y + ∣ y - x ∣)) (succ y + ∣ y - x ∣)
       (succ-monotone x (y + ∣ y - x ∣) Γ)
       (equal-gives-less-than-or-equal
        (succ (y + ∣ y - x ∣)) (succ y + ∣ y - x ∣)
        (succ-left y ∣ y - x ∣ ⁻¹))

≤-diff-plus : (x y : ℕ) → x ≤ (∣ x - y ∣ + y)
≤-diff-plus 0        y        = ⋆
≤-diff-plus (succ x) 0        = ≤-refl x
≤-diff-plus (succ x) (succ y) = ≤-diff-plus x y

triangle-inequality : (x y z : ℕ) → ∣ x - z ∣ ≤ ∣ x - y ∣ + ∣ y - z ∣
triangle-inequality 0    y z =
 ≤-trans₂ ∣ 0 - z ∣ z (y + ∣ y - z ∣) (∣ 0 - y ∣ + ∣ y - z ∣) Γ α γ
  where
   Γ : ∣ 0 - z ∣ ≤ z
   Γ = equal-gives-less-than-or-equal ∣ 0 - z ∣ z (minus-nothing z)

   α : z ≤ (y + ∣ y - z ∣)
   α = ≤-diff-minus z y

   β : y ≤ ∣ 0 - y ∣
   β = equal-gives-less-than-or-equal y ∣ 0 - y ∣ (minus-nothing y ⁻¹)

   γ : (y + ∣ y - z ∣) ≤ (∣ 0 - y ∣ + ∣ y - z ∣)
   γ = ≤-adding y ∣ 0 - y ∣ ∣ y - z ∣ ∣ y - z ∣ β (≤-refl ∣ y - z ∣)
triangle-inequality (succ x) 0    0        = ≤-refl x
triangle-inequality (succ x) 0    (succ z) =
 ≤-trans₂ ∣ x - z ∣ (x + z) (succ (x + z)) (succ (succ x + z))
      (≤-diff x z)
      (≤-succ (x + z))
      (≤-trans (x + z) (succ (x + z)) (succ x + z) (≤-succ (x + z)) α )
  where
   α : succ (x + z) ≤ (succ x + z)
   α = equal-gives-less-than-or-equal (succ (x + z)) (succ x + z)
        (succ-left x z ⁻¹)
triangle-inequality (succ x) (succ y) 0        = ≤-diff-plus x y
triangle-inequality (succ x) (succ y) (succ z) = triangle-inequality x y z

\end{code}

Added by Lane Biocini, 18 September 2023

Another lemma for Absolute Difference

\begin{code}
triangle-inequality-bound : (a b : ℕ) → ¬ (succ (a + b) ≤ ∣ a - b ∣)
triangle-inequality-bound a b l = not-less-than-itself (a + b) γ
 where
  Γ : ∣ a - b ∣ ≤ a + b
  Γ = ≤-diff a b

  γ : succ (a + b) ≤ (a + b)
  γ = ≤-trans (succ (a + b)) ∣ a - b ∣ (a + b) l Γ

triangle-inequality-bound' : (a b : ℕ) → ¬ (succ (succ a + b) ≤ ∣ a - b ∣)
triangle-inequality-bound' a b l = triangle-inequality-bound a b γ
 where
  Γ : succ (a + b) ≤ succ a + b
  Γ = equal-gives-less-than-or-equal (succ (a + b)) (succ a + b)
   (succ-left a b ⁻¹)

  γ : succ (a + b) ≤ ∣ a - b ∣
  γ = ≤-trans₂ (succ (a + b)) (succ a + b) (succ (succ a + b)) ∣ a - b ∣
       Γ (≤-succ (succ a + b) ) l
\end{code}
