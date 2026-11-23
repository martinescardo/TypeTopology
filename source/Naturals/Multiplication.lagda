Andrew Sneap - October-November 2020
Updated May 2022

This file defines multiplication of natural numbers, and proves many
standard properties of multiplication.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition
open import Naturals.Properties
open import UF.Base

module Naturals.Multiplication where

\end{code}

Multiplication is defined in the same way as addition, and is left associative.

\begin{code}

_*_ : (x y : ℕ) → ℕ
x * 0      = 0
x * succ y = x + x * y

infixl 32 _*_

{-# BUILTIN NATTIMES _*_ #-}

_*ᴸ_ : (x y : ℕ) → ℕ
x *ᴸ y = y * x

\end{code}

Zero is the base for multiplication. On the right, this is true by
definition. On the left, this is proved inductively.

Base case: 0 * 0 ≡ 0

Inductive case: Assume 0 * k ≡ 0.

Then 0 * succ k ≡ 0 + 0 * k (by definition)
                ≡ 0 + 0 (using the inductive hypothesis)
                ≡ 0 (by definition).

\begin{code}

zero-right-base : (x : ℕ) → x * 0 ＝ 0
zero-right-base x = refl

zero-left-base : (x : ℕ) → 0 * x ＝ 0
zero-left-base = ℕ-induction refl step
 where
  step : (x : ℕ)
       → 0 * x     ＝ 0
       → 0 + 0 * x ＝ 0
  step x IH = 0 + 0 * x  ＝⟨ ap (0 +_) IH ⟩
              0 + 0      ＝⟨ refl         ⟩
              0          ∎

\end{code}

One is the identity element for multiplication. On the right, this is
true by definition. Left multiplication by 1 is proved inductively,
very similarly to the above proof.

\begin{code}

mult-right-id : (x : ℕ) → x * 1 ＝ x
mult-right-id x = refl

mult-left-id : (x : ℕ) → 1 * x ＝ x
mult-left-id = ℕ-induction base step
 where
  base : 1 * 0 ＝ 0
  base = refl

  step : (x : ℕ)
       → 1 * x     ＝ x
       → 1 + 1 * x ＝ succ x

  step x IH = 1 + 1 * x  ＝⟨ ap (1 +_) IH        ⟩
              1 + x      ＝⟨ addition-commutativity 1 x ⟩
              x + 1      ＝⟨ refl                       ⟩
              succ x     ∎

\end{code}

Commutativity is slightly more complicated, since it requires three
uses of the inductive hypothesis with different arguments.

First, induct on y, then on x. In the first two cases, use the rules
that zero is the multiplicative base on left and right.

In the inductive case, we can use three inductive hypothesis:
1) x * y ＝ y * x
2) x * succ y ＝ succ y * x
3) succ x * y ＝ y * succ x

With these hypothesis, and commutativity and associativity of
addition, equational reasoning proves commutativity of multiplication.

\begin{code}

mult-commutativity : (x y : ℕ) → x * y ＝ y * x
mult-commutativity x        0        = zero-left-base x ⁻¹
mult-commutativity 0        (succ y) = γ
 where
  γ : 0 * succ y ＝ succ y * 0
  γ = 0 * succ y    ＝⟨ zero-left-base (succ y)  ⟩
      0             ＝⟨ zero-right-base (succ y) ⟩
      succ y * 0    ∎
mult-commutativity (succ x) (succ y) = γ
 where
  γ : succ x * succ y ＝ succ y * succ x
  γ = succ x * succ y        ＝⟨refl⟩
      succ x + succ x * y    ＝⟨ i    ⟩
      succ x + y * succ x    ＝⟨refl⟩
      succ x + (y + y * x)   ＝⟨ ii   ⟩
      succ (x + (y + y * x)) ＝⟨ iii  ⟩
      succ (x + y + y * x)   ＝⟨ iv   ⟩
      succ (y + x + y * x)   ＝⟨ v    ⟩
      succ (y + x + x * y)   ＝⟨ vi   ⟩
      succ (y + (x + x * y)) ＝⟨ vii  ⟩
      succ y + (x + x * y)   ＝⟨refl⟩
      succ y + x * succ y    ＝⟨ viii ⟩
      succ y + succ y * x    ＝⟨refl⟩
      succ y * succ x        ∎
   where
    i    = ap (succ x +_) (mult-commutativity (succ x) y)
    ii   = succ-left x (y + y * x)
    iii  = ap succ (addition-associativity x y (y * x) ⁻¹)
    iv   = ap (λ - → succ (- + y * x)) (addition-commutativity x y)
    v    = ap (λ - → succ (y + x + -)) (mult-commutativity y x)
    vi   = ap succ (addition-associativity y x (x * y))
    vii  = succ-left y (x + x * y) ⁻¹
    viii = ap (succ y +_) (mult-commutativity (succ y) x ⁻¹)

\end{code}

Distributivity of multiplication over addition is proved using induction on z.
This induction is chosen to simplify the proof, since
x * (y + z) ＝ x * y + x * 0 by definition.

The inductive case uses commutativity and associativity of addition, the
proof is clear by observing the chain of equations.

\begin{code}

distributivity-mult-over-addition : (x y z : ℕ) → x * (y + z) ＝ x * y + x * z
distributivity-mult-over-addition x y = ℕ-induction refl step
 where
  step : (k : ℕ)
       → x * (y + k)      ＝ x * y + x * k
       → x * (y + succ k) ＝ x * y + x * succ k

  step k IH = x * (y + succ k)        ＝⟨refl⟩
              x + x * (y + k)         ＝⟨ i    ⟩
              x + (x * y + x * k)     ＝⟨ ii   ⟩
              x + (x * k + x * y)     ＝⟨ iii  ⟩
              x + x * k + x * y       ＝⟨ iv   ⟩
              x * y + (x + x * k)     ＝⟨refl⟩
              x * y + (x * (succ k))  ∎
   where
    i   = ap (x +_ ) IH
    ii  = ap (x +_ ) (addition-commutativity (x * y) (x * k))
    iii = addition-associativity x (x * k) (x * y) ⁻¹
    iv  = addition-commutativity (x + x * k) (x * y)

\end{code}

Distributivity of multiplication from the right follows as a simple
consequence of commutativity.

\begin{code}

distributivity-mult-over-addition' : (x y z : ℕ) → (x + y) * z ＝ x * z + y * z
distributivity-mult-over-addition' x y z
 = (x + y) * z   ＝⟨ mult-commutativity (x + y) z ⟩
   z * (x + y)   ＝⟨ distributivity-mult-over-addition z x y ⟩
   z * x + z * y ＝⟨ ap (z * x +_) (mult-commutativity z y)  ⟩
   z * x + y * z ＝⟨ ap (_+ y * z) (mult-commutativity z x)  ⟩
   x * z + y * z ∎

\end{code}

Associativity is proved as a consequence of distributivity, although
there are certainly different ways to prove it.

\begin{code}

mult-associativity : (x y z : ℕ) → (x * y) * z ＝ x * (y * z)
mult-associativity x y 0        = refl
mult-associativity x y (succ z)
 = x * y * succ z      ＝⟨ refl                                             ⟩
   x * y + x * y * z   ＝⟨ ap (x * y +_) (mult-associativity x y z)         ⟩
   x * y + x * (y * z) ＝⟨ distributivity-mult-over-addition x y (y * z) ⁻¹ ⟩
   x * (y + y * z)     ＝⟨ refl                                             ⟩
   x * (y * succ z)    ∎

pos-mult-is-succ : (x y : ℕ) → Σ z ꞉ ℕ , succ z ＝ succ x * succ y
pos-mult-is-succ x = ℕ-induction base step
 where
  base : Σ z ꞉ ℕ , succ z ＝ succ x * 1
  base = x , refl

  step : (k : ℕ)
       → Σ z  ꞉ ℕ , succ z  ＝ succ x * succ k
       → Σ z' ꞉ ℕ , succ z' ＝ succ x * succ (succ k)
  step k (z , IH) = x + succ z , I
   where
    I : succ (x + succ z) ＝ succ x * succ (succ k)
    I = succ (x + succ z)               ＝⟨ succ-left x (succ z) ⁻¹ ⟩
        succ x + succ z                 ＝⟨ ap (succ x +_) IH       ⟩
        succ x + (succ x + succ x * k)  ＝⟨ refl                    ⟩
        succ x * succ (succ k) ∎

\end{code}

Multiplication by natural numbers greater than 1 can be proved by case
analysis.  Induct first on z, and prove the easy case that
1 * x ＝ 1 * y → x ＝ y.

Then induct on both x and y. When both are 0, they are equal. If one
is 0, and the other positive, then we have a proof that positive
number is 0, and hence a contradiction.

In the final case, we use the inductive hypothesis, and
addition-left-cancellable to be able to conclude that multiplication
is left cancellable. Multiplication is consequently right cancellable
by commutativity of multiplication.

\begin{code}

mult-left-cancellable-lemma : (x y : ℕ)
                            → ¬ (succ (succ x) * 0 ＝ succ (succ x) * (succ y))
mult-left-cancellable-lemma x y e = γ
 where
  I : succ (succ x + succ (succ x) * y) ＝ succ (succ x) + succ (succ x) * y
  I = succ-left (succ x) (succ (succ x) * y) ⁻¹

  II : succ (succ x + succ (succ x) * y) ＝ 0
  II = succ (succ x + succ (succ x) * y) ＝⟨ I    ⟩
       succ (succ x) + succ (succ x) * y ＝⟨ e ⁻¹ ⟩
       succ (succ x) * 0                 ∎

  γ : 𝟘
  γ = positive-not-zero (succ x + succ (succ x) * y) II

mult-left-cancellable : (x y z : ℕ) → succ z * x ＝ succ z * y → x ＝ y
mult-left-cancellable x y 0 e = γ
 where
  γ : x ＝ y
  γ = x     ＝⟨ mult-left-id x ⁻¹ ⟩
      1 * x ＝⟨ e                 ⟩
      1 * y ＝⟨ mult-left-id y    ⟩
      y     ∎
mult-left-cancellable 0 0 (succ z) e = refl
mult-left-cancellable 0 (succ y) (succ z) e
 = 𝟘-elim (mult-left-cancellable-lemma z y e)
mult-left-cancellable (succ x) 0 (succ z) e
 = 𝟘-elim (mult-left-cancellable-lemma z x (e ⁻¹))
mult-left-cancellable (succ x) (succ y) (succ z) e = ap succ (IH I)
 where
  IH : succ (succ z) * x ＝ succ (succ z) * y → x ＝ y
  IH = mult-left-cancellable x y (succ z)
  I : succ (succ z) * x ＝ succ (succ z) * y
  I = addition-left-cancellable _ _ _ e

mult-right-cancellable : (x y z : ℕ) → (x * succ z) ＝ (y * succ z) → x ＝ y
mult-right-cancellable x y z e = mult-left-cancellable x y z γ
 where
  γ : succ z * x ＝ succ z * y
  γ = succ z * x ＝⟨ mult-commutativity (succ z) x ⟩
      x * succ z ＝⟨ e                             ⟩
      y * succ z ＝⟨ mult-commutativity y (succ z) ⟩
      succ z * y ∎

\end{code}

Now we have two lemmas which will be useful later. The first is that
multiplication of positive numbers is not 0.

The idea is that succ x * succ y ＝ succ x + succ x * y
                                 ＝ succ (x + succ x * y)
And hence, is not 0.

succ-pred-multiplication will be come useful when working with
rationals. Due to the way they are defined, there is a need to remove
succ-pred in many proofs.

\begin{code}

ℕ-positive-multiplication-not-zero : (x y : ℕ) → ¬ (succ x * succ y ＝ 0)
ℕ-positive-multiplication-not-zero x 0        e = positive-not-zero x e
ℕ-positive-multiplication-not-zero x (succ y) e = γ
 where
  I : succ (x + succ x * succ y) ＝ 0
  I = succ (x + succ x * succ y) ＝⟨ succ-left x (succ x * succ y) ⁻¹ ⟩
      succ x + succ x * succ y   ＝⟨ e                                ⟩
      0                          ∎

  γ : 𝟘
  γ = positive-not-zero (x + succ x * succ y) I

succ-pred-multiplication : (x y : ℕ)
                         → succ x * succ y ＝ succ (pred (succ x * succ y))
succ-pred-multiplication x y = succ-pred' (succ x * succ y) γ ⁻¹
 where
  γ : ¬ (succ x * succ y ＝ 0)
  γ = ℕ-positive-multiplication-not-zero x y

\end{code}

Added 2022 by Andrew Sneap.

Multiplication preserves non-strict order, and this is proved by induction.

In the base case, it is required to prove that 0 ≤ 0 which is true by
definition.  In the inductive case, we need to prove that
m * succ k ≤ n * succ k, or by definitional equality m + m * k ≤ n + n * k.

By the inductive hypothesis, m * k ≤ n * k, and we have that m ≤ n, so we
can use the result which says we can combine two order relations into one.

\begin{code}

open import Naturals.Order
open import Notation.Order

multiplication-preserves-order : (m n k : ℕ) → m ≤ n → m * k ≤ n * k
multiplication-preserves-order m n 0        l = zero-least 0
multiplication-preserves-order m n (succ k) l = γ
 where
  IH : m * k ≤ n * k
  IH = multiplication-preserves-order m n k l

  γ : m * (succ k) ≤ n * (succ k)
  γ = ≤-adding m n (m * k) (n * k) l IH

\end{code}

Added by Theo Hepburn on 21 November 2026.

Multiplication preserves non-strict order when the multiplying constant
is on the left.

We show that m * k is equal to k * m, and that n * k is equal to
k * n. Since we have that m * k ≤ n * k given that m ≤ n as above, we can use
`mult-commutativity` to rearrange both sides to get k * m ≤ k * n.

\begin{code}

multiplication-preserves-order-left : (k m n : ℕ) → m ≤ n → k * m ≤ k * n
multiplication-preserves-order-left k m n l = transport₂ _≤_ γ₁ γ₂ γ₃
 where
  γ₁ : m * k ＝ k * m
  γ₁ = mult-commutativity m k

  γ₂ : n * k ＝ k * n
  γ₂ = mult-commutativity n k

  γ₃ : m * k ≤ n * k
  γ₃ = multiplication-preserves-order m n k l

\end{code}

Multiplication preserves non-strict order when, rather than multiplying by a
constant, both numbers being multiplied are different.

We have that m * x ≤ n * x by `multiplication-preserves-order`, and that
n * x ≤ n * y by `multiplication-preserves-order-left`. Therefore, by
transitivity, we have m * x ≤ n * y.

\begin{code}

≤-multiplying : (m n x y : ℕ) → m ≤ n → x ≤ y → m * x ≤ n * y
≤-multiplying m n x y l₁ l₂ = ≤-trans (m * x) (n * x) (n * y) γ₁ γ₂
 where
  γ₁ : m * x ≤ n * x
  γ₁ = multiplication-preserves-order m n x l₁ 

  γ₂ : n * x ≤ n * y
  γ₂ = multiplication-preserves-order-left n x y l₂

\end{code}

Proof that if x ≤ y, a * x + b * y ≤ (a + b) * y

If we have two variables and one is lower than the other, it allows us to
impose an upper bound on the expression without the lower variable.

We show that the right hand side can be written as follows:

(a + b) * y ＝ a * y + b * y by `distributivity-mult-over-addition'`

Since a * x ≤ a * y, by `multiplication-preserves-order-left`, we also have
a * x + b * y ≤ a * y + b * y

\begin{code}

absorb-≤-variable : (a b x y : ℕ) → x ≤ y → a * x + b * y ≤ (a + b) * y
absorb-≤-variable a b x y x≤y = transport (a * x + b * y ≤_) γ₁ γ₃
 where
  γ₁ : a * y + b * y ＝ (a + b) * y
  γ₁ = distributivity-mult-over-addition' a b y ⁻¹

  γ₂ : a * x ≤ a * y
  γ₂ = multiplication-preserves-order-left a x y x≤y

  γ₃ : a * x + b * y ≤ a * y + b * y
  γ₃ = ≤-n-monotone-right (a * x) (a * y) (b * y) γ₂

\end{code}

Proof that when n ≠ 0, we have b + a * n ≤ (b + a) * n

A special case of the above that allows us to impose an upper bound without a
constant on an expression with a constant.

First, we eliminate the invalid case n ＝ 0.

We then have n ≥ 1. We use `absorb-≤-variable` to show that
b + a * n ＝ b * 1 + a * n ≤ (b + a) * n

\begin{code}

absorb-constant : (a b n : ℕ) → n ≠ 0 → b + a * n ≤ (b + a) * n
absorb-constant a b zero   n≠0 = 𝟘-elim (n≠0 refl)
absorb-constant a b (succ n) l = absorb-≤-variable b a 1 (succ n) ⋆

\end{code}

End of addition

For strict order, order is only preserved when multiplying by a value
greater than 0.  Again by induction, the base case is trivial since we
are multiplying by 1.  The inductive case is similar to the above
proof.

\begin{code}

multiplication-preserves-strict-order : (m n k : ℕ)
                                      → m < n
                                      → m * succ k < n * succ k
multiplication-preserves-strict-order m n 0        l = l
multiplication-preserves-strict-order m n (succ k) l = γ
 where
  IH : m * succ k < n * succ k
  IH = multiplication-preserves-strict-order m n k l

  γ : m * succ (succ k) < n * succ (succ k)
  γ = <-adding m n (m * succ k) (n * succ k) l IH

\end{code}

A variation added by Fredrik Nordvall Forsberg on 11 October 2025.

\begin{code}

multiplication-preserves-strict-order' : (m n k : ℕ)
                                       → m < n
                                       → 0 < k
                                       → m * k < n * k
multiplication-preserves-strict-order' m n 0        l p = 𝟘-elim p
multiplication-preserves-strict-order' m n (succ k) l p =
 multiplication-preserves-strict-order m n k l

\end{code}

If x * (y + 1) ≤ z, then x ≤ z. This is a useful property to have, and
proof follows from x ≤ x * y + 1 and transitivity of order.

A similar proof for strict order is sometimes useful.

\begin{code}

product-order-cancellable : (x y z : ℕ) → x * (succ y) ≤ z → x ≤ z
product-order-cancellable x 0        z   = id
product-order-cancellable x (succ y) z l = γ
 where
  I : x ≤ x + x * succ y
  I = ≤-+ x (x * succ y)

  γ : x ≤ z
  γ = ≤-trans x (x * succ (succ y)) z I l

less-than-pos-mult : (x y z : ℕ) → x < y → x < y * succ z
less-than-pos-mult x y z l = <-+ x y (y * z) l

\end{code}