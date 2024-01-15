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
zero-left-base = induction refl step
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
mult-left-id = induction base step
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
  γ = succ x * succ y        ＝⟨ refl ⟩
      succ x + succ x * y    ＝⟨ i    ⟩
      succ x + y * succ x    ＝⟨ refl ⟩
      succ x + (y + y * x)   ＝⟨ ii   ⟩
      succ (x + (y + y * x)) ＝⟨ iii  ⟩
      succ (x + y + y * x)   ＝⟨ iv   ⟩
      succ (y + x + y * x)   ＝⟨ v    ⟩
      succ (y + x + x * y)   ＝⟨ vi   ⟩
      succ (y + (x + x * y)) ＝⟨ vii  ⟩
      succ y + (x + x * y)   ＝⟨ refl ⟩
      succ y + x * succ y    ＝⟨ viii ⟩
      succ y + succ y * x    ＝⟨ refl ⟩
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
distributivity-mult-over-addition x y = induction refl step
 where
  step : (k : ℕ)
       → x * (y + k)      ＝ x * y + x * k
       → x * (y + succ k) ＝ x * y + x * succ k

  step k IH = x * (y + succ k)        ＝⟨ refl ⟩
              x + x * (y + k)         ＝⟨ i    ⟩
              x + (x * y + x * k)     ＝⟨ ii   ⟩
              x + (x * k + x * y)     ＝⟨ iii  ⟩
              x + x * k + x * y       ＝⟨ iv   ⟩
              x * y + (x + x * k)     ＝⟨ refl ⟩
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
pos-mult-is-succ x = induction base step
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
