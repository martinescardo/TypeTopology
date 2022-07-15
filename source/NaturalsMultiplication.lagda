Andrew Sneap - 12/05/2021

This file defines multiplication of natural numbers, and proves many
standard properties of multiplication.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) 

open import NaturalsAddition
open import NaturalNumbers-Properties
-- open import NaturalsOrder 
-- open import OrderNotation 
open import UF-Base

module NaturalsMultiplication where

\end{code}

Multiplication is defined in the same way as addition, and is left associative.

\begin{code}

_*_ : (x y : ℕ) → ℕ
x * 0      = 0
x * succ y = x + x * y

infixl 32 _*_

\end{code}

Zero is the base for multiplication. On the right, this is true by
definition. On the left, this is proved inductively.

Base case: 0 * 0 ≡ 0

Inductive case: Assume 0 * k ≡ 0.

Then 0 * succ k ≡ 0 + 0 * k (by definition)
                ≡ 0 + 0 (using the inductive hypothesis)
                ≡ 0 (by definition).

\begin{code}

zero-right-base : (x : ℕ) → x * 0 ≡ 0 
zero-right-base x = refl

zero-left-base : (x : ℕ) → 0 * x ≡ 0
zero-left-base = induction refl step
 where
  step : (x : ℕ)
       → 0 * x     ≡ 0
       → 0 + 0 * x ≡ 0
  step x IH = 0 + 0 * x  ≡⟨ ap (0 +_) IH ⟩
              0 + 0      ≡⟨ refl         ⟩
              0          ∎

\end{code}

One is the identity element for multiplication. On the right, this is
true by definition. Left multiplication by 1 is proved inductively,
very similarly to the above proof.

\begin{code}

mult-right-id : (x : ℕ) → x * 1 ≡ x
mult-right-id x = refl

mult-left-id : (x : ℕ) → 1 * x ≡ x
mult-left-id = induction base step
 where
  base : 1 * 0 ≡ 0
  base = refl

  step : (x : ℕ)
       → 1 * x     ≡ x
       → 1 + 1 * x ≡ succ x
         
  step x IH = 1 + 1 * x  ≡⟨ ap (1 +_) IH        ⟩
              1 + x      ≡⟨ addition-commutativity 1 x ⟩
              x + 1      ≡⟨ refl                       ⟩
              succ x     ∎

\end{code}

Commutativity is slightly more complicated, since it requires three
uses of the inductive hypothesis with different arguments.

First, induct on y, then on x. In the first two cases, use the rules
that zero is the multiplicative base on left and right.

In the inductive case, we can use three inductive hypothesis:
1) x * y ≡ y * x
2) x * succ y ≡ succ y * x
3) succ x * y ≡ y * succ x

With these hypothesis, and commutativity and associativity of
addition, equational reasoning proves commutativity of multiplication.

\begin{code}

mult-commutativity : (x y : ℕ) → x * y ≡ y * x
mult-commutativity x        0        = zero-left-base x ⁻¹
mult-commutativity 0        (succ y) = 0 * succ y    ≡⟨ zero-left-base (succ y)  ⟩
                                       0             ≡⟨ zero-right-base (succ y) ⟩
                                       succ y * 0    ∎
mult-commutativity (succ x) (succ y) = succ x * succ y        ≡⟨ refl ⟩
                                       succ x + succ x * y    ≡⟨ ap (succ x +_) (mult-commutativity (succ x) y) ⟩
                                       succ x + y * succ x    ≡⟨ refl ⟩
                                       succ x + (y + y * x)   ≡⟨ succ-left x (y + y * x) ⟩
                                       succ (x + (y + y * x)) ≡⟨ ap succ (addition-associativity x y (y * x) ⁻¹) ⟩
                                       succ (x + y + y * x)   ≡⟨ ap (λ - → succ (- + y * x)) (addition-commutativity x y) ⟩
                                       succ (y + x + y * x)   ≡⟨ ap (λ - → succ (y + x + -)) (mult-commutativity y x) ⟩
                                       succ (y + x + x * y)   ≡⟨ ap succ (addition-associativity y x (x * y)) ⟩
                                       succ (y + (x + x * y)) ≡⟨ succ-left y (x + x * y) ⁻¹ ⟩
                                       succ y + (x + x * y)   ≡⟨ refl ⟩
                                       succ y + x * succ y    ≡⟨ ap (succ y +_) (mult-commutativity (succ y) x ⁻¹) ⟩
                                       succ y + succ y * x    ≡⟨ refl ⟩
                                       succ y * succ x        ∎

\end{code}

Distributivity of multiplication over addition is proved using induction on z.
This induction is chosen to simplify the proof, since
x * (y + z) ≡ x * y + x * 0 by definition.

The inductive case uses commutativity and associativity of addition, the
proof is clear by observing the chain of equations.

\begin{code}

distributivity-mult-over-addition : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z 
distributivity-mult-over-addition x y = induction refl step
 where
  step : (k : ℕ)
       → x * (y + k)      ≡ x * y + x * k
       → x * (y + succ k) ≡ x * y + x * succ k

  step k IH = x * (y + succ k)        ≡⟨ refl                                                ⟩
              x + x * (y + k)         ≡⟨ ap (x +_ ) IH                                       ⟩
              x + (x * y + x * k)     ≡⟨ ap (x +_ ) (addition-commutativity (x * y) (x * k)) ⟩ 
              x + (x * k + x * y)     ≡⟨ addition-associativity x (x * k) (x * y) ⁻¹         ⟩
              x + x * k + x * y       ≡⟨ addition-commutativity (x + x * k) (x * y)          ⟩
              x * y + (x + x * k)     ≡⟨ refl                                                ⟩  
              x * y + (x * (succ k))  ∎

\end{code}

Distributivity of multiplication from the right follows as a simple
consequence of commutativity.

\begin{code}

distributivity-mult-over-addition' : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
distributivity-mult-over-addition' x y z
 = (x + y) * z   ≡⟨ mult-commutativity (x + y) z ⟩
   z * (x + y)   ≡⟨ distributivity-mult-over-addition z x y ⟩
   z * x + z * y ≡⟨ ap (z * x +_) (mult-commutativity z y)  ⟩
   z * x + y * z ≡⟨ ap (_+ y * z) (mult-commutativity z x)  ⟩
   x * z + y * z ∎

\end{code}

Associativity is proved as a consequence of distributivity, although
there are certainly different ways to prove it.

\begin{code}

mult-associativity : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
mult-associativity x y 0        = refl
mult-associativity x y (succ z) = x * y * succ z       ≡⟨ refl                                             ⟩
                                   x * y + x * y * z   ≡⟨ ap (x * y +_) (mult-associativity x y z)         ⟩
                                   x * y + x * (y * z) ≡⟨ distributivity-mult-over-addition x y (y * z) ⁻¹ ⟩
                                   x * (y + y * z)     ≡⟨ refl                                             ⟩
                                   x * (y * succ z)    ∎

pos-mult-is-succ : (x y : ℕ) → Σ z ꞉ ℕ , succ z ≡ succ x * succ y
pos-mult-is-succ x = induction base step
 where
  base : Σ z ꞉ ℕ , succ z ≡ succ x * 1
  base = x , refl

  step : (k : ℕ)
       → Σ z  ꞉ ℕ , succ z  ≡ succ x * succ k
       → Σ z' ꞉ ℕ , succ z' ≡ succ x * succ (succ k)
  step k (z , IH) = x + succ z , I
   where
    I : succ (x + succ z) ≡ succ x * succ (succ k)
    I = succ (x + succ z)               ≡⟨ succ-left x (succ z) ⁻¹ ⟩
        succ x + succ z                 ≡⟨ ap (succ x +_) IH       ⟩
        succ x + (succ x + succ x * k)  ≡⟨ refl                    ⟩
        succ x * succ (succ k) ∎

\end{code}

Multiplication by natural numbers greater than 1 can be proved by case
analysis.  Induct first on z, and prove the easy case that
1 * x ≡ 1 * y → x ≡ y.

Then induct on both x and y. When both are 0, they are equal. If one
is 0, and the other positive, then we have a proof that positive
number is 0, and hence a contradiction.

In the final case, we use the inductive hypothesis, and
addition-left-cancellable to be able to conclude that multiplication
is left cancellable. Multiplication is consequently right cancellable
by commutativity of multiplication.

\begin{code}

mult-left-cancellable : (x y z : ℕ) → succ z * x ≡ succ z * y → x ≡ y
mult-left-cancellable x        y        0        e = mult-commutativity x 1 ∙ e ∙ mult-commutativity 1 y
mult-left-cancellable 0        0        (succ z) e = refl
mult-left-cancellable 0        (succ y) (succ z) e = 𝟘-elim (positive-not-zero (succ z + succ (succ z) * y) (succ-left (succ z) (succ (succ z) * y) ⁻¹ ∙ e ⁻¹))
mult-left-cancellable (succ x) 0        (succ z) e = 𝟘-elim (positive-not-zero (succ z + succ (succ z) * x) (succ-left (succ z) (succ (succ z) * x) ⁻¹ ∙ e))
mult-left-cancellable (succ x) (succ y) (succ z) e = ap succ (IH I)
 where
  IH : succ (succ z) * x ≡ succ (succ z) * y → x ≡ y
  IH = mult-left-cancellable x y (succ z)
  I : succ (succ z) * x ≡ succ (succ z) * y
  I = addition-left-cancellable (succ (succ z) * x) (succ (succ z) * y) (succ (succ z)) e

mult-right-cancellable : (x y z : ℕ) → (x * succ z) ≡ (y * succ z) → x ≡ y
mult-right-cancellable x y z e = mult-left-cancellable x y z (mult-commutativity (succ z) x ∙ e ∙ mult-commutativity y (succ z))

\end{code}

Now we have two lemmas which will be useful later. The first is that multiplication of positive numbers is not 0.

The idea is that succ x * succ y ≡ succ x + succ x * y
                                 ≡ succ (x + succ x * y)
And hence, is not 0.

succ-pred-multiplication will be come useful when working with
rationals. Due to the way they are defined, there is a need to remove
succ-pred in many proofs.

\begin{code}

ℕ-positive-multiplication-not-zero : (x y : ℕ) → ¬ (succ x * succ y ≡ 0)
ℕ-positive-multiplication-not-zero x 0        e = positive-not-zero x e
ℕ-positive-multiplication-not-zero x (succ y) e = positive-not-zero (x + succ x * succ y) (succ-left x (succ x * succ y) ⁻¹ ∙ e)

succ-pred-multiplication : (x y : ℕ) → succ x * succ y ≡ succ (pred (succ x * succ y))
succ-pred-multiplication x y = succ-pred' (succ x * succ y) (ℕ-positive-multiplication-not-zero x y) ⁻¹

\end{code}
