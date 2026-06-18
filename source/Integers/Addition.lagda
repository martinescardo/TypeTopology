Andrew Sneap, 26 November 2021
Updated 18 July 2022

This file defines addition of integers, and commonly used properties used in
proofs, for example commutativity and associativity.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Type
open import Integers.Negation
open import Naturals.Addition renaming (_+_ to _ℕ+_)

module Integers.Addition where

\end{code}

Addition is defined inductively, first on positive and then through
negatives using auxiliary functions. +pos and +negsucc.

\begin{code}

_+pos_ : ℤ → ℕ → ℤ
x +pos 0      = x
x +pos succ y = succℤ (x +pos y)

_+negsucc_ : ℤ → ℕ → ℤ
x +negsucc 0      = predℤ x
x +negsucc succ y = predℤ (x +negsucc y)

_+_ : ℤ → ℤ → ℤ
x + pos y     = x +pos y
x + negsucc y = x +negsucc y

_-_ : ℤ → ℤ → ℤ
a - b = a + (- b)

infixl 31 _-_
infixl 31 _+_

\end{code}

We now have the proof that pos distributes over addition of natural numbers.

Following this, we have the interactions of succℤ and predℤ with
integer addition, by first considering their interactions with the
auxiliary functions +pos and +negsucc. These will of course be useful
in inductive proofs.

\begin{code}

distributivity-pos-addition : (x y : ℕ) → pos x + pos y ＝ pos (x ℕ+ y)
distributivity-pos-addition x = ℕ-induction base step
 where
  base : (pos x + pos 0) ＝ pos (x ℕ+ 0)
  base = refl

  step : (k : ℕ)
       → pos x + pos k        ＝ pos (x ℕ+ k)
       → pos x + pos (succ k) ＝ pos (x ℕ+ succ k)
  step k IH = pos x + pos (succ k)  ＝⟨ ap succℤ IH ⟩
              succℤ (pos (x ℕ+ k))  ∎

ℤ-left-succ-pos : (x : ℤ) → (y : ℕ) → succℤ x +pos y ＝ succℤ (x +pos y)
ℤ-left-succ-pos x 0        = refl
ℤ-left-succ-pos x (succ y) = ap succℤ (ℤ-left-succ-pos x y)

ℤ-left-pred-pos : (x : ℤ) → (y : ℕ) → predℤ x +pos y ＝ predℤ (x +pos y)
ℤ-left-pred-pos x 0        = refl
ℤ-left-pred-pos x (succ y)
 = succℤ (predℤ x +pos y)    ＝⟨ ℤ-left-succ-pos (predℤ x) y ⁻¹ ⟩
   succℤ (predℤ x) +pos y    ＝⟨ ap (_+pos y) (succpredℤ x)     ⟩
   x +pos y                  ＝⟨ predsuccℤ (x +pos y) ⁻¹        ⟩
   predℤ (succℤ (x +pos y))  ∎

ℤ-left-pred-negsucc : (x : ℤ) → (y : ℕ)
                    → predℤ x +negsucc y ＝ predℤ (x +negsucc y)
ℤ-left-pred-negsucc x 0        = refl
ℤ-left-pred-negsucc x (succ y) = ap predℤ (ℤ-left-pred-negsucc x y)

ℤ-left-succ-negsucc : (x : ℤ) (y : ℕ)
                    → succℤ x +negsucc y ＝ succℤ (x +negsucc y)
ℤ-left-succ-negsucc x 0        = predsuccℤ x ∙ (succpredℤ x ⁻¹)
ℤ-left-succ-negsucc x (succ y)
 = succℤ x +negsucc succ y      ＝⟨ ℤ-left-pred-negsucc (succℤ x) y ⁻¹  ⟩
   predℤ (succℤ x) +negsucc y   ＝⟨ ap (_+ (negsucc y)) (predsuccℤ x)   ⟩
   x + negsucc y                ＝⟨ succpredℤ (x +negsucc y) ⁻¹         ⟩
   succℤ (x +negsucc succ y)    ∎

ℤ-right-succ : (x y : ℤ) → x + succℤ y ＝ succℤ (x + y)
ℤ-right-succ x (pos y)            = refl
ℤ-right-succ x (negsucc 0)        = succpredℤ x ⁻¹
ℤ-right-succ x (negsucc (succ y)) = succpredℤ (x +negsucc y) ⁻¹

ℤ-left-succ : (x y : ℤ) → succℤ x + y ＝ succℤ (x + y)
ℤ-left-succ x (pos y)     = ℤ-left-succ-pos x y
ℤ-left-succ x (negsucc y) = ℤ-left-succ-negsucc x y

ℤ-left-pred : (x y : ℤ) → predℤ x + y ＝ predℤ (x + y)
ℤ-left-pred x (pos y)     = ℤ-left-pred-pos x y
ℤ-left-pred x (negsucc y) = ℤ-left-pred-negsucc x y

ℤ-right-pred : (x y : ℤ) → x + predℤ y ＝ predℤ (x + y)
ℤ-right-pred x (pos 0)        = refl
ℤ-right-pred x (pos (succ y)) = predsuccℤ (x +pos y) ⁻¹
ℤ-right-pred x (negsucc y)    = refl

\end{code}

Zero is the left and right base for addition and addition of integers
is commutative, both proved by induction.

\begin{code}

ℤ-zero-right-neutral : (x : ℤ) → x + pos 0 ＝ x
ℤ-zero-right-neutral x = refl

ℤ-zero-left-neutral : (x : ℤ) → pos 0 + x ＝ x
ℤ-zero-left-neutral (pos 0)            = refl
ℤ-zero-left-neutral (pos (succ x))     = ap succℤ (ℤ-zero-left-neutral (pos x))
ℤ-zero-left-neutral (negsucc 0)        = refl
ℤ-zero-left-neutral (negsucc (succ x)) = ap predℤ (ℤ-zero-left-neutral (negsucc x))

ℤ+-comm : (x y : ℤ) → x + y ＝ y + x
ℤ+-comm x = ℤ-induction base step₁ step₂
 where
  base : x ＝ (pos 0 + x)
  base = ℤ-zero-left-neutral x ⁻¹

  step₁ : (k : ℤ)
        → x + k         ＝ k + x
        → x + succℤ k   ＝ succℤ k + x
  step₁ k IH = x + succℤ k   ＝⟨ ℤ-right-succ x k   ⟩
               succℤ (x + k) ＝⟨ ap succℤ IH        ⟩
               succℤ (k + x) ＝⟨ ℤ-left-succ k x ⁻¹ ⟩
               succℤ k + x   ∎

  step₂ : (k : ℤ)
        → x + succℤ k ＝ succℤ k + x
        → x + k       ＝ k + x
  step₂ k IH = succℤ-lc I
   where
    I : succℤ (x + k) ＝ succℤ (k + x)
    I = succℤ (x + k) ＝⟨ ℤ-right-succ x k ⁻¹ ⟩
        x + succℤ k   ＝⟨ IH                  ⟩
        succℤ k + x   ＝⟨ ℤ-left-succ k x     ⟩
        succℤ (k + x) ∎

\end{code}

As a corollary of commutativity, we prove that predℤ x ＝ -1 + x.

\begin{code}

ℤ-pred-is-minus-one : (x : ℤ) → predℤ x ＝ negsucc 0 + x
ℤ-pred-is-minus-one x = ℤ+-comm x (negsucc 0)

ℤ+-assoc : (a b c : ℤ) → (a + b) + c ＝ a + (b + c)
ℤ+-assoc a b = ℤ-induction base step₁ step₂
 where
  base : (a + b) + pos 0 ＝ a + (b + pos 0)
  base = refl

  step₁ : (k : ℤ)
        → (a + b) + k       ＝ a + (b + k)
        → (a + b) + succℤ k ＝ a + (b + succℤ k)
  step₁ k IH = (a + b) + succℤ k   ＝⟨ ℤ-right-succ (a + b) k          ⟩
               succℤ ((a + b) + k) ＝⟨ ap succℤ IH                     ⟩
               succℤ (a + (b + k)) ＝⟨ ℤ-right-succ a (b + k) ⁻¹       ⟩
               a + succℤ (b + k)   ＝⟨ ap (a +_) (ℤ-right-succ b k ⁻¹) ⟩
               a + (b + succℤ k)   ∎

  step₂ : (k : ℤ)
        → (a + b) + succℤ k ＝ a + (b + succℤ k)
        → (a + b) + k       ＝ a + (b + k)
  step₂ k IH = succℤ-lc I
   where
    I : succℤ (a + b + k) ＝ succℤ (a + (b + k))
    I = succℤ ((a + b) + k)        ＝⟨ ℤ-right-succ (a + b) k ⁻¹    ⟩
        (a + b) + succℤ k          ＝⟨ IH                           ⟩
        a + (b + succℤ k)          ＝⟨ ap (a +_) (ℤ-right-succ b k) ⟩
        a + succℤ (b + k)          ＝⟨ ℤ-right-succ a (b + k)       ⟩
        succℤ (a + (b + k))        ∎

ℤ+-rearrangement : (a b c : ℤ) → a + c + b ＝ a + (b + c)
ℤ+-rearrangement a b c = a + c + b   ＝⟨ ℤ+-assoc a c b          ⟩
                         a + (c + b) ＝⟨ ap (a +_) (ℤ+-comm c b) ⟩
                         a + (b + c) ∎

\end{code}

Following is the first use of ℤ-induction, which is used to prove that
integer addition is cancellable. In this case, using the induction
principle as opposed to pattern matching is preferable, since it
avoids the use of predℤ in the proof.

\begin{code}

ℤ+-lc : (x y z : ℤ) → z + x ＝ z + y → x ＝ y
ℤ+-lc x y = ℤ-induction base step₁ step₂
 where
  base : pos 0 + x ＝ pos 0 + y → x ＝ y
  base e = x           ＝⟨ ℤ-zero-left-neutral x ⁻¹ ⟩
           pos 0 + x   ＝⟨ e                        ⟩
           pos 0 + y   ＝⟨ ℤ-zero-left-neutral y    ⟩
           y           ∎

  step₁ : (k : ℤ)
        → (k + x ＝ k + y → x ＝ y)
        → succℤ k + x ＝ succℤ k + y
        → x ＝ y
  step₁ k IH e = IH (succℤ-lc I)
   where
    I : succℤ (k + x) ＝ succℤ (k + y)
    I = succℤ (k + x)  ＝⟨ ℤ-left-succ k x ⁻¹ ⟩
        succℤ k + x    ＝⟨ e                  ⟩
        succℤ k + y    ＝⟨ ℤ-left-succ k y    ⟩
        succℤ (k + y)  ∎

  step₂ : (k : ℤ)
        → (succℤ k + x ＝ succℤ k + y → x ＝ y)
        → k + x ＝ k + y
        → x ＝ y
  step₂ k IH e = IH I
   where
    I : succℤ k + x ＝ succℤ k + y
    I = succℤ k + x    ＝⟨ ℤ-left-succ k x    ⟩
        succℤ (k + x)  ＝⟨ ap succℤ e         ⟩
        succℤ (k + y)  ＝⟨ ℤ-left-succ k y ⁻¹ ⟩
        succℤ k + y    ∎

\end{code}

Proving that negation distributes over addition is proved by induction
on natural numbers, by considering the positive and negative case in
one argument. As such, we first have 2 lemmas which are then used to
conclude that negation distributes over addition. This strategy is
also used repeatedly in this development of integers.

\begin{code}

negation-dist₀ : (x : ℤ) (y : ℕ) → (- x) + (- pos y) ＝ - (x + pos y)
negation-dist₀ x = ℕ-induction base step
 where
  base : (- x) + (- pos 0) ＝ - (x + pos 0)
  base = refl

  step : (k : ℕ)
       → (- x) + (- pos k)        ＝ - (x + pos k)
       → (- x) + (- pos (succ k)) ＝ - (x + pos (succ k))
  step k IH = (- x) + negsucc k            ＝⟨ ap ((- x) +_) (negsucctopredℤ k) ⟩
              (- x) + predℤ (- pos k)      ＝⟨ ℤ-right-pred (- x) (- pos k)     ⟩
              predℤ ((- x) + (- pos k))    ＝⟨ ap predℤ IH                      ⟩
              predℤ (- (x + pos k))        ＝⟨ predminus (x + pos k)            ⟩
              - (x + pos (succ k))         ∎

negation-dist₁ : (x : ℤ) → (y : ℕ) → (- x) + (- (negsucc y)) ＝ - (x + negsucc y)
negation-dist₁ x = ℕ-induction base step
 where
  base : ((- x) + (- negsucc 0)) ＝ (- (x + negsucc 0))
  base = succℤtominuspredℤ x

  step : (k : ℕ)
       → (- x) + pos (succ k)         ＝ - (x + negsucc k)
       → (- x) + (- negsucc (succ k)) ＝ - (x + negsucc (succ k))
  step k IH = (- x) + succℤ (pos (succ k)) ＝⟨ ℤ-right-succ (- x) (pos (succ k)) ⟩
              succℤ ((- x) + pos (succ k)) ＝⟨ ap succℤ IH                       ⟩
              succℤ (- (x +negsucc k))     ＝⟨ succℤtominuspredℤ (x +negsucc k)  ⟩
              - (x + negsucc (succ k))     ∎

negation-dist : (x y : ℤ) → (- x) + (- y) ＝ - (x + y)
negation-dist x (pos y)     = negation-dist₀ x y
negation-dist x (negsucc y) = negation-dist₁ x y

\end{code}

The strategy above is used to prove that x - x ＝ (- x) + x ＝ 0 for all integers.

\begin{code}

ℤ-sum-of-inverse-is-zero₀ : (x : ℕ) → pos x + (- pos x) ＝ pos 0
ℤ-sum-of-inverse-is-zero₀ = ℕ-induction base step
 where
  base : pos 0 + (- pos 0) ＝ pos 0
  base = refl

  step : (k : ℕ)
       → pos k + (- pos k)               ＝ pos 0
       → pos (succ k) + (- pos (succ k)) ＝ pos 0
  step 0        IH = refl
  step (succ k) IH = predℤ (pos (succ (succ k)) + negsucc k) ＝⟨ i  ⟩
                     (pos (succ k) + (- pos (succ k)))       ＝⟨ IH ⟩
                     pos 0                                   ∎
   where
    i = ℤ-left-pred (pos (succ (succ k))) (negsucc k) ⁻¹

ℤ-sum-of-inverse-is-zero₁ : (x : ℕ) → negsucc x - negsucc x ＝ pos 0
ℤ-sum-of-inverse-is-zero₁ = ℕ-induction base step
 where
  base : (negsucc 0 + (- negsucc 0)) ＝ pos 0
  base = refl

  step : (k : ℕ)
       → negsucc k + (- negsucc k)               ＝ pos 0
       → negsucc (succ k) + (- negsucc (succ k)) ＝ pos 0
  step k IH = negsucc (succ k) + (- negsucc (succ k))  ＝⟨ i  ⟩
              succℤ (succℤ (negsucc (succ k)) + pos k) ＝⟨ IH ⟩
              pos 0                                    ∎
   where
    i = ap succℤ (ℤ-left-succ (negsucc (succ k)) (pos k) ⁻¹)

ℤ-sum-of-inverse-is-zero : (x : ℤ) → x + (- x) ＝ pos 0
ℤ-sum-of-inverse-is-zero (pos x)     = ℤ-sum-of-inverse-is-zero₀ x
ℤ-sum-of-inverse-is-zero (negsucc x) = ℤ-sum-of-inverse-is-zero₁ x

ℤ-sum-of-inverse-is-zero' : (x : ℤ) → (- x) + x ＝ pos 0
ℤ-sum-of-inverse-is-zero' x = ℤ+-comm (- x) x ∙ ℤ-sum-of-inverse-is-zero x

\end{code}
