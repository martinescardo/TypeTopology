Andrew Sneap, 26 November 2021

This file defines negation of integers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Type

module Integers.Negation where

-_ : ℤ → ℤ
-_ (pos 0)        = pos 0
-_ (pos (succ x)) = negsucc x
-_ (negsucc x)    = pos (succ x)

infix 31 -_

\end{code}

These proofs are all by definition, however we must consider each case
seperately.

\begin{code}

predminus : (x : ℤ) → predℤ (- x) ＝ (- succℤ x)
predminus (pos 0)            = refl
predminus (pos (succ x))     = refl
predminus (negsucc 0)        = refl
predminus (negsucc (succ x)) = refl

negsucctopredℤ : (k : ℕ) → negsucc k ＝ predℤ (- pos k)
negsucctopredℤ 0        = refl
negsucctopredℤ (succ k) = refl

succℤtominuspredℤ : (x : ℤ) → succℤ (- x) ＝ (- predℤ x)
succℤtominuspredℤ (pos 0)               = refl
succℤtominuspredℤ (pos (succ 0))        = refl
succℤtominuspredℤ (pos (succ (succ x))) = refl
succℤtominuspredℤ (negsucc x)           = refl

minus-minus-is-plus : (x : ℤ) → - (- x) ＝ x
minus-minus-is-plus (pos 0)        = refl
minus-minus-is-plus (pos (succ x)) = refl
minus-minus-is-plus (negsucc x)    = refl

\end{code}
