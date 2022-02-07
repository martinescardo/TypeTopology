Andrew Sneap - 27th April 2021

In this file I define Integers, along with an induction principle for integers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalsAddition renaming (_+_ to _ℕ+_)  --TypeTopology
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)

module IntegersB where

data ℤ : 𝓤₀ ̇ where 
 pos     : ℕ → ℤ
 negsucc : ℕ → ℤ

predℤ : ℤ → ℤ
predℤ (pos 0)        = negsucc 0
predℤ (pos (succ x)) = pos x
predℤ (negsucc x)    = negsucc (succ x)

succℤ : ℤ → ℤ
succℤ (pos x)            = pos (succ x)
succℤ (negsucc 0)        = pos 0
succℤ (negsucc (succ x)) = negsucc x

ℤ-induction : {A : ℤ → 𝓤 ̇} → A (pos 0)
                             → ((k : ℤ) → A k → A (succℤ k))
                             → ((k : ℤ) → A (succℤ k) → A k)
                             → (x : ℤ)
                             → A x 
ℤ-induction base step₀ step₁ (pos 0)            = base
ℤ-induction base step₀ step₁ (pos (succ x))     = step₀ (pos x) (ℤ-induction base step₀ step₁ (pos x))
ℤ-induction base step₀ step₁ (negsucc 0)        = step₁ (negsucc 0) base
ℤ-induction base step₀ step₁ (negsucc (succ x)) = step₁ (negsucc (succ x)) (ℤ-induction base step₀ step₁ (negsucc x))

succpredℤ : (x : ℤ) → succℤ (predℤ x) ≡ x 
succpredℤ (pos 0)        = refl
succpredℤ (pos (succ x)) = refl
succpredℤ (negsucc x)    = refl

predsuccℤ : (x : ℤ) → predℤ (succℤ x) ≡ x 
predsuccℤ (pos x)            = refl
predsuccℤ (negsucc 0)        = refl
predsuccℤ (negsucc (succ x)) = refl



{-

_-_ : ℤ → ℤ → ℤ 
x - pos 0        = x + (- pos 0)
x - pos (succ y) = x + (- pos (succ y))
x - negsucc y    = x + (- negsucc y)



-}

\end{code}
