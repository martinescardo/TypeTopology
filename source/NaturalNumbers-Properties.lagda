Natural numbers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module NaturalNumbers-Properties where

open import Universes
open import NaturalNumbers
open import Negation
open import Id
open import Empty

a-peano-axiom : {n : ℕ} → succ n ≢ 0
a-peano-axiom ()

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-lc = ap pred

succ-no-fp : (n : ℕ) → n ≡ succ n → 𝟘 {𝓤}
succ-no-fp zero ()
succ-no-fp (succ n) p = succ-no-fp n (succ-lc p)

\end{code}
