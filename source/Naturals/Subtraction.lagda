Martin Escardo, started 5th May 2018

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.Subtraction where

open import MLTT.Spartan hiding (_^_)

open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order
open import Naturals.Properties
open import Notation.Order

subtraction : (m n : ℕ) → m ≤ n → Σ k ꞉ ℕ , k +' m ＝ n
subtraction 0        n        l = n , refl
subtraction (succ m) 0        l = 𝟘-elim l
subtraction (succ m) (succ n) l = pr₁ IH , ap succ (pr₂ IH)
 where
  IH : Σ k ꞉ ℕ , k +' m ＝ n
  IH = subtraction m n l

cosubtraction : (m n : ℕ) → (Σ k ꞉ ℕ , k +' m ＝ n) → m ≤ n
cosubtraction 0        n                (.n , refl) = ⋆
cosubtraction (succ m) 0                (k , p) = positive-not-zero (k +' m) p
cosubtraction (succ m) (succ .(k +' m)) (k , refl) =
 cosubtraction m (k +' m) (k , refl)

subtraction' : (x y : ℕ) → x < y → Σ z ꞉ ℕ , (z +' x ＝ y)
subtraction' 0        0        l = 𝟘-induction l
subtraction' 0        (succ y) l = (succ y) , refl
subtraction' (succ x) (succ y) l = pr₁ IH , ap succ (pr₂ IH)
 where
  IH : Σ z ꞉ ℕ , z +' x ＝ y
  IH = subtraction' x y l

subtraction'' : (x y : ℕ) → x < y → Σ z ꞉ ℕ , (succ z +' x ＝ y)
subtraction'' x 0               l = 𝟘-elim l
subtraction'' 0        (succ y) l = y , refl
subtraction'' (succ x) (succ y) l = pr₁ IH , ap succ (pr₂ IH)
 where
  IH : Σ z ꞉ ℕ , (succ z +' x ＝ y)
  IH = subtraction'' x y l

\end{code}
