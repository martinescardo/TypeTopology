Theo Hepburn, started February 2025.

Contains proofs about natural number exponentiation
beyond those provided in Naturals.Exponentiation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TGH.MyExponentiation where

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_)

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication renaming
 (mult-commutativity to *-comm ; mult-associativity to *-assoc)
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import UF.Base

^-over-* : (n m k : ℕ) → (n * m) ^ k ＝ (n ^ k * m ^ k)
^-over-* n m zero = refl
^-over-* n m (succ k)
 = n * m * (n * m) ^ k ＝⟨ ap (λ z → n * m * z) ((^-over-* n m k)) ⟩
   (n * m) * (n ^ k * m ^ k) ＝⟨ *-assoc n m (n ^ k * m ^ k) ⟩
   n * (m * (n ^ k * m ^ k)) ＝⟨ ap (λ z → n * z)
                                 (*-assoc m (n ^ k) (m ^ k) ⁻¹) ⟩
   n * ((m * n ^ k) * m ^ k) ＝⟨ *-assoc n (m * n ^ k) (m ^ k) ⁻¹ ⟩
   n * (m * n ^ k) * m ^ k ＝⟨ ap (λ z → n * z * m ^ k) (*-comm m (n ^ k)) ⟩
   n * (n ^ k * m) * m ^ k ＝⟨ ap (λ z → z * m ^ k) (*-assoc n (n ^ k) m ⁻¹) ⟩
   (n * n ^ k) * m * m ^ k ＝⟨ *-assoc (n * n ^ k) m (m ^ k) ⟩
   n * n ^ k * (m * m ^ k) ∎

\end{code}
