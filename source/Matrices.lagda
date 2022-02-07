Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_)

open import NaturalNumbers
open import Fin 
open import FieldAxioms

module Matrices
  (F : Ordered-Field 𝓤 { 𝓥 } { 𝓦 })
  where

0ₘ : ⟨ F ⟩
0ₘ = additive-identity F

1ₘ : ⟨ F ⟩
1ₘ = multiplicative-identity F

_+_ : ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
_+_ = addition F

_*_ : ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
_*_ = multiplication F

matrix : (n m : ℕ) → 𝓤 ̇
matrix n m = Fin (succ n) → Fin (succ m) → ⟨ F ⟩

+M : {n m : ℕ} → matrix n m → matrix n m → matrix n m
+M A B i j = A i j + B i j

*M : {n m q : ℕ} → matrix n m → matrix m q → matrix n q
*M {n} {m} {q} A B i j   = induction 0ₘ (λ k ACC → ACC + (A i (inr ⋆) * B (inr ⋆) j)) m

scalar* : {n m : ℕ} → ⟨ F ⟩ → matrix n m → matrix n m
scalar* s M i j = s * M i j

ᵗ : {n m : ℕ} → matrix n m → matrix m n
ᵗ  A i j = A j i

transpose-involutive : {n m : ℕ} → (M : matrix n m) → ᵗ (ᵗ M) ≡ M
transpose-involutive M = refl

2x2ᵢ : matrix 2 2
2x2ᵢ (suc x) (suc y) = 1ₘ
2x2ᵢ (suc x) (inr y) = 0ₘ
2x2ᵢ (inr x) (suc y) = 0ₘ
2x2ᵢ (inr x) (inr y) = 1ₘ






