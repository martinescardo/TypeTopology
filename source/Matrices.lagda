Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_)

open import NaturalNumbers
open import Fin
open import UF-Subsingletons

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

+-comm : (x y : ⟨ F ⟩) → x + y ≡ y + x
+-comm = addition-commutative F

_*_ : ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
_*_ = multiplication F

F-is-set : is-set ⟨ F ⟩
F-is-set = underlying-type-is-set F

matrix : (n m : ℕ) → 𝓤 ̇
matrix n m = Fin (succ n) → Fin (succ m) → ⟨ F ⟩

_+M_ : {n m : ℕ} → matrix n m → matrix n m → matrix n m
A +M B = λ i j → A i j + B i j

*M' : {n m q : ℕ} → matrix n m → matrix m q → matrix n q
*M' {n} {m} {q} A B i j = induction 0ₘ step m
 where
  step : (k : ℕ) → ⟨ F ⟩ → ⟨ F ⟩
  step k f = f + ((A i 𝟎) * B 𝟎 j)

_*M_ : {n m q : ℕ} → matrix n m → matrix m q → matrix n q
_*M_ A B = *M' A B

scalar* : {n m : ℕ} → ⟨ F ⟩ → matrix n m → matrix n m
scalar* s M i j = s * M i j

ᵗ : {n m : ℕ} → matrix n m → matrix m n
ᵗ A i j = A j i

transpose-involutive : {n m : ℕ} → (M : matrix n m) → ᵗ (ᵗ M) ≡ M
transpose-involutive M = refl

2x2ᵢ : matrix 2 2
2x2ᵢ (suc x) (suc y) = 1ₘ
2x2ᵢ (suc x) (inr y) = 0ₘ
2x2ᵢ (inr x) (suc y) = 0ₘ
2x2ᵢ (inr x) (inr y) = 1ₘ

open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

+M-comm' : {n m : ℕ} → (A B : matrix n m) → (fsm : Fin (succ m)) → (fsn : Fin (succ n)) → (A +M B) fsn fsm ≡ (B +M A) fsn fsm
+M-comm' {n} {m} A B fsm fsn = (A +M B) fsn fsm        ≡⟨ by-definition ⟩
                                  (A fsn fsm + B fsn fsm) ≡⟨ +-comm (A fsn fsm) (B fsn fsm) ⟩
                                  (B fsn fsm + A fsn fsm) ≡⟨ by-definition ⟩
                                  (B +M A) fsn fsm        ∎


-- +M-comm : Fun-Ext → {n m : ℕ} → (A B : matrix n m) → A +M B ≡ (B +M A)
-- +M-comm fe {n} {m} A B = {!!}
{-
*M-comm' : {n : ℕ} → (A : matrix n n) → (B : matrix n n) (fsn1 fsn2 : Fin (succ n)) → (A *M B) fsn1 fsn2 ≡ (B *M A) fsn1 fsn2
*M-comm' {n} A B i j = (A *M B) i j ≡⟨ by-definition ⟩
                       induction 0ₘ (λ k α → α + (A i fzero * B fzero j)) n ≡⟨ {!!} ⟩
                       {!!} ≡⟨ {!!} ⟩
                       induction 0ₘ (λ k α → α + (B i fzero * A fzero j)) n ≡⟨ by-definition ⟩
                       (B *M A) i j ∎
-}










