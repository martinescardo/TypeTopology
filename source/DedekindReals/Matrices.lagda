Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_)

open import NaturalNumbers
open import Fin
open import Fin-Properties
open import UF-Subsingletons

open import FieldAxioms


module Matrices
  (Field : Ordered-Field 𝓤 { 𝓥 } { 𝓦 })
  where

F : 𝓤 ̇
F = ⟨ Field ⟩

e₀ : F
e₀ = additive-identity Field

e₁ : F
e₁ = multiplicative-identity Field

_+_ : F → F → F
_+_ = addition Field 

+-comm : (x y : F) → x + y ≡ y + x
+-comm = addition-commutative Field

_*_ : F → F → F
_*_ = multiplication Field

F-is-set : is-set F
F-is-set = underlying-type-is-set Field

F-zero-left-neutral : (x : F) → e₀ + x ≡ x
F-zero-left-neutral = zero-left-neutral Field

matrix : (n m : ℕ) → 𝓤 ̇
matrix n m = Fin n → Fin m → F

0ₘ : {n m : ℕ} → matrix n m
0ₘ i j = e₀

row : {n m : ℕ} → Fin n → matrix n m → matrix 1 m
row fn A i j = A fn j

column : {n m : ℕ} → Fin m → matrix n m → matrix n 1
column fm A i j = A i fm

inner-product : {n : ℕ} → matrix 1 n → matrix n 1 → matrix 1 1 -- With help from "An Agda proof of Valiant's aglorithm for context free parsing"
inner-product {zero} A B i j = e₀
inner-product {succ n} A B i j = (A fzero fzero * B fzero fzero) + inner-product {n} (λ i j → A fzero (suc j)) (λ i j → B (suc i) j) i j

outer-product : {n : ℕ} → matrix n 1 → matrix 1 n → matrix n n
outer-product A B i j = A i fzero * B fzero j

_*M_ : {n m q : ℕ} → matrix n m → matrix m q → matrix n q
_*M_ A B i j = inner-product (row i A) (column j B) fzero fzero

_≈_ : {n m : ℕ} → (A B : matrix n m) → 𝓤 ̇
_≈_ {n} {m} A B = (i : Fin n) → (j : Fin m) → A i j ≡ B i j

infix 19 _≈_

_+M_ : {n m : ℕ} → matrix n m → matrix n m → matrix n m
_+M_ A B i j = A i j + B i j

+M-comm : {n m : ℕ} → (A B : matrix n m) → (A +M B) ≈ (B +M A)
+M-comm A B i j = +-comm (A i j) (B i j)

_*sM_ : {n m : ℕ} → (s : F) → matrix n m → matrix n m
_*sM_ s M i j = s * M i j

ᵗ : {n m : ℕ} → matrix n m → matrix m n
ᵗ A i j = A j i

transpose-involutive : {n m : ℕ} → (M : matrix n m) → ᵗ (ᵗ M) ≡ M
transpose-involutive M = refl

transpose-involutive' : {n m : ℕ} → (M : matrix n m) → ᵗ (ᵗ M) ≈ M
transpose-involutive' M i j = ᵗ (ᵗ M) i j ≡⟨ by-definition ⟩
                              ᵗ M j i     ≡⟨ by-definition ⟩
                              M i j ∎

+M-zero-left-neutral : {n m : ℕ} → (A : matrix n m) → 0ₘ +M A ≈ A
+M-zero-left-neutral A i j = (0ₘ +M A) i j    ≡⟨ by-definition ⟩
                             (0ₘ i j + A i j) ≡⟨ by-definition ⟩
                             (e₀ + A i j)     ≡⟨ F-zero-left-neutral (A i j) ⟩
                             A i j ∎


open import UF-FunExt
open import UF-Subsingletons-FunExt

matrix-equiv→equality : Fun-Ext → {n m : ℕ} → (A B : matrix n m) → A ≈ B → A ≡ B
matrix-equiv→equality fe {n} {m} A B equiv = dfunext fe (λ i → dfunext fe (λ j → equiv i j))











