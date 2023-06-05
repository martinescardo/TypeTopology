-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --safe --exact-split --no-sized-types --no-guardedness --auto-inline #-}

module Pigeon.Order where

open import Pigeon.Addition
open import Pigeon.Equality
open import Pigeon.Logic
open import Pigeon.Naturals

_≤_ : ℕ → ℕ → Ω
x ≤ y = ∃ \(n : ℕ) → x + n ≡ y

_<_ : ℕ → ℕ → Ω
x < y = ∃ \(n : ℕ) → x + n + 1 ≡ y

infix 29 _<_
infix 29 _≤_

-- This is how we are going to write inequality proofs (when possible):

less-proof : {x : ℕ} → (n : ℕ) → x < x + n + 1
less-proof n = ∃-intro n reflexivity
