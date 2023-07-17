-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --exact-split #-}

module Pigeon.ProgramsWithoutSpecification where

open import Pigeon.Addition
open import Pigeon.Cantor
open import Pigeon.Finite
open import Pigeon.FinitePigeon
open import Pigeon.Logic
open import Pigeon.Naturals
open import Pigeon.Two

program₁ : ₂ℕ → ℕ → ₂
program₁ α m = ∃-witness(Theorem α m)

program₂ : ₂ℕ → (m : ℕ) → (smaller(m + 1) → ℕ)
program₂ α m = ∃-witness(∃-elim (Theorem α m))
