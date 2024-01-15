-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.ProgramsWithoutSpecificationBis where

open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Finite
open import InfinitePigeon.FinitePigeon
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals
open import InfinitePigeon.Two

program₁ : ₂ℕ → ℕ → ₂
program₁ α m = f(Theorem α m)
 where f : Finite-Pigeonhole α m → ₂
       f(∃-intro b proof) = b

program₂ : ₂ℕ → (m : ℕ) → (smaller(m + 1) → ℕ)
program₂ α m = f(Theorem α m)
 where f : Finite-Pigeonhole α m → (smaller(m + 1) → ℕ)
       f(∃-intro b (∃-intro s proof)) = s
