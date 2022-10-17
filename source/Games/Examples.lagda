
Martin Escardo, Paulo Oliva, 2-27 July 2021

Incomplete example:

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

module Games.Examples where

open import MLTT.Spartan
open import Games.TypeTrees
open import Games.FiniteHistoryDependent

module permutations-example where

 open import MLTT.NonSpartanMLTTTypes

 no-repetitions : (n : ℕ) (X : Type) → 𝕋
 no-repetitions 0        X = []
 no-repetitions (succ n) X = X ∷ λ (x : X) → no-repetitions n (Σ y ꞉ X , y ≠ x)

 Permutations : ℕ → Type
 Permutations n = Path (no-repetitions n (Fin n))

 example-permutation2 : Permutations 2
 example-permutation2 = 𝟎 :: ((𝟏 , (λ ())) :: ⟨⟩)

 example-permutation3 : Permutations 3
 example-permutation3 = 𝟐 :: ((𝟏 :: (λ ())) :: (((𝟎 , (λ ())) , (λ ())) :: ⟨⟩))
