-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.DataStructures where

-- Some definitions of standard things
-- (sorry for not using libraries).

open import InfinitePigeon.Addition
open import InfinitePigeon.Finite
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals


data List (X : Set) : Set where
 [] : List X
 _::_  : X → List X → List X

infixr 30 _::_


-- Transforms a finite list given as a map to an enumerated finite
-- list:

list : {m : ℕ} {X : Set} → (smaller m → X) → List X
list {0} s = []
list {succ m} s = s fzero :: list {m} (s ∘ fsucc)


-- Binary products:

data _×_ (X Y : Set) : Set where
 _,_ : X → Y → X × Y


infixr 20 _,_


-- The cons operation for the Cantor space:

open import InfinitePigeon.Cantor
open import InfinitePigeon.Two

_^_ : ℕ → ₂ℕ → ₂ℕ
(O ^ α) O = ₀
(O ^ α) (succ i) = α i
(succ n ^ α) O = ₁
(succ n ^ α) (succ i) = α i

infixr 30 _^_


-- Take a finite initial sublist of an infinite sequence.

take : (m : ℕ) {X : Set} → (ℕ → X) → List X
take 0 α = []
take (succ m) α = α 0 :: take m (α ∘ succ)

-- Index a finite sequence:

_!_ : {m : ℕ} → (smaller(m + 1) → ℕ) → ℕ → ℕ
_!_ {m} s n = s(fmin m n)
