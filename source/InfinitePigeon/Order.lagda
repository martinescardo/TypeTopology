Martin Escardo and Paulo Oliva 2011

\begin{code}

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.Order where

open import InfinitePigeon.Addition
open import InfinitePigeon.Equality
open import InfinitePigeon.Logic
open import InfinitePigeon.Naturals

_≤_ : ℕ → ℕ → Ω
x ≤ y = ∃ \(n : ℕ) → x + n ≡ y

_<_ : ℕ → ℕ → Ω
x < y = ∃ \(n : ℕ) → x + n + 1 ≡ y

infix 29 _<_
infix 29 _≤_

\end{code}

This is how we are going to write inequality proofs (when possible):

\begin{code}

less-proof : {x : ℕ} → (n : ℕ) → x < x + n + 1
less-proof n = ∃-intro n reflexivity

\end{code}
