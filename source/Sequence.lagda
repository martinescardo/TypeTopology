Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-} 

open import UF-FunExt

module Sequence (fe : ∀ {U V} → FunExt U V) where

open import SpartanMLTT hiding (_+_)
open import UF-Retracts
open import Naturals
open import NaturalsAddition

_∶∶_ : ∀ {U} {X : ℕ → U ̇} → X 0 → ((n : ℕ) → X(succ n)) → ((n : ℕ) → X n)
(x ∶∶ α) 0 = x
(x ∶∶ α) (succ n) = α n


hd : ∀ {U} {X : ℕ → U ̇} → ((n : ℕ) → X n) → X 0
hd α = α 0


tl : ∀ {U} {X : ℕ → U ̇} → ((n : ℕ) → X n) → ((n : ℕ) → X(succ n))
tl α n = α(succ n)


hd-tl-eta : ∀ {U} {X : ℕ → U ̇} {α : (n : ℕ) → X n} → (hd α ∶∶ tl α) ≡ α
hd-tl-eta {U} {X} = funext fe lemma
 where 
  lemma : {α : (n : ℕ) → X n} → (i : ℕ) → (hd α ∶∶ tl α) i ≡ α i
  lemma 0 = refl
  lemma (succ i) = refl


cons : ∀ {U} {X : ℕ → U ̇} → X 0 × ((n : ℕ) → X(succ n)) → ((n : ℕ) → X n)
cons(x , α) = x ∶∶ α

cons-retraction : ∀ {U} {X : ℕ → U ̇} → retraction(cons {U} {X})
cons-retraction α = (hd α , tl α) , hd-tl-eta 

\end{code}

(In fact it is an isomorphism, but I won't bother.)

\begin{code}

tail : ∀ {U} {X : ℕ → U ̇} → (n : ℕ) → ((i : ℕ) → X i) → ((i : ℕ) → X(i + n))
tail n α i = α(i + n)

\end{code}
