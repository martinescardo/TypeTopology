Martin Escardo, 20-21 December 2012.

If X and Y come with orders, both denoted by ≤, then the lexicographic
order on X × Y is defined by

  (x , y) ≤ (x' , y') ⇔ x ≤ x' ∧ (x ≡ x' → y ≤ y').

More generally, we can consider the lexicographic product of two
binary relations R on X and S on Y, which is a relation on X × Y, or
even on (Σ \(x : X) → Y x) if Y and S depend on X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LexicographicOrder where

open import SpartanMLTT

bin-rel : ∀ {U} → U ̇ → U ′ ̇
bin-rel {U} X = X → X → U ̇

lex-prod : ∀ {U V} {X : U ̇} {Y : X → V ̇} →  bin-rel X → ((x : X) → bin-rel(Y x)) → bin-rel(Σ \(x : X) → Y x)
lex-prod R S (x , y) (x' , y') = R x x' × ((r : x ≡ x') → S x y (transport _ (r ⁻¹) y'))
