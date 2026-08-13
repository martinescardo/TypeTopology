Martin Escardo, 12 Feb 2018.

Moved from the file TypeTopology.TotallySeparated 22 August 2024.

We give a positive characterization of the negation of apartness.

See also
https://nforum.ncatlab.org/discussion/8282/points-of-the-localic-quotient-with-respect-to-an-apartness-relation/

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Apartness.Negation
        (pt : propositional-truncations-exist)
       where

open import Apartness.Definition
open import MLTT.Spartan

open PropositionalTruncation pt
open Apartness pt

\end{code}

The following positive formulation of ¬ (x ♯ y), which says that two
elements have the same elements apart from them iff they are not
apart, gives another way to see that it is an equivalence relation.
As far as we know, this positive characterization of the negation of
apartness is a new observation.

Notice that irreflexivity is not used in the following, but
irreflexivity is the only assumption about _♯_ used in the converse.

\begin{code}

elements-that-are-not-apart-have-the-same-apartness-class
 : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
 → is-apartness _♯_
 → ¬ (x ♯ y)
 → ((z : X) → x ♯ z ↔ y ♯ z)
elements-that-are-not-apart-have-the-same-apartness-class
 {𝓤} {𝓥} {X} x y _♯_ (p , _ , s , c) = g
 where
  g : ¬ (x ♯ y) → (z : X) → x ♯ z ↔ y ♯ z
  g n z = g₁ , g₂
   where
    g₁ : x ♯ z → y ♯ z
    g₁ a = s z y (left-fails-gives-right-holds (p z y) b n)
     where
      b : (x ♯ y) ∨ (z ♯ y)
      b = c x z y a

    n' : ¬ (y ♯ x)
    n' a = n (s y x a)

    g₂ : y ♯ z → x ♯ z
    g₂ a = s z x (left-fails-gives-right-holds (p z x) b n')
     where
      b : (y ♯ x) ∨ (z ♯ x)
      b = c y z x a

elements-with-the-same-apartness-class-are-not-apart
 : {X : 𝓤 ̇ } (x y : X) (_♯_ : X → X → 𝓥 ̇ )
 → is-irreflexive _♯_
 → ((z : X) → x ♯ z ↔ y ♯ z)
 → ¬ (x ♯ y)
elements-with-the-same-apartness-class-are-not-apart
 {𝓤} {𝓥} {X} x y _♯_ i = f
 where
  f : ((z : X) → x ♯ z ↔ y ♯ z) → ¬ (x ♯ y)
  f φ a = i y (pr₁(φ y) a)

\end{code}
