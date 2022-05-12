Our Spartan (intensional) Martin-Löf type theory has the empty type ∅,
the unit type 𝟙, two-point-type 𝟚, natural numbers ℕ, product types Π,
sum types Σ (and hence binary product types _×_), sum types _+_,
identity types _≡_, and universes 𝓤, 𝓥, 𝓦, ....

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module SpartanMLTT where

open import Empty           public
open import Unit            public
open import Two             public
open import NaturalNumbers  public
open import Plus            public
open import Pi              public
open import Sigma           public
open import Universes       public
open import Id              public

open import GeneralNotation public

\end{code}
