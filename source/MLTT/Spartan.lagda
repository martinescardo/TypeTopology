Our Spartan (intensional) Martin-Löf type theory has the empty type ∅,
the unit type 𝟙, two-point-type 𝟚, natural numbers ℕ, product types Π,
sum types Σ (and hence binary product types _×_), sum types _+_,
identity types _＝_, and universes 𝓤, 𝓥, 𝓦, ....

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module MLTT.Spartan where

open import MLTT.Empty           public
open import MLTT.Unit            public
open import MLTT.Two             public
open import MLTT.NaturalNumbers  public
open import MLTT.Plus            public
open import MLTT.Pi              public
open import MLTT.Sigma           public
open import MLTT.Universes       public
open import MLTT.Id              public

open import Notation.General public

\end{code}
