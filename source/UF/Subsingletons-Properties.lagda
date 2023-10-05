Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module UF.Subsingletons-Properties where

open import MLTT.Spartan
open import UF.Hedberg
open import UF.Sets
open import UF.Subsingletons

props-are-Id-collapsible : {X : 𝓤 ̇ } → is-prop X → Id-collapsible X
props-are-Id-collapsible h {x} {y} = (λ p → h x y) , (λ p q → refl)

props-are-sets : {X : 𝓤 ̇ } → is-prop X → is-set X
props-are-sets h = Id-collapsibles-are-sets (props-are-Id-collapsible h)

\end{code}
