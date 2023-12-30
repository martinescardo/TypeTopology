Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Subsingletons-Properties where

open import MLTT.Spartan
open import UF.Hedberg
open import UF.Sets
open import UF.Subsingletons

props-are-Id-collapsible : {X : 𝓤 ̇ } → is-prop X → Id-collapsible X
props-are-Id-collapsible h {x} {y} = (λ p → h x y) , (λ p q → refl)

props-are-sets : {X : 𝓤 ̇ } → is-prop X → is-set X
props-are-sets h = Id-collapsibles-are-sets (props-are-Id-collapsible h)

singletons-are-sets : {X : 𝓤 ̇ } → is-singleton X → is-set X
singletons-are-sets i = props-are-sets (singletons-are-props i)

\end{code}
