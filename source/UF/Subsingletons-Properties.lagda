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

identifications-in-props-are-refl : {X : 𝓤 ̇ } (i : is-prop X) (x : X)
                                  → i x x ＝ refl
identifications-in-props-are-refl i x = props-are-sets i (i x x) refl

transport-over-prop : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x} (i : is-prop X)
                    → transport Y (i x x) y ＝ y
transport-over-prop {𝓤} {𝓥} {X} {Y} {x} {y} i =
 ap (λ - → transport Y - y) (identifications-in-props-are-refl i x)

transport-over-prop' : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {x : X} {y : Y x} (i : is-prop X)
                       (p : x ＝ x)
                     → transport Y p y ＝ y
transport-over-prop' {𝓤} {𝓥} {X} {Y} {x} {y} i p =
 ap (λ - → transport Y - y) (props-are-sets i p refl)

\end{code}
