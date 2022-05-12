Martin Escardo, January 2021.

It is possible to work with lists *defined* from the ingredients of
our Spartan MLTT (see the module Fin.lagda). For the moment we are
Athenian in this respect.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

module List where

open import SpartanMLTT

data List {𝓤} (X : 𝓤 ̇ ) : 𝓤 ̇  where
 [] : List X
 _∷_ : X → List X → List X

infixr 3 _∷_

equal-heads : {X : 𝓤 ̇ } {x y : X} {s t : List X}
            → x ∷ s ≡ y ∷ t
            → x ≡ y
equal-heads refl = refl

equal-tails : {X : 𝓤 ̇ } {x y : X} {s t : List X}
            → x ∷ s ≡ y ∷ t
            → s ≡ t
equal-tails {𝓤} {X} refl = refl

[_] : {X : 𝓤 ̇ } → X → List X
[ x ] = x ∷ []

_++_ : {X : 𝓤 ̇ } → List X → List X → List X
[]      ++ t = t
(x ∷ s) ++ t = x ∷ (s ++ t)

infixr 4 _++_

[]-right-neutral : {X : 𝓤 ̇ } (s : List X) → s ≡ s ++ []
[]-right-neutral []      = refl
[]-right-neutral (x ∷ s) = ap (x ∷_) ([]-right-neutral s)

++-assoc : {X : 𝓤 ̇ } → associative (_++_ {𝓤} {X})
++-assoc []      t u = refl
++-assoc (x ∷ s) t u = ap (x ∷_) (++-assoc s t u)

foldr : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y → Y) → Y → List X → Y
foldr _·_ ε []       = ε
foldr _·_ ε (x ∷ xs) = x · foldr _·_ ε xs

map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → List X → List Y
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

_<$>_ = map

\end{code}

The above is all we need about lists for the moment, in the module
FreeGroups.lagda.
