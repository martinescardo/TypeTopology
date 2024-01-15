Martin Escardo 1st January 2022

Type-class for notation for canonical maps. Our convention here is
that a canonical map is something we decide to call a canonical map.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Notation.CanonicalMap where

open import MLTT.Spartan

record Canonical-Map {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 field
  ι : X → Y

open Canonical-Map {{...}} public

canonical-map : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → {{_ : Canonical-Map X Y}} → X → Y
canonical-map X Y = ι

[_] : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {{ r : Canonical-Map X Y }} → X → Y
[_] = ι

\end{code}
