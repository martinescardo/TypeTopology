Martin Escardo 1st January 2022

Type-class for notation for canonical maps. Our convention here is
that a canonical map is something we decide to call a canonical map.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CanonicalMap where

open import SpartanMLTT

record Canonical-Map {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 field
  ι : X → Y

open Canonical-Map {{...}} public

\end{code}
