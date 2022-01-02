Martin Escardo 31st December 2021

Type-class for notation for strict orders.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module OrderNotation where

open import SpartanMLTT

record Strict-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _<_ : X → Y → 𝓦  ̇

 _≮_ : X → Y → 𝓦 ̇
 p ≮ q = ¬(p < q)

 _>_ : Y → X → 𝓦 ̇
 p > q = q < p

open Strict-Order {{...}} public

record Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _≤_ : X → Y → 𝓦  ̇

 _≥_ : Y → X → 𝓦 ̇
 p ≥ q = q ≤ p

open Order {{...}} public

record Square-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _⊑_ : X → Y → 𝓦  ̇

 _⊒_ : Y → X → 𝓦 ̇
 p ⊒ q = q ⊑ p

open Square-Order {{...}} public

\end{code}
