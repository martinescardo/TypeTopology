Martin Escardo 31st December 2021

Type-class for notation for strict orders.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module OrderNotation where

open import SpartanMLTT

record Strict-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _<_ : X → Y → 𝓦  ̇

 _≮_ : X → Y → 𝓦 ̇
 _>_ _≯_ : Y → X → 𝓦 ̇

 x ≮ y = ¬(x < y)
 y > x = x < y
 y ≯ x = ¬ (y > x)

 infix 30 _<_
 infix 30 _>_
 infix 30 _≮_
 infix 30 _≯_

open Strict-Order {{...}} public

record Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _≤_ : X → Y → 𝓦  ̇

 _≰_ : X → Y → 𝓦 ̇
 _≥_ _≱_ : Y → X → 𝓦 ̇

 x ≰ y = ¬(x ≤ y)
 y ≥ x = x ≤ y
 y ≱ x = ¬(y ≥ x)

 infix 30 _≤_
 infix 30 _≥_
 infix 30 _≰_
 infix 30 _≱_


open Order {{...}} public

record Strict-Square-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _⊏_ : X → Y → 𝓦  ̇

 _⊐_ : Y → X → 𝓦 ̇
 x ⊐ y = y ⊏ x

 infix 30 _⊏_
 infix 30 _⊐_

open Strict-Square-Order {{...}} public

record Square-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _⊑_ : X → Y → 𝓦  ̇

 _⊒_ : Y → X → 𝓦 ̇
 x ⊒ y = y ⊑ x

 infix 30 _⊑_
 infix 30 _⊒_

open Square-Order {{...}} public

record Strict-Curly-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _≺_ : X → Y → 𝓦  ̇

 _≻_ : Y → X → 𝓦 ̇
 x ≻ y = y ≺ x

 infix 30 _≺_
 infix 30 _≻_

open Strict-Curly-Order {{...}} public

record Curly-Order {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _≼_ : X → Y → 𝓦  ̇

 _≽_ : Y → X → 𝓦 ̇
 x ≽ y = y ≼ x

 infix 30 _≼_
 infix 30 _≽_

open Curly-Order {{...}} public

\end{code}
