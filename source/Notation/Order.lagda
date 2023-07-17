Martin Escardo 31st December 2021

Type-class for notation for strict orders.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Notation.Order where

open import MLTT.Spartan

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

record Strict-Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇)
 (_<₁_ : X → Y → 𝓣 ̇)
 (_<₂_ : Y → Z → 𝓧 ̇) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _<_<_ : X → Y → Z → 𝓣 ⊔ 𝓧 ̇

 infix 30 _<_<_

open Strict-Order-Chain {{...}} public

record Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇)
 (_≤₁_ : X → Y → 𝓣 ̇)
 (_≤₂_ : Y → Z → 𝓧 ̇) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _≤_≤_ : X → Y → Z → 𝓣 ⊔ 𝓧 ̇

 infix 30 _≤_≤_

open Order-Chain {{...}} public

\end{code}
