Martin Escardo 6th May 2022

Type-class for notation for underlying types of ordered sets.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Notation.UnderlyingType where

open import MLTT.Spartan

record Underlying-Type {𝓤} (X : 𝓤 ̇ ) (𝓥 : Universe) : 𝓤 ⊔ 𝓥 ⁺ ̇  where
 field
  ⟨_⟩ : X → 𝓥 ̇

open Underlying-Type {{...}} public

\end{code}
