Martin Escardo 6th May 2022

Type-class for notation for underlying things.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Notation.UnderlyingType where

open import MLTT.Spartan

record Underlying-Type {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
 field
  ⟨_⟩ : X → Y

open Underlying-Type {{...}} public

\end{code}
