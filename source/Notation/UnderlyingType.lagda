Martin Escardo 4th January 2023

Type-class for notation for underlying types. Our convention here is
that an underlying type something we decide to call an underlying
type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Notation.UnderlyingType where

open import MLTT.Spartan

record Underlying-Type {𝓤} {𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 field
  ⟨_⟩ : X → Y

open Underlying-Type {{...}} public

underlying-type : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → {{_ : Underlying-Type X Y}} → X → Y
underlying-type X Y = ⟨_⟩

\end{code}
