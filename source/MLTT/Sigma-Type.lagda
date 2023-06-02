\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module MLTT.Sigma-Type where

open import MLTT.Universes

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

infixr 50 _,_

\end{code}
