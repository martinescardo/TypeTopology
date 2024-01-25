\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Plus-Type where

open import MLTT.Universes public

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y

\end{code}
