\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Plus-Type where

open import Universes public

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y

\end{code}
