Jonathan Sterling, 22nd March 2023.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Coslice.Type where

open import MLTT.Spartan

Coslice : 𝓤 ̇ → 𝓤 ⁺ ̇
Coslice {𝓤} A = Σ I ꞉ 𝓤 ̇ , (A → I)

module _ {A : 𝓤 ̇ } where
 target : Coslice A → 𝓤 ̇
 target (I , α) = I

 alg : (X : Coslice A) → A → target X
 alg (I , α) = α

\end{code}
