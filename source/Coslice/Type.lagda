Jonathan Sterling, 22nd March 2023.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Coslice.Type where

open import MLTT.Spartan

coslice : 𝓤 ̇ → 𝓤 ⁺ ̇
coslice {𝓤} A = Σ I ꞉ 𝓤 ̇ , (A → I)

module _ {A : 𝓤 ̇ } where
 target : coslice A → 𝓤 ̇
 target (I , α) = I

 alg : (X : coslice A) → A → target X
 alg (I , α) = α

\end{code}
