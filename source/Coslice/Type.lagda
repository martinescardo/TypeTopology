Jonathan Sterling, 22nd March 2023.

In this module we define the coslice of a universe under a given type; in fact,
our construction is slightly more general, as we allow the given type to lie in
a different universe. This is useful for characterizing things like small
reflective subuniverses, which arise when studying impredicativity.

\begin{code}
{-# OPTIONS --safe --without-K #-}

module Coslice.Type where

open import MLTT.Spartan

_↓_ : 𝓥 ̇ → (𝓤 : Universe) → 𝓥 ⊔ 𝓤 ⁺ ̇
A ↓ 𝓤 = Σ I ꞉ 𝓤 ̇ , (A → I)

Coslice : 𝓤 ̇ → 𝓤 ⁺ ̇
Coslice A = A ↓ _

module _ {A : 𝓥 ̇ } where
 target : A ↓ 𝓤 → 𝓤 ̇
 target (I , α) = I

 alg : (X : A ↓ 𝓤) → A → target X
 alg (I , α) = α

\end{code}
