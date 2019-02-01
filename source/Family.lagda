Martin Escardo, 6th December 2018.

Cf. The lifting monad.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Family (𝓣 : Universe) where

open import UF-Subsingletons hiding (⊥)

𝓕 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
𝓕 X = Σ \(I : 𝓣 ̇) → (I → X)

source : {X : 𝓤 ̇} → 𝓕 X → 𝓣 ̇
source (I , φ) = I


family : {X : 𝓤 ̇} (l : 𝓕  X) → source l → X
family (I , φ) = φ

η : {X : 𝓤 ̇} → X → 𝓕 X
η x = 𝟙 , (λ _ → x)

\end{code}
