\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Plus-Type where

open import Universes public

data _⊎_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X ⊎ Y
 inr : Y → X ⊎ Y

open import PlusNotation public

module _ {𝓤 𝓥 : Universe} where

 instance
  coproduct : Plus (𝓤 ̇ ) (𝓥 ̇ )
  _+_ {{coproduct}} = _⊎_

infixr 1 _⊎_

\end{code}
