Martin Escardo 7th December 2022

Type-class for notation for _+_.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module PlusNotation where

open import Universes

record Plus {𝓤} {𝓥} {𝓦} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : (𝓤 ⊔ 𝓥 ⊔ 𝓦)⁺ ̇  where
 field
   _∔_ : X → Y → 𝓦  ̇

 infixl 31 _∔_

open Plus {{...}} public


\end{code}
