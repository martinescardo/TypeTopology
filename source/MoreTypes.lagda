\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MoreTypes where

open import Universes

data Maybe {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ̇ where
 Nothing : Maybe A
 Just    : A → Maybe A

data Bool : 𝓤₀ ̇ where
 true false : Bool

data List {𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 []  : List X
 _∷_ : X → List X → List X

\end{code}
