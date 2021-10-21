\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MoreTypes where

open import SpartanMLTT

open import Universes

data Maybe {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ̇ where
 Nothing : Maybe A
 Just    : A → Maybe A

Just-is-not-Nothing : {A : 𝓤 ̇ } {a : A} → Just a ≢ Nothing
Just-is-not-Nothing ()

data Bool : 𝓤₀ ̇ where
 true false : Bool

_||_ _&&_ : Bool → Bool → Bool

true  || y = true
false || y = y

true  && y = y
false && y = false

infixl 10 _||_
infixl 20 _&&_

data List {𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 []  : List X
 _∷_ : X → List X → List X

\end{code}
