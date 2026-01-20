Martin Escardo, Paulo Oliva, 2024

The list monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MonadOnTypesLSU.List where

open import MonadOnTypesLSU.Construction
open import MLTT.Spartan hiding (J)
open import MLTT.List hiding (map)

𝕃 : Monad
𝕃 = record {
 functor = List ;
 η       = [_] ;
 ext     = List-ext ;
 ext-η   = concat-singletons ;
 unit    = List-ext-unit ;
 assoc   = List-ext-assoc
 }

module List-definitions where

 _⊗ᴸ_ : {X : Type} {Y : X → Type}
      → List X
      → ((x : X) → List (Y x))
      → List (Σ x ꞉ X , Y x)
 _⊗ᴸ_ = _⊗_ 𝕃

 ηᴸ : {X : Type} → X → List X
 ηᴸ = η 𝕃

 extᴸ : {X Y : Type} → (X → List Y) → List X → List Y
 extᴸ = ext 𝕃

 mapᴸ : {X Y : Type} → (X → Y) → List X → List Y
 mapᴸ = map 𝕃

\end{code}
