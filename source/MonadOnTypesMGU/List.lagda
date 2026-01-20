Martin Escardo, Paulo Oliva, 2024

The list monad.

Generalized universes Jan 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MonadOnTypesMGU.List where

open import MonadOnTypesMGU.Construction
open import MLTT.Spartan hiding (J)
open import MLTT.List hiding (map)

𝕃 : Monad {λ 𝓤 → 𝓤}
𝕃 = record {
 functor = List ;
 η       = [_] ;
 ext     = List-ext ;
 ext-η   = concat-singletons ;
 unit    = List-ext-unit ;
 assoc   = List-ext-assoc
 }

module List-definitions where

 _⊗ᴸ_ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
      → List X
      → ((x : X) → List (Y x))
      → List (Σ x ꞉ X , Y x)
 _⊗ᴸ_ = _⊗_ 𝕃

 ηᴸ : {X : 𝓤 ̇ } → X → List X
 ηᴸ = η 𝕃

 extᴸ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → List Y) → List X → List Y
 extᴸ = ext 𝕃

 mapᴸ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → List X → List Y
 mapᴸ = map 𝕃

\end{code}
