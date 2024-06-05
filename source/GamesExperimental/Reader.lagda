Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

open import MLTT.Spartan hiding (J)

module GamesExperimental.Reader where

open import GamesExperimental.Monad

Reader : {𝓦₀ : Universe} → 𝓦₀ ̇  → Monad
Reader {𝓦₀} A = record {
            ℓ       = λ 𝓤 → 𝓤 ⊔ 𝓦₀ ;
            functor = λ X → A → X ;
            η       = λ x _ → x ;
            ext     = λ f ρ a → f (ρ a) a ;
            ext-η   = λ x → refl ;
            unit    = λ f x → refl ;
            assoc   = λ g f x → refl
           }

\end{code}
