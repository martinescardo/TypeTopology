Martin Escardo, Paulo Oliva, originally 2023, with universes
generalized in March 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypesMGU.Reader where

open import MonadOnTypesMGU.Monad

Reader : {𝓦₀ : Universe} → 𝓦₀ ̇ → Monad {λ 𝓤 → 𝓦₀ ⊔ 𝓤}
Reader {𝓦₀} A = record {
            functor = λ X → A → X ;
            η       = λ x _ → x ;
            ext     = λ f ρ a → f (ρ a) a ;
            ext-η   = λ x → refl ;
            unit    = λ f x → refl ;
            assoc   = λ g f x → refl
          }

\end{code}
