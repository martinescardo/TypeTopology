Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan hiding (J)

module Games.K where

open import Games.Monad

𝕂 : Type → Monad
𝕂 R = record {
       functor = λ X → (X → R) → R ;
       η       = λ x p → p x ;
       ext     = λ f ϕ p → ϕ (λ x → f x p) ;
       ext-η   = λ x → refl ;
       unit    = λ f x → refl ;
       assoc   = λ g f x → refl
      }

\end{code}
