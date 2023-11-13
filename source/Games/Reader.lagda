Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.Reader where

open import Games.Monad

Reader : Type → Monad
Reader A = record {
            functor = λ X → A → X ;
            η     = λ x _ → x ;
            ext   = λ f ρ a → f (ρ a) a ;
            ext-η = λ x → refl ;
            unit  = λ f x → refl ;
            assoc = λ g f x → refl
           }

\end{code}
