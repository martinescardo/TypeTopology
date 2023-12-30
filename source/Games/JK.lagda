Martin Escardo, Paulo Oliva, 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module Games.JK where

open import UF.FunExt
open import Games.Monad
open import Games.J
open import Games.K

module JK (R : Type) where

 open J-definitions R
 open K-definitions R

 overline : {X : Type} → J X → K X
 overline ε = λ p → p (ε p)

 overline-theorem : {X : Type} {Y : X → Type}
                    (ε : J X) (δ : (x : X) → J (Y x))
                  → overline (ε ⊗ᴶ δ) ∼ overline ε ⊗ᴷ (λ x → overline (δ x))
 overline-theorem ε δ q = refl

 _attains_ : {X : Type} → J X → K X → Type
 ε attains ϕ = overline ε ∼ ϕ

\end{code}

TODO. Show that overline is a monad morphism.

TODO. Define also the above for the J and K monad transformers, maybe
in this file, maybe in another file.
