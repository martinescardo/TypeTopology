Martin Escardo, Paulo Oliva, originally 2023, with universes
generalized in March 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)

module MonadOnTypes.JK (R : 𝓦₀ ̇ ) where

open import MonadOnTypes.J
open import MonadOnTypes.K

open J-definitions R
open K-definitions R

overline : {X : 𝓤 ̇ } → J X → K X
overline ε = λ p → p (ε p)

overline-theorem : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                   (ε : J X) (δ : (x : X) → J (Y x))
                 → overline (ε ⊗ᴶ δ) ∼ overline ε ⊗ᴷ (λ x → overline (δ x))
overline-theorem ε δ q = refl

_attains_ : {X : 𝓤 ̇ } → J X → K X → 𝓦₀ ⊔ 𝓤 ̇
ε attains ϕ = overline ε ∼ ϕ

is-attainable : {X : 𝓤 ̇ } → K X → 𝓦₀ ⊔ 𝓤 ̇
is-attainable {𝓤} {X} ϕ = Σ ε ꞉ J X , (ε attains ϕ)

\end{code}

Notice that attainability is data in general, rather than property, as a quantifier can have many selection functions.

TODO. Show that overline is a monad morphism.

TODO. Define also the above for the J and K monad transformers, maybe
in this file, maybe in another file.
