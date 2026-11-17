Theo Hepburn, started October 2024.

Contains a formalisation of the `Thunk` type proposed by Nils Anders Danielsson.
This is a monad used to keep track of the number of steps used to construct a
type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TGH.Thunk where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Addition

infixl 1 _>>=_
infix 0 √_

data Thunk' (X : 𝓤₀ ̇) : ℕ → 𝓤₀ ̇ where
 return : X → Thunk' X 0
 √_     : {n : ℕ} → Thunk' X n → Thunk' X (succ n)

Thunk : ℕ → 𝓤₀ ̇ → 𝓤₀ ̇
Thunk n X = Thunk' X n

force : {n : ℕ} {X : 𝓤₀ ̇} → Thunk n X → X
force (return x) = x
force (√ x)      = force x

_>>=_ : {n₁ n₂ : ℕ} {X Y : 𝓤₀ ̇}
      → Thunk n₁ X → (X → Thunk n₂ Y) → Thunk (n₂ + n₁) Y
return x >>= f = f x
(√ x)    >>= f = √ (x >>= f)

\end{code}
