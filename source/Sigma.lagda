\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Sigma where

open import Universes

\end{code}

Using our conventions below, a sum can be written Σ {X} Y or as
Σ \(x : X) → Y x, or even Σ \x → Y x when Agda can infer the type of
the element x from the context. I prefer to use \ rather than λ in
such cases.

\begin{code}

record Σ {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

open Σ public

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y

uncurry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇} {Z : 𝓦 ̇}
        → ((x : X) → Y x → Z) → Σ Y → Z
uncurry f (x , y) = f x y

curry :  {X : 𝓤 ̇ } {Y : X → 𝓥 ̇} {Z : 𝓦 ̇}
      → (Σ Y → Z) → ((x : X) → Y x → Z)
curry f x y = f (x , y)

\end{code}

As usual in type theory, binary products are particular cases of
dependent sums.


Fixities:

\begin{code}

infixr 4 _,_
infixr 2 _×_

\end{code}

Not used anymore, kept just in case we change our minds:

  syntax Σ {A} (λ x → B) = Σ（ x ∶ A ） B
