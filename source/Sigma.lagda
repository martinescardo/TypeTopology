Martin Escardo

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

record Σ {U V} {X : U ̇} (Y : X → V ̇) : U ⊔ V ̇ where
  constructor _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

open Σ public

syntax Σ {A} (λ x → B) = Σ（ x ∶ A ） B

Σ-elim : ∀ {U V} {X : U ̇} {Y : X → V ̇} {A : Σ Y → U ⊔ V ̇}
       → ((x : X) (y : Y x) → A (x , y)) → (σ : Σ Y) → A σ
Σ-elim f (x , y) = f x y

uncurry : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {Z : W ̇}
        → ((x : X) → Y x → Z) → Σ Y → Z
uncurry f (x , y) = f x y

curry :  ∀ {U V W} {X : U ̇} {Y : X → V ̇} {Z : W ̇}
      → (Σ Y → Z) → ((x : X) → Y x → Z)
curry f x y = f (x , y)

\end{code}

Equivalently, Σ-elim f t = f (pr₁ t) (pr₂ t).

As usual in type theory, binary products are particular cases of
dependent sums.

\begin{code}

_×_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
X × Y = Σ \(x : X) → Y

\end{code}

Fixities:

\begin{code}

infixr 4 _,_
infixr 2 _×_

\end{code}
