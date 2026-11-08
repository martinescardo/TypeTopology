Martin Escardo, original date unknown.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Sigma where

open import MLTT.Universes

\end{code}

Using our conventions below, a sum can be written Σ {X} Y or as
Σ x ꞉ X , Y x, or even Σ λ x → Y x when Agda can infer the type of
the element x from the context. I prefer to use \ rather than λ in
such cases.

\begin{code}

open import MLTT.Sigma-Type renaming (_,_ to infixr 4 _,_) public

open Σ public

Sigma : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Sigma _ Y = Σ Y

syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infixr -1 Sigma

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

uncurry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : 𝓦 ̇ }
        → ((x : X) → Y x → Z) → Σ Y → Z
uncurry f (x , y) = f x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : 𝓦 ̇ }
      → (Σ Y → Z) → ((x : X) → Y x → Z)
curry f x y = f (x , y)

×functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
         → (X → A) → (Y → B) → X × Y → A × B
×functor f g (x , y) = f x , g y

\end{code}

As usual in type theory, binary products are particular cases of
dependent sums.


Fixities:

\begin{code}

infixr 2 _×_

\end{code}
