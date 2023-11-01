Pi types.

Built-in, with the notation (x : X) → A x for Π A.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Pi where

open import MLTT.Universes

Π : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

\end{code}

We often write Π x ꞉ X , A x for Π A to make X explicit.

\begin{code}

Pi : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Pi X Y = Π Y

syntax Pi A (λ x → b) = Π x ꞉ A , b

infixr -1 Pi

id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y) (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

S-combinator : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {Z : (x : X) → Y x → 𝓦 ̇ }
             → ((x : X) (y : Y x) → Z x y)
             → (f : (x : X) → Y x) (x : X) → Z x (f x)
S-combinator g f = λ x → g x (f x)

\end{code}

The domain and codomain of a function, mainly to avoid implicit
arguments:

\begin{code}

domain : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Π Y → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

\end{code}

Fixities:

\begin{code}

infixl 5 _∘_

\end{code}
