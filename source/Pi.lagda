Pi types.

Built-in, with the notation (x : X) → A x for Π A.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Pi where

open import Universes

Π : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} Y = (x : X) → Y x

\end{code}

We often write Π \(x : X) → A x for Π A to make X explicit.

Not used any more, but kept here in a comment just in case we change
our mind:

syntax Π {A} (λ x → B) = Π（ x ∶ A ） B

\begin{code}

id : {X : 𝓤 ̇ } → X → X
id x = x

id─ : (X : 𝓤 ̇ ) → X → X
id─ X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
    → ((y : Y) → Z y)
    → (f : X → Y) (x : X) → Z (f x)
g ∘ f = λ x → g(f x)

\end{code}

The domain and codomain of a function, mainly to avoid implicit
arguments:

\begin{code}

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

\end{code}


Fixities:

\begin{code}

infixl 5 _∘_

\end{code}
