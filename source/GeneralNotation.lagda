General notation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module GeneralNotation where

open import Sigma
open import Universes
open import Id
open import Negation public

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ⇔ B = (A → B) × (B → A)

\end{code}

This is to avoid naming implicit arguments:

\begin{code}

type-of : {X : 𝓤 ̇} → X → 𝓤 ̇
type-of {𝓤} {X} x = X

\end{code}

We use the following to indicate the type of a subterm:

\begin{code}

-id : (X : 𝓤 ̇ ) → X → X
-id X x = x

syntax -id X x = x ∶ X

\end{code}

And the following to make explicit the type of hypotheses:

\begin{code}

have : {A : 𝓤 ̇} {B : 𝓥 ̇} → A → B → B
have _ y = y

\end{code}

Get rid of this:

\begin{code}

Σ! : {X : 𝓤 ̇} (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Σ! {𝓤} {𝓥} {X} A = (Σ \(x : X) → A x) × ((x x' : X) → A x → A x' → x ≡ x')

\end{code}

Note: Σ! is to be avoided, in favour of the contractibility of Σ,
following univalent mathematics.

Fixities:

\begin{code}

infix 0 -id
infix  -1 _⇔_

\end{code}
