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

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

\end{code}

We use the following to indicate the type of a subterm (where "∶"
(typed "\:" in emacs) is not the same as ":":

\begin{code}

-id : (X : 𝓤 ̇ ) → X → X
-id X x = x

syntax -id X x = x ∶ X

\end{code}

And the following to make explicit the type of hypotheses:

\begin{code}

need_which-is-given-by_ : (A : 𝓤 ̇ ) → A → A
need A which-is-given-by a = a

have_so_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a so b = b

have_so-use_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a so-use b = b

apply_to_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → A → B
apply f to a = f a

have_so-apply_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → (A → B) → B
have a so-apply f = f a

-assume : (A : 𝓤 ̇ ) {B : 𝓥 ̇ } → (A → B) → A → B
-assume A f = f

syntax -assume A (λ x → b) = assume x ∶ A then b

infixr 100 -assume

\end{code}

Get rid of this:

\begin{code}

Σ! : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Σ! {𝓤} {𝓥} {X} A = (Σ \(x : X) → A x) × ((x x' : X) → A x → A x' → x ≡ x')

\end{code}

Note: Σ! is to be avoided, in favour of the contractibility of Σ,
following univalent mathematics.

I am not sure where to put this, so it goes here for the moment:

\begin{code}

left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

left-cancellable' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable' f = ∀ x x' → f x ≡ f x' → x ≡ x'

\end{code}

Fixities:

\begin{code}

infixl -1 -id
infix -1 _⇔_

\end{code}
