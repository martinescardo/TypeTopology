\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module MoreTypes where

open import SpartanMLTT

open import Universes

data Maybe {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ̇ where
 Nothing : Maybe A
 Just    : A → Maybe A

Just-is-not-Nothing : {A : 𝓤 ̇ } {a : A} → Just a ≢ Nothing
Just-is-not-Nothing ()

Nothing-is-isolated : {A : 𝓤 ̇ } (x : Maybe A) → decidable (Nothing ≡ x)
Nothing-is-isolated Nothing  = inl refl
Nothing-is-isolated (Just a) = inr (λ (p : Nothing ≡ Just a) → Just-is-not-Nothing (p ⁻¹))

Nothing-is-isolated' : {A : 𝓤 ̇ } (x : Maybe A) → decidable (x ≡ Nothing)
Nothing-is-isolated' Nothing  = inl refl
Nothing-is-isolated' (Just a) = inr Just-is-not-Nothing

open import UF-Miscelanea
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Subsingletons

Nothing-is-h-isolated : {A : 𝓤 ̇ } (x : Maybe A) → is-prop (Nothing ≡ x)
Nothing-is-h-isolated x = isolated-is-h-isolated Nothing Nothing-is-isolated

Nothing-is-h-isolated' : {A : 𝓤 ̇ } (x : Maybe A) → is-prop (x ≡ Nothing)
Nothing-is-h-isolated' x = equiv-to-prop ≡-flip (Nothing-is-h-isolated x)

data Bool : 𝓤₀ ̇ where
 true false : Bool

_||_ _&&_ : Bool → Bool → Bool


if_then_else_ : {X : 𝓤 ̇ } → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

Bool-induction : {A : Bool → 𝓤 ̇ } → A true → A false → (b : Bool) → A b
Bool-induction x y true  = x
Bool-induction x y false = y

true  || y = true
false || y = y

true  && y = y
false && y = false

infixl 10 _||_
infixl 20 _&&_

data List {𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ̇ where
 []  : List X
 _∷_ : X → List X → List X

_++_ : {𝓤 : Universe} {X : 𝓤 ̇ } → List X → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

empty : {𝓤 : Universe} {X : 𝓤 ̇ } → List X → Bool
empty []       = true
empty (x ∷ xs) = false

\end{code}
