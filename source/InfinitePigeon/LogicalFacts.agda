-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.LogicalFacts where

infixl 30 _∘_

open import InfinitePigeon.Logic

_∘_ : {A B : Ω} {C : B → Ω} →
      (∀(b : B) → C b) → ∀(f : A → B) → ∀(a : A) → C(f a)

g ∘ f = λ x → g(f x)


id : {A : Ω} → A → A
id x = x


uncurry : {A B C : Ω} →
  (A → B → C) → A ∧ B → C

uncurry f (∧-intro a b) = f a b


curry : {A B C : Ω} →
  (A ∧ B → C) → A → B → C

curry f a b = f(∧-intro a b)


double-negation-intro : {R A : Ω} →
 A → ((A → R) → R)

double-negation-intro a p = p a


contra-positive : {R A B : Ω} →
 (A → B) → (B → R) → (A → R)

contra-positive f p = p ∘ f


three-negations-imply-one : {R A : Ω} →
  (((A → R) → R) → R) → (A → R)

three-negations-imply-one = contra-positive double-negation-intro


not-exists-implies-forall-not : {R : Ω} → {X : Set} → {A : X → Ω} →
 ((∃ \(x : X) → A x) → R) → ∀(x : X) → A x → R

not-exists-implies-forall-not f x a = f(∃-intro x a)


forall-not-implies-not-exists : {R : Ω} → {X : Set} → {A : X → Ω} →
 (∀(x : X) → A x → R) → (∃ \(x : X) → A x) → R

forall-not-implies-not-exists f (∃-intro x a) = f x a


∃-functor : {X : Set} {A B : X → Ω} →
 ({x : X} → A x → B x) →
 (∃ \(x : X) → A x) →  ∃ \(x : X) → B x

∃-functor f (∃-intro x a) = ∃-intro x (f a)


∃-nested-functor : {X Y : Set} {A B : X → Y → Ω} →
 ({x : X} → {y : Y} → A x y → B x y) →
 (∃ \(x : X) → ∃ \(y : Y) → A x y) →  ∃ \(x : X) → ∃ \(y : Y) → B x y

∃-nested-functor f = ∃-functor (λ a → ∃-functor f a)
