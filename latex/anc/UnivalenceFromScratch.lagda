Martin Escardo, 28 February 2018.

    ---------------------------------------------------
    A self-contained, brief and complete formulation of
    Voevodsky's Univalence Axiom
    ---------------------------------------------------

A 9-page verbal explanation is available at
http://www.cs.bham.ac.uk/~mhe/agda-new/UnivalenceFromScratch.pdf

This file type checks in Agda 2.6.0.

\begin{code}

{-# OPTIONS --without-K #-}

module UnivalenceFromScratch where

open import Agda.Primitive using (_⊔_) renaming (lzero to U₀ ; lsuc to _′ ; Level to Universe)

_̇ : (U : Universe) → _
U ̇ = Set U

infix  0 _̇

data Σ {U V : Universe} {X : U ̇} (Y : X → V ̇) : U ⊔ V ̇ where
  _,_ : (x : X) (y : Y x) → Σ Y

data Id {U : Universe} {X : U ̇} : X → X → U ̇ where
  refl : (x : X) → Id x x

J : {U V : Universe} {X : U ̇}
  → (A : (x y : X) → Id x y → V ̇)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : Id x y) → A x y p
J A f x x (refl x) = f x

isSingleton : {U : Universe} → U ̇ → U ̇
isSingleton X = Σ \(c : X) → (x : X) → Id c x

fiber : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → Y → U ⊔ V ̇
fiber f y = Σ \x → Id (f x) y

isEquiv : {U V : Universe} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
isEquiv f = (y : _) → isSingleton(fiber f y)

Eq : {U V : Universe} → U ̇ → V ̇ → U ⊔ V ̇
Eq X Y = Σ \(f : X → Y) → isEquiv f

singletonType : {U : Universe} {X : U ̇} → X → U ̇
singletonType x = Σ \y → Id y x

η : {U : Universe} {X : U ̇} (x : X) → singletonType x
η x = (x , refl x)

singletonTypesAreSingletons : {U : Universe} {X : U ̇} (x : X) → isSingleton(singletonType x)
singletonTypesAreSingletons {U} {X} = h
 where
  A : (y x : X) → Id y x → U ̇
  A y x p = Id (η x) (y , p)
  f : (x : X) → A x x (refl x)
  f x = refl (η x)
  φ : (y x : X) (p : Id y x) → Id (η x) (y , p)
  φ = J A f
  g : (x : X) (σ : singletonType x) → Id (η x) σ
  g x (y , p) = φ y x p
  h : (x : X) → Σ \(c : singletonType x) → (σ : singletonType x) → Id c σ
  h x = (η x , g x)

id : {U : Universe} (X : U ̇) → X → X
id X x = x

idIsEquiv : {U : Universe} (X : U ̇) → isEquiv(id X)
idIsEquiv X = g
 where
  g : (x : X) → isSingleton (fiber (id X) x)
  g = singletonTypesAreSingletons

IdToEq : {U : Universe} (X Y : U ̇) → Id X Y → Eq X Y
IdToEq {U} = J A f
 where
  A : (X Y : U ̇) → Id X Y → U ̇
  A X Y p = Eq X Y
  f : (X : U ̇) → A X X (refl X)
  f X = (id X , idIsEquiv X)

isUnivalent : (U : Universe) → U ′ ̇
isUnivalent U = (X Y : U ̇) → isEquiv(IdToEq X Y)

\end{code}

The univalence axiom for the universe U postulates an inhabitant of
the type `isUnivalent U`. Alternatively, `isUnivalent U` can be used
as an explicit hypothesis.
