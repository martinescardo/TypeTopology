Identity type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Id where

open import Universes
open import Pi

open import Identity-Type renaming (_≡_ to infix 0 _≡_) public

𝓻𝓮𝒻𝓵 : {X : 𝓤 ̇ } (x : X) → x ≡ x
𝓻𝓮𝒻𝓵 x = refl {_} {_} {x}

by-definition : {X : 𝓤 ̇ } {x : X} → x ≡ x
by-definition = refl

by-construction : {X : 𝓤 ̇ } {x : X} → x ≡ x
by-construction = refl

by-assumption : {X : 𝓤 ̇ } {x : X} → x ≡ x
by-assumption = refl

lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

Id : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
Id = _≡_

Jbased : {X : 𝓤 ̇ } (x : X) (A : (y : X) → x ≡ y → 𝓥 ̇ )
       → A x refl → (y : X) (r : x ≡ y) → A y r
Jbased x A b .x refl = b

J : {X : 𝓤 ̇ } (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x refl) → {x y : X} (r : x ≡ y) → A x y r
J A f {x} {y} = Jbased x (A x) (f x) y


private

 transport' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
            → x ≡ y → A x → A y
 transport' A {x} {y} p a = Jbased x (λ y p → A y) a y p


transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A refl = id

_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p refl

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p refl

transport⁻¹ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} → x ≡ y → A y → A x
transport⁻¹ B p = transport B (p ⁻¹)

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → A x) → ((x : X) → A x) → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
_∎ _ = refl

\end{code}

Fixities:

\begin{code}

infix  3  _⁻¹
infix  1 _∎
infixr 0 _≡⟨_⟩_
infixl 2 _∙_
infix  4  _∼_

\end{code}
