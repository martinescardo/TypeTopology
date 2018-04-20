Martin Escardo 2011.

Our Spartan (intensional) Martin-Löf type theory has a countable tower
of universes, the empty type ∅, the unit type 𝟙, product types Π, sum
types Σ (and hence binary product types _×_), sum types _+_.
identity types _≡_.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SpartanMLTT where

open import Agda.Primitive using (_⊔_) renaming (lzero to U₀ ; lsuc to _′ ; Level to Universe) public

_̇ : (U : Universe) → _
U ̇ = Set U -- This should be the only use of the Agda keyword 'Set' in this development.

U₁ = U₀ ′
U₂ = U₁ ′

\end{code}

For example, we write the following instead of 

    Π : ∀ {i j} {X : Set i} → (Y : X → Set j) → Set (i ⊔ j)
    Π Y = (x : _) → Y x

\begin{code}

Π : ∀ {U V} {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
Π Y = (x : _) → Y x
 
\end{code}

Identity and dependent function composition:

\begin{code}

id : ∀ {U} {X : U ̇} → X → X
id x = x

_∘_ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : Y → W ̇}
    → Π Z → (f : X → Y) → Π (λ x → Z (f x))
g ∘ f = λ x → g(f x)

\end{code}

Empty type.

\begin{code}

data 𝟘 : U₀ ̇ where

unique-from-𝟘 : ∀ {U} {A : U ̇} → 𝟘 → A
unique-from-𝟘 = λ ()

𝟘-elim = unique-from-𝟘

\end{code}

The one-element type is defined by induction with one case:

\begin{code}

data 𝟙 : U₀ ̇ where
 * : 𝟙 

unique-to-𝟙 : ∀ {U} {A : U ̇} → A → 𝟙
unique-to-𝟙 a = *

\end{code}

Using our conventions below, a sum can be written Σ {X} Y or as
Σ \(x : X) → Y x, or even Σ \x → Y x when Agda can infer the type of
the element x from the context. I prefer to use \ rather than λ in
such cases.

\begin{code}

record Σ {U V : Universe} {X : U ̇} (Y : X → V ̇) : U ⊔ V ̇ where
  constructor _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

open Σ public

Σ-elim : ∀ {U V} {X : U ̇} {Y : X → V ̇} {A : Σ Y → U ⊔ V ̇}
       → ((x : X) (y : Y x) → A (x , y)) → Π A
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

Binary sums

\begin{code}

data _+_ {U V : Universe} (X : U ̇) (Y : V ̇) : U ⊔ V ̇ where
  inl : X → X + Y
  inr : Y → X + Y

dep-cases : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : X + Y → W ̇}
          → ((x : X) → A(inl x))
          → ((y : Y) → A(inr y))
          → ((z : X + Y) → A z)
dep-cases f g (inl x) = f x
dep-cases f g (inr y) = g y

cases : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} → (X → A) → (Y → A) → X + Y → A
cases = dep-cases

+-commutative : ∀ {U V} {A : U ̇} {B : V ̇} → A + B → B + A
+-commutative = cases inr inl

\end{code}

Some basic Curry--Howard logic. 

\begin{code}

_⇔_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
A ⇔ B = (A → B) × (B → A)

¬_ : ∀ {U}→ U ̇ → U ̇
¬ A = A → 𝟘

dual : ∀ {U V W} {X : U ̇} {Y : V ̇} (R : W ̇) → (X → Y) → (Y → R) → (X → R)
dual R f p = p ∘ f

contrapositive : ∀ {U V} {A : U ̇} {B : V ̇} → (A → B) → ¬ B → ¬ A
contrapositive = dual _

¬¬ : ∀ {U} → U ̇ → U ̇
¬¬ A = ¬(¬ A)

¬¬-functor : ∀ {U V} {A : U ̇} {B : V ̇} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = contrapositive ∘ contrapositive

double-negation-intro : ∀ {U} {A : U ̇} → A → ¬¬ A
double-negation-intro x u = u x

three-negations-imply-one : ∀ {U} {A : U ̇} → ¬(¬¬ A) → ¬ A
three-negations-imply-one = contrapositive double-negation-intro

double-negation-unshift : ∀ {U V} {X : U ̇} {A : X → V ̇} → ¬¬((x : X) → A x) → (x : X) → ¬¬(A x)
double-negation-unshift f x g = f (λ h → g (h x))

dnu : ∀ {U} {V} {A : U ̇} {B : V ̇} → ¬¬(A × B) → ¬¬ A × ¬¬ B
dnu φ = (¬¬-functor pr₁ φ) , (¬¬-functor pr₂ φ)

und : ∀ {U} {V} {A : U ̇} {B : V ̇} → ¬¬ A × ¬¬ B → ¬¬(A × B)
und (φ , γ) w = γ (λ y → φ (λ x → w (x , y))) 

not-Σ-implies-Π-not : ∀ {U V} {X : U ̇} {A : X → V ̇}
                    → ¬(Σ \(x : X) → A x) → (x : X) → ¬(A x)
not-Σ-implies-Π-not = curry

Π-not-implies-not-Σ : ∀ {U} {X : U ̇} {A : X → U ̇}
                    → ((x : X) → ¬(A x)) → ¬(Σ \(x : X) → A x)
Π-not-implies-not-Σ = uncurry

Left-fails-then-right-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → P + Q → ¬ P → Q
Left-fails-then-right-holds (inl p) u = 𝟘-elim (u p)
Left-fails-then-right-holds (inr q) u = q

Right-fails-then-left-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → P + Q → ¬ Q → P
Right-fails-then-left-holds (inl p) u = p
Right-fails-then-left-holds (inr q) u = 𝟘-elim (u q)

\end{code}

Equality (more in the module UF).

\begin{code}

data _≡_ {U : Universe} {X : U ̇} : X → X → U ̇ where
  refl : {x : X} → x ≡ x

Id : ∀ {U} {X : U ̇} → X → X → U ̇
Id = _≡_

_≢_ : ∀ {U} {X : U ̇} → (x y : X) → U ̇
x ≢ y = x ≡ y → 𝟘

Jbased : ∀ {U V} {X : U ̇} (x : X) (A : (y : X) → x ≡ y → V ̇)
       → A x refl → (y : X) (r : x ≡ y) → A y r
Jbased x A b .x refl = b

J : ∀ {U V} {X : U ̇} (A : (x y : X) → x ≡ y → V ̇)
  → ((x : X) → A x x refl) → {x y : X} (r : x ≡ y) → A x y r
J A f {x} {y} = Jbased x (λ y p → A x y p) (f x) y

transport' : ∀ {U V} {X : U ̇} (A : X → V ̇) {x y : X}
          → x ≡ y → A x → A y
transport' A {x} {y} p a = Jbased x (λ y p → A y) a y p

transport : ∀ {U V} {X : U ̇} (A : X → V ̇) {x y : X}
          → x ≡ y → A x → A y
transport A refl = id

_∙_ : ∀ {U} {X : U ̇} → {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (Id _) q p

_⁻¹ : ∀ {U} {X : U ̇} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (λ x → x ≡ _) p refl

ap : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ x' → f _ ≡ f x') p refl

back-transport : ∀ {U V} {X : U ̇} (A : X → V ̇) {x y : X} → x ≡ y → A y → A x
back-transport B p = transport B (p ⁻¹)

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_≡⟨_⟩_ : ∀ {U} {X : U ̇} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : ∀ {U} {X : U ̇} → (x : X) → x ≡ x
_∎ _ = refl

\end{code}

The following is properly proved using universes, but we don't both at
the moment:

\begin{code}

sum-disjoint : ∀ {U V} {X : U ̇} {Y : V ̇} {x : X} {y : Y} → inl x ≡ inr y → 𝟘
sum-disjoint ()

\end{code}

\begin{code}

𝟙-all-* : (x : 𝟙) → x ≡ *
𝟙-all-* * = refl 

\end{code}

General utilities to avoid (sometimes) mentionint implicit arguments
in function definitions.

\begin{code}

typeOf : ∀ {U} {X : U ̇} → X → U ̇
typeOf {U} {X} x = X

universeOf : ∀ {U} (X : U ̇) → Universe
universeOf {U} X = U

domain : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ̇
domain {U} {V} {X} {Y} f = X

codomain : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → V ̇
codomain {U} {V} {X} {Y} f = Y

\end{code}

Operator fixity and precedences.

\begin{code}

infix  0 _̇
infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_ 
infix  50 ¬_
infix  -1 _⇔_
infix  0 _≡_
infix  0 _≢_
infix  3  _⁻¹
infix  1 _∎
infixr 0 _≡⟨_⟩_ 
infixl 2 _∙_

\end{code}
