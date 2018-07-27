Martin Escardo 2011.

Our Spartan (intensional) Martin-Löf type theory has a countable tower
of universes, the empty type ∅, the unit type 𝟙, product types Π, sum
types Σ (and hence binary product types _×_), sum types _+_.
identity types _≡_.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SpartanMLTT where

open import Universes public

\end{code}

The module Universes allows us to write e.g. the following instead of

    Π : ∀ {i j} {X : Set i} (Y : X → Set j) → Set (i ⊔ j)
    Π Y = (x : _) → Y x

\begin{code}

Π : ∀ {U V} {X : U ̇} (Y : X → V ̇) → U ⊔ V ̇
Π Y = (x : _) → Y x

syntax Π {A} (λ x → B) = Π（ x ∶ A ）, B

\end{code}

Identity and dependent function composition:

\begin{code}

id : ∀ {U} {X : U ̇} → X → X
id x = x

_∘_ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : Y → W ̇}
    → ((y : Y) → Z y) → (f : X → Y) → (x : X) → Z (f x)
g ∘ f = λ x → g(f x)

\end{code}

xsEmpty type.

\begin{code}

data 𝟘 {U} : U ̇ where

unique-from-𝟘 : ∀ {U V} {A : U ̇} → 𝟘 {V} → A
unique-from-𝟘 = λ ()

𝟘-elim = unique-from-𝟘

\end{code}

The one-element type is defined by induction with one case:

\begin{code}

data 𝟙 {U} : U ̇ where
 * : 𝟙

unique-to-𝟙 : ∀ {U V} {A : U ̇} → A → 𝟙 {V}
unique-to-𝟙 {U} {V} a = * {V}

\end{code}

Using our conventions below, a sum can be written Σ {X} Y or as
Σ \(x : X) → Y x, or even Σ \x → Y x when Agda can infer the type of
the element x from the context. I prefer to use \ rather than λ in
such cases.

\begin{code}

record Σ {U V} {X : U ̇} (Y : X → V ̇) : U ⊔ V ̇ where
  constructor _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

open Σ public

syntax Σ {A} (λ x → B) = Σ（ x ∶ A ）, B

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

data _+_ {U V} (X : U ̇) (Y : V ̇) : U ⊔ V ̇ where
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

Cases : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} → X + Y → (X → A) → (Y → A) → A
Cases z f g = cases f g z

+-commutative : ∀ {U V} {A : U ̇} {B : V ̇} → A + B → B + A
+-commutative = cases inr inl

\end{code}

Some basic Curry--Howard logic.

\begin{code}

¬_ : ∀ {U} → U ̇ → U ̇
¬ A = A → 𝟘 {U₀}

is-empty : ∀ {U} → U ̇ → U ̇
is-empty = ¬_

decidable : ∀ {U} → U ̇ → U ̇
decidable A = A + ¬ A

_⇔_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
A ⇔ B = (A → B) × (B → A)

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

data _≡_ {U} {X : U ̇} : X → X → U ̇ where
  refl : {x : X} → x ≡ x

lhs : ∀ {U} {X : U ̇} {x y : X} → x ≡ y → X
lhs {U} {X} {x} {y} p = x

rhs : ∀ {U} {X : U ̇} {x y : X} → x ≡ y → X
rhs {U} {X} {x} {y} p = y

Id : ∀ {U} {X : U ̇} → X → X → U ̇
Id = _≡_

_≢_ : ∀ {U} {X : U ̇} → (x y : X) → U ̇
x ≢ y = ¬(x ≡ y)

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
p ∙ q = transport (Id (lhs p)) q p

_⁻¹ : ∀ {U} {X : U ̇} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (λ - → - ≡ lhs p) p refl

ap : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p refl

back-transport : ∀ {U V} {X : U ̇} (A : X → V ̇) {x y : X} → x ≡ y → A y → A x
back-transport B p = transport B (p ⁻¹)

≢-sym : ∀ {U} {X : U ̇} → {x y : X} → x ≢ y → y ≢ x
≢-sym u r = u(r ⁻¹)

\end{code}

Some general definitions (perhaps we need to find a better place for
this):

\begin{code}

Nat : ∀ {U V W} {X : U ̇} → (X → V ̇) → (X → W ̇) → U ⊔ V ⊔ W ̇
Nat A B = Π \x → A x → B x

_∼_ : ∀ {U V} {X : U ̇} {A : X → V ̇} → Π A → Π A → U ⊔ V ̇
f ∼ g = ∀ x → f x ≡ g x

_≈_ : ∀ {U V} {X : U ̇} {x : X} {A : X → V ̇} → Nat (Id x) A → Nat (Id x) A → U ⊔ V ̇
η ≈ θ = ∀ y → η y ∼ θ y

NatΣ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Σ A → Σ B
NatΣ ζ (x , a) = (x , ζ x a)

NatΠ : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} → Nat A B → Π A → Π B
NatΠ f g x = f x (g x) -- (S combinator from combinatory logic!)

left-cancellable : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable f = ∀ {x x'} → f x ≡ f x' → x ≡ x'

left-cancellable' : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
left-cancellable' f = ∀ x x' → f x ≡ f x' → x ≡ x'

Σ! : ∀ {U V} {X : U ̇} (A : X → V ̇) → U ⊔ V ̇
Σ! {U} {V} {X} A = (Σ \(x : X) → A x) × ((x x' : X) → A x → A x' → x ≡ x')

\end{code}

Note: Σ! is to be avoided, in favour of the contractibility of Σ, following univalent mathematics.

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

+disjoint : ∀ {U V} {X : U ̇} {Y : V ̇} {x : X} {y : Y} → ¬(inl x ≡ inr y)
+disjoint ()

+disjoint' : ∀ {U V} {X : U ̇} {Y : V ̇} {x : X} {y : Y} → ¬(inr y ≡ inl x)
+disjoint' ()

inl-lc : ∀ {U V} {X : U ̇} {Y : V ̇} {x x' : X} → inl {U} {V} {X} {Y} x ≡ inl x' → x ≡ x'
inl-lc refl = refl

inr-lc : ∀ {U V} {X : U ̇} {Y : V ̇} {y y' : Y} → inr {U} {V} {X} {Y} y ≡ inr y' → y ≡ y'
inr-lc refl = refl

\end{code}

\begin{code}

𝟙-all-* : ∀ {U} (x : 𝟙) → x ≡ *
𝟙-all-* {U} * = refl {U}

equality-cases : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} (z : X + Y)
              → ((x : X) → z ≡ inl x → A) → ((y : Y) → z ≡ inr y → A) → A
equality-cases (inl x) f g = f x refl
equality-cases (inr y) f g = g y refl

\end{code}

General utilities to avoid (sometimes) mentionint implicit arguments
in function definitions.

\begin{code}

typeOf : ∀ {U} {X : U ̇} → X → U ̇
typeOf {U} {X} x = X

universeOf : ∀ {U} (X : U ̇) → Universe
universeOf {U} X = U

domain dom : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ̇
domain {U} {V} {X} {Y} f = X
dom = domain

codomain cod : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → V ̇
codomain {U} {V} {X} {Y} f = Y
cod = codomain

\end{code}

The two-point type (or booleans)

\begin{code}

data 𝟚 : U₀ ̇ where
 ₀ : 𝟚
 ₁ : 𝟚

𝟚-possibilities : (b : 𝟚) → (b ≡ ₀) + (b ≡ ₁)
𝟚-possibilities ₀ = inl refl
𝟚-possibilities ₁ = inr refl

zero-is-not-one : ₀ ≢ ₁
zero-is-not-one ()

𝟚-induction : ∀ {U} {A : 𝟚 → U ̇} → A ₀ → A ₁ → (x : 𝟚) → A x
𝟚-induction r s ₀ = r
𝟚-induction r s ₁ = s

𝟚-cases : ∀ {U} {A : U ̇} → A → A → 𝟚 → A
𝟚-cases = 𝟚-induction

𝟚-Cases : ∀ {U} {A : U ̇} → 𝟚 → A → A → A
𝟚-Cases a b c = 𝟚-cases b c a

𝟚-equality-cases : ∀ {U} {A : U ̇} {b : 𝟚} → (b ≡ ₀ → A) → (b ≡ ₁ → A) → A
𝟚-equality-cases {U} {A} {₀} f₀ f₁ = f₀ refl
𝟚-equality-cases {U} {A} {₁} f₀ f₁ = f₁ refl

𝟚-equality-cases' : ∀ {U} {A₀ A₁ : U ̇} {b : 𝟚} → (b ≡ ₀ → A₀) → (b ≡ ₁ → A₁) → A₀ + A₁
𝟚-equality-cases' {U} {A₀} {A₁} {₀} f₀ f₁ = inl(f₀ refl)
𝟚-equality-cases' {U} {A₀} {A₁} {₁} f₀ f₁ = inr(f₁ refl)

Lemma[b≡₁→b≢₀] : {b : 𝟚} → b ≡ ₁ → b ≢ ₀
Lemma[b≡₁→b≢₀] r s = zero-is-not-one (s ⁻¹ ∙ r)

Lemma[b≢₀→b≡₁] : {b : 𝟚} → b ≢ ₀ → b ≡ ₁
Lemma[b≢₀→b≡₁] f = 𝟚-equality-cases (𝟘-elim ∘ f) (λ r → r)

Lemma[b≢₁→b≡₀] : {b : 𝟚} → b ≢ ₁ → b ≡ ₀
Lemma[b≢₁→b≡₀] f = 𝟚-equality-cases (λ r → r) (𝟘-elim ∘ f)

Lemma[b≡₀→b≢₁] : {b : 𝟚} → b ≡ ₀ → b ≢ ₁
Lemma[b≡₀→b≢₁] r s = zero-is-not-one (r ⁻¹ ∙ s)

Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] : {a b : 𝟚} → (a ≡ ₁ → b ≡ ₁) → b ≡ ₀ → a ≡ ₀
Lemma[[a≡₁→b≡₁]→b≡₀→a≡₀] f = Lemma[b≢₁→b≡₀] ∘ (contrapositive f) ∘ Lemma[b≡₀→b≢₁]

Lemma[[a≡₀→b≡₀]→b≡₁→a≡₁] : {a b : 𝟚} → (a ≡ ₀ → b ≡ ₀) → b ≡ ₁ → a ≡ ₁
Lemma[[a≡₀→b≡₀]→b≡₁→a≡₁] f = Lemma[b≢₀→b≡₁] ∘ (contrapositive f) ∘ Lemma[b≡₁→b≢₀]

\end{code}

𝟚-Characteristic function of equality on 𝟚:

\begin{code}

complement : 𝟚 → 𝟚
complement ₀ = ₁
complement ₁ = ₀

complement-involutive : (b : 𝟚) → complement(complement b) ≡ b
complement-involutive ₀ = refl
complement-involutive ₁ = refl

eq𝟚 : 𝟚 → 𝟚 → 𝟚
eq𝟚 ₀ n = complement n
eq𝟚 ₁ n = n

eq𝟚-equal : (m n : 𝟚) → eq𝟚 m n ≡ ₁ → m ≡ n
eq𝟚-equal ₀ n p = ap complement (p ⁻¹) ∙ complement-involutive n
eq𝟚-equal ₁ n p = p ⁻¹

equal-eq𝟚 : (m n : 𝟚) → m ≡ n → eq𝟚 m n ≡ ₁
equal-eq𝟚 ₀ ₀ refl = refl
equal-eq𝟚 ₁ ₁ refl = refl

\end{code}

Alternative coproduct:

\begin{code}

_+'_ : ∀ {U} → U ̇ → U ̇ → U ̇
X₀ +' X₁ = Σ \(i : 𝟚) → 𝟚-cases X₀ X₁ i

\end{code}

Natural order of binary numbers:

\begin{code}

_<₂_ : (a b : 𝟚) → U₀ ̇
a <₂ b = (a ≡ ₀) × (b ≡ ₁)

_≤₂_ : (a b : 𝟚) → U₀ ̇
a ≤₂ b = a ≡ ₁ → b ≡ ₁

<₂-coarser-than-≤₂ : {a b : 𝟚} → a <₂ b → a ≤₂ b
<₂-coarser-than-≤₂ (refl , refl) _ = refl

₁-top : {b : 𝟚} → b ≤₂ ₁
₁-top r = refl

₀-bottom : {b : 𝟚} → ₀ ≤₂ b
₀-bottom ()

_≤₂'_ : (a b : 𝟚) → U₀ ̇
a ≤₂' b = b ≡ ₀ → a ≡ ₀

≤₂-coarser-than-≤₂' : {a b : 𝟚} → a ≤₂ b → a ≤₂' b
≤₂-coarser-than-≤₂' {₀} {b} f p = refl
≤₂-coarser-than-≤₂' {₁} {₀} f p = (f refl)⁻¹
≤₂-coarser-than-≤₂' {₁} {₁} f p = p

≤₂'-coarser-than-≤₂ : {a b : 𝟚} → a ≤₂' b → a ≤₂ b
≤₂'-coarser-than-≤₂ {₀} {₀} f p = p
≤₂'-coarser-than-≤₂ {₀} {₁} f p = refl
≤₂'-coarser-than-≤₂ {₁} {₀} f p = (f refl)⁻¹
≤₂'-coarser-than-≤₂ {₁} {₁} f p = p

≤₂-anti : {a b : 𝟚} → a ≤₂ b → b ≤₂ a → a ≡ b
≤₂-anti {₀} {₀} f g = refl
≤₂-anti {₀} {₁} f g = g refl
≤₂-anti {₁} {₀} f g = ≤₂-coarser-than-≤₂' f refl
≤₂-anti {₁} {₁} f g = refl

₁-maximal : {b : 𝟚} → ₁ ≤₂ b → b ≡ ₁
₁-maximal = ≤₂-anti ₁-top

_≥₂_ : (a b : 𝟚) → U₀ ̇
a ≥₂ b = b ≤₂ a

min𝟚 : 𝟚 → 𝟚 → 𝟚
min𝟚 ₀ b = ₀
min𝟚 ₁ b = b

Lemma[minab≤₂a] : {a b : 𝟚} → min𝟚 a b ≤₂ a
Lemma[minab≤₂a] {₀} {b} r = 𝟘-elim(Lemma[b≡₁→b≢₀] r refl)
Lemma[minab≤₂a] {₁} {b} r = refl

Lemma[minab≤₂b] : {a b : 𝟚} → min𝟚 a b ≤₂ b
Lemma[minab≤₂b] {₀} {b} r = 𝟘-elim(Lemma[b≡₁→b≢₀] r refl)
Lemma[minab≤₂b] {₁} {b} r = r

Lemma[min𝟚ab≡₁→b≡₁] : {a b : 𝟚} → min𝟚 a b ≡ ₁ → b ≡ ₁
Lemma[min𝟚ab≡₁→b≡₁] {₀} {₀} r = r
Lemma[min𝟚ab≡₁→b≡₁] {₀} {₁} r = refl
Lemma[min𝟚ab≡₁→b≡₁] {₁} {₀} r = r
Lemma[min𝟚ab≡₁→b≡₁] {₁} {₁} r = refl

Lemma[min𝟚ab≡₁→a≡₁]  : {a b : 𝟚} → min𝟚 a b ≡ ₁ → a ≡ ₁
Lemma[min𝟚ab≡₁→a≡₁] {₀} r = r
Lemma[min𝟚ab≡₁→a≡₁] {₁} r = refl

Lemma[a≡₁→b≡₁→min𝟚ab≡₁] : {a b : 𝟚} → a ≡ ₁ → b ≡ ₁ → min𝟚 a b ≡ ₁
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₀} {₀} p q = q
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₀} {₁} p q = p
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₁} {₀} p q = q
Lemma[a≡₁→b≡₁→min𝟚ab≡₁] {₁} {₁} p q = refl

Lemma[a≤₂b→min𝟚ab≡a] : {a b : 𝟚} → a ≤₂ b → min𝟚 a b ≡ a
Lemma[a≤₂b→min𝟚ab≡a] {₀} {b} p = refl
Lemma[a≤₂b→min𝟚ab≡a] {₁} {b} p = p refl

lemma[min𝟚ab≡₀] : {a b : 𝟚} → min𝟚 a b ≡ ₀ → (a ≡ ₀) + (b ≡ ₀)
lemma[min𝟚ab≡₀] {₀} {b} p = inl p
lemma[min𝟚ab≡₀] {₁} {b} p = inr p

max𝟚 : 𝟚 → 𝟚 → 𝟚
max𝟚 ₀ b = b
max𝟚 ₁ b = ₁

max𝟚-lemma : (a b : 𝟚) → max𝟚 a b ≡ ₁ → (a ≡ ₁) + (b ≡ ₁)
max𝟚-lemma ₀ b r = inr r
max𝟚-lemma ₁ b r = inl refl

max𝟚-lemma-converse : (a b : 𝟚) → (a ≡ ₁) + (b ≡ ₁) → max𝟚 a b ≡ ₁
max𝟚-lemma-converse ₀ b (inl r) = unique-from-𝟘 (zero-is-not-one r)
max𝟚-lemma-converse ₀ b (inr r) = r
max𝟚-lemma-converse ₁ b x = refl

\end{code}

Addition modulo 2:

\begin{code}

_⊕_ : 𝟚 → 𝟚 → 𝟚
₀ ⊕ x = x
₁ ⊕ x = complement x

complement-of-eq𝟚-is-⊕ : (m n : 𝟚) → complement(eq𝟚 m n) ≡ m ⊕ n
complement-of-eq𝟚-is-⊕ ₀ n = complement-involutive n
complement-of-eq𝟚-is-⊕ ₁ n = refl

Lemma[b⊕b≡₀] : {b : 𝟚} → b ⊕ b ≡ ₀
Lemma[b⊕b≡₀] {₀} = refl
Lemma[b⊕b≡₀] {₁} = refl

Lemma[b≡c→b⊕c≡₀] : {b c : 𝟚} → b ≡ c → b ⊕ c ≡ ₀
Lemma[b≡c→b⊕c≡₀] {b} {c} r = ap (λ - → b ⊕ -) (r ⁻¹) ∙ (Lemma[b⊕b≡₀] {b})

Lemma[b⊕c≡₀→b≡c] : {b c : 𝟚} → b ⊕ c ≡ ₀ → b ≡ c
Lemma[b⊕c≡₀→b≡c] {₀} {₀} r = refl
Lemma[b⊕c≡₀→b≡c] {₀} {₁} ()
Lemma[b⊕c≡₀→b≡c] {₁} {₀} ()
Lemma[b⊕c≡₀→b≡c] {₁} {₁} r = refl

Lemma[b≢c→b⊕c≡₁] : {b c : 𝟚} → b ≢ c → b ⊕ c ≡ ₁
Lemma[b≢c→b⊕c≡₁] = Lemma[b≢₀→b≡₁] ∘ (contrapositive Lemma[b⊕c≡₀→b≡c])

Lemma[b⊕c≡₁→b≢c] : {b c : 𝟚} → b ⊕ c ≡ ₁ → b ≢ c
Lemma[b⊕c≡₁→b≢c] = (contrapositive Lemma[b≡c→b⊕c≡₀]) ∘ Lemma[b≡₁→b≢₀]

\end{code}

Order and complements:

\begin{code}

complement-left : {b c : 𝟚} → complement b ≤₂ c → complement c ≤₂ b
complement-left {₀} {₀} f p = f p
complement-left {₀} {₁} f p = p
complement-left {₁} {c} f p = refl

complement-right : {b c : 𝟚} → b ≤₂ complement c → c ≤₂ complement b
complement-right {₀} {c} f p = refl
complement-right {₁} {₀} f p = p
complement-right {₁} {₁} f p = f p

complement-both-left : {b c : 𝟚} → complement b ≤₂ complement c → c ≤₂ b
complement-both-left {₀} {₀} f p = p
complement-both-left {₀} {₁} f p = f p
complement-both-left {₁} {c} f p = refl

complement-both-right : {b c : 𝟚} → b ≤₂ c → complement c ≤₂ complement b
complement-both-right {₀} {c} f p = refl
complement-both-right {₁} {₀} f p = f p
complement-both-right {₁} {₁} f p = p

\end{code}

The natural numbers:

\begin{code}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

rec : ∀ {U} {X : U ̇} → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (succ n) = f(rec x f n)

induction : ∀ {U} {A : ℕ → U ̇} → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n
induction base step 0 = base
induction base step (succ n) = step n (induction base step n)

a-peano-axiom : {n : ℕ} → succ n ≢ 0
a-peano-axiom ()

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-injective : {i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-injective = ap pred

\end{code}

Operator fixity and precedences.

\begin{code}

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
infix  4  _∼_
infixr 31 _⊕_

\end{code}
