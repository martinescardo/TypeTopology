Martin Escardo 2011.

Our Spartan (intensional) Martin-Löf type theory has a countable tower
of universes, the empty type ∅, the unit type 𝟙, product types Π, sum
types Σ (and hence binary product types _×_), sum types _+_, and
identity types _≡_.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SpartanMLTT where

open import Agda.Primitive using (_⊔_) renaming (lzero to U₀ ; lsuc to usuc ; Level to Universe) public

_̇ : (U : Universe) → _
U ̇ = Set U -- This should be the only use of the Agda keyword 'Set' in this development.

_′ : Universe → Universe
_′ = usuc

U₁ = U₀ ′
U₂ = U₁ ′

\end{code}

For example, we write the following instead of the usual

  unique-from-∅ : ∀ {ℓ} {A : Set ℓ} → ∅ → A
  unique-from-∅ = λ ()

\begin{code}

data 𝟘 : U₀ ̇ where

unique-from-𝟘 : ∀ {U} {A : U ̇} → 𝟘 → A
unique-from-𝟘 = λ ()

𝟘-elim = unique-from-𝟘


\end{code}

The one-element set is defined by induction with one case:
\begin{code}

data 𝟙 : U₀ ̇ where
 * : 𝟙 

unique-to-𝟙 : ∀ {U} {A : U ̇} → A → 𝟙
unique-to-𝟙 a = *

\end{code}

Product types are built-in, but we may introduce the standard notation:

\begin{code}

Π : ∀ {U V} {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
Π Y = (x : _) → Y x
 
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

Σ-elim : ∀ {U V} {X : U ̇} {Y : X → V ̇} {A : (Σ \(x : X) → Y x) → U ⊔ V ̇}
   → ((x : X) (y : Y x) → A(x , y)) → (t : (Σ \(x : X) → Y x)) → A t
Σ-elim f (x , y) = f x y

uncurry : ∀ {U V W} {X : U ̇} {Y : X → V ̇} {Z : W ̇}
        → ((x : X) → Y x → Z) → (Σ \(x : X) → Y x) → Z
uncurry f (x , y) = f x y


curry :  ∀ {U V W} {X : U ̇} {Y : X → V ̇} {Z : W ̇}
      → ((Σ \(x : X) → Y x) → Z) → ((x : X) → Y x → Z)
curry f x y = f(x , y)

\end{code}

Equivalently, Σ-elim f t = f (pr₁ t) (pr₂ t).

As usual in type theory, binary products are particular cases of
dependent sums.

\begin{code}

_×_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
X × Y = Σ \(x : X) → Y

\end{code}

This can also be considered as a special case, but I won't
bother:

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

General constructions on functions:

\begin{code}

_∘_ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : Y → W ̇}
    → ((y : Y) → Z y) → (f : X → Y) → (x : X) → Z(f x)
g ∘ f = λ x → g(f x)

id : ∀ {U} {X : U ̇} → X → X
id x = x

\end{code}

I use JJ and KK to avoid confusion with J and K for
equality.

\begin{code}

KK : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
KK R X = (X → R) → R

dual : ∀ {U V W} {X : U ̇} {Y : V ̇} (R : W ̇) → (X → Y) → (Y → R) → (X → R)
dual R f p = p ∘ f

K-functor : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : W ̇} → (X → Y) → KK R X → KK R Y
K-functor = dual _ ∘ dual _

ηK : ∀ {U V} {R : U ̇} {X : V ̇} → X → KK R X
ηK x p = p x

\end{code}

K-unshift:

\begin{code}

KU : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : X → W ̇}
   → KK R ((x : X) → Y x) → (x : X) → KK R (Y x)
KU = λ f x g → f(λ h → g(h x))

\end{code}

Special case, if you like:

\begin{code}

ku : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : W ̇} → KK R (X × Y) → KK R X × KK R Y
ku φ = (K-functor pr₁ φ , K-functor pr₂ φ)

\end{code}

I am not sure were to put the following (product of quantifiers and
selection functions). At the moment it goes in this module. It is not
used, but it is included for the sake of comparison with similar
patterns.

\begin{code}

quant-prod : ∀ {U V} {X R : U ̇} {Y : X → V ̇}
    → KK R X → ((x : X)  → KK R (Y x)) → KK R ((Σ \(x : X)  → Y x))
quant-prod φ γ p = φ(λ x → γ x (λ y → p(x , y)))

JJ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
JJ R X = (X → R) → X

sel-prod : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : X → W ̇}
         → JJ R X → ((x : X) → JJ R (Y x)) → JJ R (Σ \(x : X) → Y x)
sel-prod {U} {V} {W} {R} {X} {Y} ε δ p = (x₀ , y₀)
   where 
    next : (x : X) → Y x
    next x = δ x (λ y → p(x , y))
    x₀ : X
    x₀ = ε(λ x → p(x , next x))
    y₀ : Y x₀
    y₀ = next x₀ 

\end{code}

Alternative, equivalent, construction:

\begin{code}

overline : ∀ {U V} {R : U ̇} {X : V ̇} → JJ R X → KK R X
overline ε p = p(ε p)

sel-prod' : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : X → W ̇}
          → JJ R X → ((x : X) → JJ R (Y x)) → JJ R (Σ \(x : X) → Y x)
sel-prod' {U} {V} {W} {R} {X} {Y} ε δ p = (x₀ , y₀)
   where 
    x₀ : X
    x₀ = ε(λ x → overline(δ x) (λ y → p(x , y)))
    y₀ : Y x₀
    y₀ = δ x₀ (λ y → p(x₀ , y))

\end{code}

Some basic Curry--Howard logic. 

\begin{code}

_⇔_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
A ⇔ B = (A → B) × (B → A)

¬_ : ∀ {U}→ U ̇ → U ̇
¬ A = A → 𝟘

contrapositive : ∀ {U V} {A : U ̇} {B : V ̇} → (A → B) → ¬ B → ¬ A
contrapositive = dual _

\end{code}

Double-negation monad:

\begin{code}

¬¬ : ∀ {U} → U ̇ → U ̇
¬¬ A = ¬(¬ A)

¬¬-functor : ∀ {U V} {A : U ̇} {B : V ̇} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor = K-functor

double-negation-intro : ∀ {U} {A : U ̇} → A → ¬¬ A
double-negation-intro = ηK

three-negations-imply-one : ∀ {U} {A : U ̇} → ¬(¬¬ A) → ¬ A
three-negations-imply-one = contrapositive double-negation-intro

not-exists-implies-forall-not : ∀ {U V} {X : U ̇} {A : X → V ̇}
    → ¬(Σ \(x : X) → A x) → (x : X) → ¬(A x)
not-exists-implies-forall-not = curry

forall-not-implies-not-Σ : ∀ {U} {X : U ̇} {A : X → U ̇}
    → ((x : X) → ¬(A x)) → ¬(Σ \(x : X) → A x)
forall-not-implies-not-Σ = uncurry

Left-fails-then-right-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → P + Q → ¬ P → Q
Left-fails-then-right-holds (inl p) u = 𝟘-elim (u p)
Left-fails-then-right-holds (inr q) u = q

Right-fails-then-left-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → P + Q → ¬ Q → P
Right-fails-then-left-holds (inl p) u = p
Right-fails-then-left-holds (inr q) u = 𝟘-elim (u q)

\end{code}

Double-negation unshift:

\begin{code}

DNU : ∀ {U V} {X : U ̇} {A : X → V ̇} → ¬¬((x : X) → A x) → (x : X) → ¬¬(A x)
DNU = KU

\end{code}

Special case, if you like:

\begin{code}

dnu : ∀ {U} {V} {A : U ̇} {B : V ̇} → ¬¬(A × B) → ¬¬ A × ¬¬ B
dnu = ku
 
\end{code}

Binary relations:

\begin{code}

bin-rel : ∀ {U} → U ̇ → U ′ ̇
bin-rel {U} X = X → X → U ̇

\end{code}

Equality (should be moved to the module UF).

\begin{code}

data _≡_ {U : Universe} {X : U ̇} : X → X → U ̇ where
  refl : {x : X} → x ≡ x

idp : ∀ {U} {X : U ̇} (x : X) → x ≡ x
idp _ = refl

_≢_ : ∀ {U} {X : U ̇} → (x y : X) → U ̇
x ≢ y = x ≡ y → 𝟘

Id : ∀ {U} {X : U ̇} → X → X → U ̇
Id = _≡_

sum-disjoint : ∀ {U V} {X : U ̇} {Y : V ̇} {x : X} {y : Y} → inl x ≡ inr y → 𝟘
sum-disjoint ()

\end{code}

Induction on ≡:

\begin{code}

Jbased : ∀ {U V} {X : U ̇} (x : X)
  → (A : (y : X) → x ≡ y → V ̇)
  → A x refl
  → (y : X) (r : x ≡ y)
  → A y r
Jbased x A b .x refl = b

J : ∀ {U V} {X : U ̇}
  → (A : (x y : X) → x ≡ y → V ̇)
  → ((x : X) → A x x refl)
  → {x y : X} (r : x ≡ y) → A x y r
J A f {x} {y} = Jbased x (λ y p → A x y p) (f x) y

\end{code}

We will often use pattern matching rather than J, but we'll make sure
we don't use the K rule (UIP) inadvertently. But not in the following
definition:

\begin{code}

pseudo-uip : ∀ {U} {X : U ̇} {x x' : X} (r : x ≡ x') → (x , refl) ≡ (x' , r)
pseudo-uip {U} {X} = J {U} {U} {X} A (λ x → refl)
 where
   A : (x x' : X) → x ≡ x' → U ̇
   A x x' r = _≡_ {_} {Σ \(x' : X) → x ≡ x'} (x , refl) (x' , r)

\end{code}

The parameter Y is not used explicitly in the definition of transport,
but hardly ever can be inferred by Agda, and hence we make it
explicit:

\begin{code}

transport : ∀ {U V} {X : U ̇}(A : X → V ̇){x y : X}
          → x ≡ y → A x → A y
transport A {x} {y} p a = Jbased x (λ y p → A y) a y p

_∙_ : ∀ {U} {X : U ̇}
     → {x y z : X} →  x ≡ y  →  y ≡ z  →  x ≡ z
p ∙ q = transport (Id _) q p

_⁻¹ : ∀ {U} {X : U ̇} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (λ x → x ≡ _) p refl

≢-sym : ∀ {U} {X : U ̇} → {x y : X} → x ≢ y → y ≢ x
≢-sym u r = u(r ⁻¹)

trans-sym : ∀ {U} {X : U ̇} {x y : X} (r : x ≡ y) → r ⁻¹ ∙ r ≡ refl
trans-sym refl = refl

trans-sym' : ∀ {U} {X : U ̇} {x y : X} (r : x ≡ y) → r ∙ r ⁻¹ ≡ refl
trans-sym' refl = refl

ap : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
ap f p = transport (λ y → f _ ≡ f y) p refl

ap-id-is-id : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y) → p ≡ ap id p
ap-id-is-id refl = refl

Lemma-ap-ap : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z) {x x' : X}
              (r : x ≡ x')
           → ap g (ap f r) ≡ ap (g ∘ f) r
Lemma-ap-ap {U} {V} {W} {X} {Y} {Z} f g = J A (λ x → refl)
 where
  A : (x x' : X) → x ≡ x' → W ̇
  A x x' r = ap g (ap f r) ≡ ap (g ∘ f) r

ap₂ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y}
   → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
ap₂ f refl refl = refl

_∼_ : ∀ {U V} {X : U ̇} {A : X → V ̇} → Π A → Π A → U ⊔ V ̇
f ∼ g = ∀ x → f x ≡ g x

happly : ∀ {U V} {X : U ̇} {A : X → V ̇} (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ h → h x) p

ap-eval : ∀ {U V} {X : U ̇} {A : X → V ̇} {f g : Π A} → f ≡ g → f ∼ g
ap-eval = happly _ _

sym-is-inverse : ∀ {U} {X : U ̇} {x y : X} (p : x ≡ y)
               → refl ≡ p ⁻¹ ∙ p
sym-is-inverse {X} = J (λ x y p → refl ≡ p ⁻¹ ∙ p) (λ x → refl)

Lemma[x≡y→y≡z→y≡z] : ∀ {U} {X : U ̇} {x y z : X} → x ≡ y → x ≡ z → y ≡ z
Lemma[x≡y→y≡z→y≡z] refl p = p

Lemma[x≡y→x≡z→z≡y] : ∀ {U} {X : U ̇} {x y z : X} → x ≡ y → x ≡ z → z ≡ y
Lemma[x≡y→x≡z→z≡y] p refl = p

Lemma[x≡y→x≡z→y≡z] : ∀ {U} {X : U ̇} {x y z : X} → x ≡ y → x ≡ z → y ≡ z
Lemma[x≡y→x≡z→y≡z] refl p = p

Lemma[x≡z→y≡z→x≡y] : ∀ {U} {X : U ̇} {x y z : X} → x ≡ z → y ≡ z → x ≡ y
Lemma[x≡z→y≡z→x≡y] p refl = p

Lemma[fx≡y→x≡x'→fx'≡y] : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) {x x' : X} {y : Y}
                         → f x ≡ y →  x ≡ x' → f x' ≡ y
Lemma[fx≡y→x≡x'→fx'≡y] f {x} {x'} {y} r s =  Lemma[x≡y→x≡z→z≡y] r (ap f s)

equality-cases : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : W ̇} (z : X + Y)
      → ((x : X) → z ≡ inl x → A) → ((y : Y) → z ≡ inr y → A) → A
equality-cases (inl x) f g = f x refl
equality-cases (inr y) f g = g y refl

+disjoint : ∀ {U V} {X : U ̇} {Y : V ̇} {x : X} {y : Y} → inl x ≡ inr y → 𝟘
+disjoint ()

+disjoint' : ∀ {U V} {X : U ̇} {Y : V ̇} {x : X} {y : Y} → inr y ≡ inl x → 𝟘
+disjoint' ()

inl-injective : ∀ {U V} {X : U ̇} {Y : V ̇} {x x' : X} → inl {U} {V} {X} {Y} x ≡ inl x' → x ≡ x'
inl-injective refl = refl

inr-injective : ∀ {U V} {X : U ̇} {Y : V ̇} {y y' : Y} → inr {U} {V} {X} {Y} y ≡ inr y' → y ≡ y'
inr-injective refl = refl

×-≡ : ∀ {U V} {X : U ̇} {Y : V ̇} {x x' : X} {y y' : Y}
     → x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y') 
×-≡ refl refl = refl

Σ! : ∀ {U V} {X : U ̇} (A : X → V ̇) → U ⊔ V ̇ 
Σ! {U} {V} {X} A = (Σ \(x : X) → A x) × ((x x' : X) → A x → A x' → x ≡ x')

Σ-≡-lemma : ∀ {U V} {X : U ̇} {Y : X → V ̇} (u v : Σ Y) (r : u ≡ v)
          → transport Y (ap pr₁ r) (pr₂ u) ≡ (pr₂ v)
Σ-≡-lemma {U} {V} {X} {Y} u v = J A (λ u → refl) {u} {v}
 where
  A : (u v : Σ Y) → u ≡ v → V ̇
  A u v r = transport Y (ap pr₁ r) (pr₂ u) ≡ (pr₂ v)

Σ-≡-lemma' : ∀ {U V} {X : U ̇} {Y : X → V ̇} (x : X) (y y' : Y x)
           → (r : (x , y) ≡ (x , y')) → transport Y (ap pr₁ r) y ≡ y'
Σ-≡-lemma' x y y' = Σ-≡-lemma (x , y) (x , y')

Σ-≡ : ∀ {U V} {X : U ̇} {Y : X → V ̇} (x x' : X) (y : Y x) (y' : Y x')
     → (p : x ≡ x') → transport Y p y ≡ y' → (x , y) ≡ (x' , y') 
Σ-≡ .x' x' .y y refl refl = refl

Σ-≡' : ∀ {U V} {X : U ̇} {Y : X → V ̇} (x : X) (y y' : Y x) 
     → y ≡ y' → _≡_ {_} {Σ Y} (x , y) (x , y') 
Σ-≡' x y y' r = ap (λ y → (x , y)) r

\end{code}

Standard syntax for equality chain reasoning:

\begin{code}

_≡⟨_⟩_ : ∀ {U} {X : U ̇} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = p ∙ q

_∎ : ∀ {U} {X : U ̇} → (x : X) → x ≡ x
_∎ _ = refl

𝟙-all-* : (x : 𝟙) → x ≡ *
𝟙-all-* * = refl 

typeOf : ∀ {U} {X : U ̇} → X → U ̇
typeOf {U} {X} x = X

universeOf : ∀ {U} (X : U ̇) → Universe
universeOf {U} X = U

domain : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ̇
domain {U} {V} {X} {Y} f = X

codomain : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → V ̇
codomain {U} {V} {X} {Y} f = Y

\end{code}

\begin{code}

infix  0 _̇
infix  99 _′
infix  4  _∼_
infixl 2 _∙_
infix  1 _∎
infixr 0 _≡⟨_⟩_ 
infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_ 
infix  50 ¬_
infix  0 _≡_
infix  0 _≢_
infix  3  _⁻¹
infix  -1 _⇔_

\end{code}

