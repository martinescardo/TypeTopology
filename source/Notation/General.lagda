Martin Escardo.

General terminology and notation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Notation.General where

open import MLTT.Pi
open import MLTT.Sigma
open import MLTT.Universes
open import MLTT.Id
open import MLTT.Negation public

\end{code}

The notation `Type 𝓤` should be avoided in favour of `𝓤 ̇`, but some
module do use it.

\begin{code}

fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ x ꞉ domain f , f x ＝ y

to-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
         → fiber f (f x)
to-fiber f x = x , refl

fiber-point : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y} → fiber f y → X
fiber-point = pr₁

fiber-identification : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {y : Y} (w : fiber f y)
                     → f (fiber-point w) ＝ y
fiber-identification = pr₂

each-fiber-of : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (X → Y)
              → (𝓤 ⊔ 𝓥 ̇ → 𝓦 ̇ )
              → 𝓥 ⊔ 𝓦 ̇
each-fiber-of f P = ∀ y → P (fiber f y)

fix : {X : 𝓤 ̇ } → (f : X → X) → 𝓤 ̇
fix f = Σ x ꞉ domain f , x ＝ f x

from-fix : {X : 𝓤 ̇ } (f : X → X) → fix f → X
from-fix f = pr₁

from-fix-is-fixed : {X : 𝓤 ̇ } (f : X → X) (φ : fix f)
                  → from-fix f φ ＝ f (from-fix f φ)
from-fix-is-fixed f = pr₂

reflexive : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
reflexive R = ∀ x → R x x

symmetric : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
symmetric R = ∀ x y → R x y → R y x

antisymmetric : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
antisymmetric R = ∀ x y → R x y → R y x → x ＝ y

transitive : {X : 𝓤 ̇ } → (X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
transitive R = ∀ x y z → R x y → R y z → R x z

idempotent-map : {X : 𝓥 ̇ } → (f : X → X) → 𝓥 ̇
idempotent-map f = ∀ x → f (f x) ＝ f x

involutive : {X : 𝓥 ̇ } → (f : X → X) → 𝓥 ̇
involutive f = ∀ x → f (f x) ＝ x

left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
left-neutral e _·_ = ∀ x → e · x ＝ x

right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
right-neutral e _·_ = ∀ x → x · e ＝ x

associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
associative _·_ = ∀ x y z → (x · y) · z ＝ x · (y · z)

associative' : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
associative' _·_ = ∀ x y z → x · (y · z) ＝ (x · y) · z

commutative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
commutative _·_ = ∀ x y → (x · y) ＝ (y · x)

left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = ∀ {x x'} → f x ＝ f x' → x ＝ x'

left-cancellable' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable' f = ∀ x x' → f x ＝ f x' → x ＝ x'

right-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤ω
right-cancellable f = {𝓦 : Universe} {Z : 𝓦 ̇ } (g h : codomain f → Z)
                    → g ∘ f ∼ h ∘ f
                    → g ∼ h

_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ↔ B = (A → B) × (B → A)

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↔ Y) → (Y → X)
rl-implication = pr₂

↔-sym : {X : 𝓤' ̇ } {Y : 𝓥' ̇ } → X ↔ Y → Y ↔ X
↔-sym (f , g) = (g , f)

↔-trans : {X : 𝓤' ̇ } {Y : 𝓥' ̇ } {Z : 𝓦' ̇ }
        → X ↔ Y → Y ↔ Z → X ↔ Z
↔-trans (f , g) (h , k) = (h ∘ f , g ∘ k)

↔-refl : {X : 𝓤' ̇ } → X ↔ X
↔-refl = (id , id)

\end{code}

This is to avoid naming implicit arguments:

\begin{code}

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

\end{code}

We use the following to indicate the type of a subterm (where "∶"
(typed "\:" in emacs) is not the same as ":"):

\begin{code}

-id : (X : 𝓤 ̇ ) → X → X
-id X x = x

syntax -id X x = x ∶ X

\end{code}

This is used for efficiency as a substitute for lazy "let" (or "where"):

\begin{code}

case_of_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (a : A) → ((a : A) → B a) → B a
case x of f = f x

Case_of_ : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → (a : A) → ((x : A) → a ＝ x → B a) → B a
Case x of f = f x refl

{-# NOINLINE case_of_ #-}

\end{code}

Notation to try to make proofs readable:

\begin{code}

need_which-is-given-by_ : (A : 𝓤 ̇ ) → A → A
need A which-is-given-by a = a

have_by_ : (A : 𝓤 ̇ ) → A → A
have A by a = a

have_so_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a so b = b

have_so-use_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a so-use b = b

have_and_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → B → B
have a and b = b

apply_to_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → A → B
apply f to a = f a

have_so-apply_ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → A → (A → B) → B
have a so-apply f = f a

assume-then : (A : 𝓤 ̇ ) {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
assume-then A f x = f x

syntax assume-then A (λ x → b) = assume x ∶ A then b

assume-and : (A : 𝓤 ̇ ) {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
assume-and A f x = f x

syntax assume-and A (λ x → b) = assume x ∶ A and b

mapsto : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
mapsto f = f

syntax mapsto (λ x → b) = x ↦ b

infixr 10 mapsto

Mapsto : (A : 𝓤 ̇ ) {B : A → 𝓥 ̇ } → ((a : A) → B a) → (a : A) → B a
Mapsto A f = f

syntax Mapsto A (λ x → b) = x ꞉ A ↦ b

infixr 10 Mapsto

\end{code}

Get rid of this:

\begin{code}

Σ! : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Σ! {𝓤} {𝓥} {X} A = (Σ x ꞉ X , A x) × ((x x' : X) → A x → A x' → x ＝ x')

Sigma! : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Sigma! X A = Σ! A

syntax Sigma! A (λ x → b) = Σ! x ꞉ A , b

infixr -1 Sigma!

\end{code}

Note: Σ! is to be avoided, in favour of the contractibility of Σ,
following univalent mathematics.

Ian Ray, 3rd December 2025.

We add a new syntax where we reason with functions chained in sequence which is
analogous to reasoning by chains of equations or equivalences (see
MLTT/Id.lagda and UF/Equiv.lagda to review these ideas). We will include both
compostional and diagrammatic order.

Notice that reasoning in compositional order with g : B → C and f : A → B

 C ←⟨ g ⟩
 B ←⟨ f ⟩
 A ▢

amounts to a function A → C (via normal composition), but it appears in the
'bottom up' direction. This may seem strange at first, as one might expect
this feature to only be useful in the forward direction, that is, in
diagrammatic order. In fact, the above actually reflects a common mode of proof
where one proves C by observing it suffices to prove B (and supplying a map
from B to C) and then proving B by observing it suffices to prove A (and
supplying a map from A to B). For this reason we provide notation that allows
us to display proofs of this sort.

\begin{code}

_→⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → (X → Y) → (Y → Z) → (X → Z)
_ →⟨ f ⟩ g = g ∘ f

_←⟨_⟩_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ ) → (Y → Z) → (X → Y) → (X → Z)
_ ←⟨ g ⟩ f = g ∘ f

_suffices-to-show⟨_⟩_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (Z : 𝓦 ̇ )
                      → (Y → Z) → (X → Y) → (X → Z)
_ suffices-to-show⟨ g ⟩ f = g ∘ f

_▢ : (X : 𝓤 ̇ ) → X → X
X ▢ = id

by-instance-resolution : {X : 𝓤 ̇ } → {{X}} → X
by-instance-resolution  {{x}} = x

\end{code}

Fixities:

\begin{code}

infixl -1 -id
infix -1 _↔_
infixr 0 _→⟨_⟩_
infixr 0 _←⟨_⟩_
infixr 0 _suffices-to-show⟨_⟩_
infix  1 _▢

\end{code}
