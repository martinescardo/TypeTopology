Martin Escardo 1st May 2020.

This is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF.Agda-Lecture-Notes

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MGS.MLTT where

open import MLTT.Universes public

open import MLTT.Unit-Type renaming (𝟙 to 𝟙') public

𝟙 : 𝓤₀ ̇
𝟙 = 𝟙' {𝓤₀}

𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆

open import MLTT.Empty-Type renaming (𝟘 to 𝟘') public

𝟘 : 𝓤₀ ̇
𝟘 = 𝟘' {𝓤₀}

𝟘-induction : (A : 𝟘 → 𝓤 ̇ ) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇ ) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

open import MLTT.Natural-Numbers-Type public

ℕ-induction : (A : ℕ → 𝓤 ̇ )
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n

ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)

ℕ-recursion : (X : 𝓤 ̇ )
            → X
            → (ℕ → X → X)
            → ℕ → X

ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇ )
            → X
            → (X → X)
            → ℕ → X

ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_

module Arithmetic' where

  _+_  _×_ : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_

module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_

open import MLTT.Plus-Type renaming (_+_ to infixr 20 _+_) public

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z

+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

open import MLTT.Sigma-Type renaming (_,_ to infixr 50 _,_) public

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)

Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → A (x , y))
      → ((x : X) (y : Y x) → A (x , y))

curry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)

g ∘ f = λ x → g (f x)

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

open import MLTT.Identity-Type renaming (_＝_ to infix 0 _＝_ ; refl to 𝓻ℯ𝓯𝓵) public
pattern refl x = 𝓻ℯ𝓯𝓵 {x = x}

Id : (X : 𝓤 ̇ ) → X → X → 𝓤 ̇
Id _ x y = x ＝ y

𝕁 : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ＝ y) → A x y p

𝕁 X A f x x (refl x) = f x

ℍ : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ＝ y) → B y p

ℍ x B b x (refl x) = b

𝕁' : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ＝ y) → A x y p

𝕁' X A f x = ℍ x (A x) (f x)

𝕁s-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ＝ y)
             → 𝕁 X A f x y p ＝ 𝕁' X A f x y p

𝕁s-agreement X A f x x (refl x) = refl (f x)

transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ＝ y → A x → A y

transport A (refl x) = 𝑖𝑑 (A x)

transport𝕁 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ＝ y → A x → A y

transport𝕁 {𝓤} {𝓥} {X} A {x} {y} = 𝕁 X (λ x y _ → A x → A y) (λ x → 𝑖𝑑 (A x)) x y

nondep-ℍ : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
         → A x → (y : X) → x ＝ y → A y
nondep-ℍ x A = ℍ x (λ y _ → A y)

transportℍ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ＝ y → A x → A y
transportℍ A {x} {y} p a = nondep-ℍ x A a y p

transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ＝ y)
                     → (transportℍ A p ＝ transport A p)
                     × (transport𝕁 A p ＝ transport A p)

transports-agreement A (refl x) = refl (transport A (refl x)) ,
                                  refl (transport A (refl x))

lhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ＝ y → X
rhs {𝓤} {X} {x} {y} p = y

_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p ∙ q = transport (lhs p ＝_) q p

_＝⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
x ＝⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ＝ x
x ∎ = refl x

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ＝ y → y ＝ x
p ⁻¹ = transport (_＝ lhs p) p (refl (lhs p))

_∙'_ : {X : 𝓤 ̇ } {x y z : X} → x ＝ y → y ＝ z → x ＝ z
p ∙' q = transport (_＝ rhs q) (p ⁻¹) q

∙agreement : {X : 𝓤 ̇ } {x y z : X} (p : x ＝ y) (q : y ＝ z)
           → p ∙' q ＝ p ∙ q

∙agreement (refl x) (refl x) = refl (refl x)

rdnel : {X : 𝓤 ̇ } {x y : X} (p : x ＝ y)
      → p ∙ refl y ＝ p

rdnel p = refl p

rdner : {X : 𝓤 ̇ } {y z : X} (q : y ＝ z)
      → refl y  ∙' q ＝ q

rdner q = refl q

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ＝ x' → f x ＝ f x'
ap f {x} {x'} p = transport (λ - → f x ＝ f -) p (refl (f x))

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ＝ g x

¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬ (¬ A)
¬¬¬ A = ¬ (¬¬ A)

dni : (A : 𝓤 ̇ ) → A → ¬¬ A
dni A a u = u a

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

tno : (A : 𝓤 ̇ ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

_↔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↔ Y = (X → Y) × (Y → X)

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↔ Y) → (Y → X)
rl-implication = pr₂

absurdity³-is-absurdity : {A : 𝓤 ̇ } → ¬¬¬ A ↔ ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = contrapositive (dni A)

  secondly : ¬ A → ¬¬¬ A
  secondly = dni (¬ A)

_≠_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≠ y = ¬ (x ＝ y)

≠-sym : {X : 𝓤 ̇ } {x y : X} → x ≠ y → y ≠ x
≠-sym {𝓤} {X} {x} {y} u = λ (p : y ＝ x) → u (p ⁻¹)

Id→Fun : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇ ))

Id→Fun' : {X Y : 𝓤 ̇ } → X ＝ Y → X → Y
Id→Fun' (refl X) = 𝑖𝑑 X

Id→Funs-agree : {X Y : 𝓤 ̇ } (p : X ＝ Y)
              → Id→Fun p ＝ Id→Fun' p

Id→Funs-agree (refl X) = refl (𝑖𝑑 X)

𝟙-is-not-𝟘 : 𝟙 ≠ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p ⋆

₁-is-not-₀ : ₁ ≠ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙

  q : 𝟙 ＝ 𝟘
  q = ap f p

decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : (X : 𝓤 ̇ ) → 𝓤 ̇
has-decidable-equality X = (x y : X) → decidable (x ＝ y)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≠-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≠ ₀ → n ＝ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ＝ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁

inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≠ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 q
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘

  q : 𝟙 ＝ 𝟘
  q = ap f p

right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
right-fails-gives-left-holds (inl p) u = p
right-fails-gives-left-holds (inr q) u = !𝟘 _ (u q)

module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ＝ n → (x ＝ 1) + (x ＝ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , (p ≥ n)
                                           × is-prime p
                                           × is-prime (p ∔ 2)

positive-not-zero : (x : ℕ) → succ x ≠ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙

  g : succ x ＝ 0 → 𝟙 ＝ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ＝ succ y → x ＝ y
succ-lc = ap pred

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≠-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : decidable (x ＝ y) → decidable (succ x ＝ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ＝ succ y) → k (succ-lc s))

module basic-arithmetic-and-order where

  open ℕ-order public
  open Arithmetic renaming (_+_ to _∔_) hiding (_×_)

  +-assoc : (x y z : ℕ) → (x ∔ y) ∔ z ＝ x ∔ (y ∔ z)

  +-assoc x y zero     = (x ∔ y) ∔ 0 ＝⟨ refl _ ⟩
                         x ∔ (y ∔ 0) ∎

  +-assoc x y (succ z) = (x ∔ y) ∔ succ z   ＝⟨ refl _ ⟩
                         succ ((x ∔ y) ∔ z) ＝⟨ ap succ IH ⟩
                         succ (x ∔ (y ∔ z)) ＝⟨ refl _ ⟩
                         x ∔ (y ∔ succ z)   ∎
   where
    IH : (x ∔ y) ∔ z ＝ x ∔ (y ∔ z)
    IH = +-assoc x y z

  +-assoc' : (x y z : ℕ) → (x ∔ y) ∔ z ＝ x ∔ (y ∔ z)
  +-assoc' x y zero     = refl _
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)

  +-base-on-first : (x : ℕ) → 0 ∔ x ＝ x

  +-base-on-first 0        = refl 0

  +-base-on-first (succ x) = 0 ∔ succ x   ＝⟨ refl _ ⟩
                             succ (0 ∔ x) ＝⟨ ap succ IH ⟩
                             succ x       ∎
   where
    IH : 0 ∔ x ＝ x
    IH = +-base-on-first x

  +-step-on-first : (x y : ℕ) → succ x ∔ y ＝ succ (x ∔ y)

  +-step-on-first x zero     = refl (succ x)

  +-step-on-first x (succ y) = succ x ∔ succ y   ＝⟨ refl _ ⟩
                               succ (succ x ∔ y) ＝⟨ ap succ IH ⟩
                               succ (x ∔ succ y) ∎
   where
    IH : succ x ∔ y ＝ succ (x ∔ y)
    IH = +-step-on-first x y

  +-comm : (x y : ℕ) → x ∔ y ＝ y ∔ x

  +-comm 0 y = 0 ∔ y ＝⟨ +-base-on-first y ⟩
               y     ＝⟨ refl _ ⟩
               y ∔ 0 ∎

  +-comm (succ x) y = succ x ∔ y  ＝⟨ +-step-on-first x y ⟩
                      succ(x ∔ y) ＝⟨ ap succ IH ⟩
                      succ(y ∔ x) ＝⟨ refl _ ⟩
                      y ∔ succ x  ∎
    where
     IH : x ∔ y ＝ y ∔ x
     IH = +-comm x y

  +-lc : (x y z : ℕ) → x ∔ y ＝ x ∔ z → y ＝ z

  +-lc 0        y z p = y     ＝⟨ (+-base-on-first y)⁻¹ ⟩
                        0 ∔ y ＝⟨ p ⟩
                        0 ∔ z ＝⟨ +-base-on-first z ⟩
                        z     ∎

  +-lc (succ x) y z p = IH
   where
    q = succ (x ∔ y) ＝⟨ (+-step-on-first x y)⁻¹ ⟩
        succ x ∔ y   ＝⟨ p ⟩
        succ x ∔ z   ＝⟨ +-step-on-first x z ⟩
        succ (x ∔ z) ∎

    IH : y ＝ z
    IH = +-lc x y z (succ-lc q)

  _≼_ : ℕ → ℕ → 𝓤₀ ̇
  x ≼ y = Σ z ꞉ ℕ , x ∔ z ＝ y

  ≤-gives-≼ : (x y : ℕ) → x ≤ y → x ≼ y
  ≤-gives-≼ 0 0               l = 0 , refl 0
  ≤-gives-≼ 0 (succ y)        l = succ y , +-base-on-first (succ y)
  ≤-gives-≼ (succ x) 0        l = !𝟘 (succ x ≼ zero) l
  ≤-gives-≼ (succ x) (succ y) l = γ
   where
    IH : x ≼ y
    IH = ≤-gives-≼ x y l

    z : ℕ
    z = pr₁ IH

    p : x ∔ z ＝ y
    p = pr₂ IH

    γ : succ x ≼ succ y
    γ = z , (succ x ∔ z   ＝⟨ +-step-on-first x z ⟩
             succ (x ∔ z) ＝⟨ ap succ p ⟩
             succ y       ∎)

  ≼-gives-≤ : (x y : ℕ) → x ≼ y → x ≤ y

  ≼-gives-≤ 0 0               (z , p) = ⋆

  ≼-gives-≤ 0 (succ y)        (z , p) = ⋆

  ≼-gives-≤ (succ x) 0        (z , p) = positive-not-zero (x ∔ z) q
   where
    q = succ (x ∔ z) ＝⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ＝⟨ p ⟩
        zero         ∎

  ≼-gives-≤ (succ x) (succ y) (z , p) = IH
   where
    q = succ (x ∔ z) ＝⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ＝⟨ p ⟩
        succ y       ∎

    IH : x ≤ y
    IH = ≼-gives-≤ x y (z , succ-lc q)

  ≤-refl : (n : ℕ) → n ≤ n
  ≤-refl zero     = ⋆
  ≤-refl (succ n) = ≤-refl n

  ≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
  ≤-trans zero m n p q = ⋆
  ≤-trans (succ l) zero n p q = !𝟘 (succ l ≤ n) p
  ≤-trans (succ l) (succ m) zero p q = q
  ≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

  ≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ＝ n
  ≤-anti zero zero p q = refl zero
  ≤-anti zero (succ n) p q = !𝟘 (zero ＝ succ n) q
  ≤-anti (succ m) zero p q = !𝟘 (succ m ＝ zero) p
  ≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

  ≤-succ : (n : ℕ) → n ≤ succ n
  ≤-succ zero     = ⋆
  ≤-succ (succ n) = ≤-succ n

  zero-minimal : (n : ℕ) → zero ≤ n
  zero-minimal n = ⋆

  unique-minimal : (n : ℕ) → n ≤ zero → n ＝ zero
  unique-minimal zero p = refl zero
  unique-minimal (succ n) p = !𝟘 (succ n ＝ zero) p

  ≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ＝ succ n)
  ≤-split zero n l = inl l
  ≤-split (succ m) zero l = inr (ap succ (unique-minimal m l))
  ≤-split (succ m) (succ n) l = +-recursion inl (inr ∘ ap succ) (≤-split m n l)

  _<_ : ℕ → ℕ → 𝓤₀ ̇
  x < y = succ x ≤ y

  infix 10 _<_

  not-<-gives-≥ : (m n : ℕ) → ¬ (n < m) → m ≤ n
  not-<-gives-≥ zero n u = zero-minimal n
  not-<-gives-≥ (succ m) zero = dni (zero < succ m) (zero-minimal m)
  not-<-gives-≥ (succ m) (succ n) = not-<-gives-≥ m n

  bounded-∀-next : (A : ℕ → 𝓤 ̇ ) (k : ℕ)
                 → A k
                 → ((n : ℕ) → n < k → A n)
                 → (n : ℕ) → n < succ k → A n
  bounded-∀-next A k a φ n l = +-recursion f g s
   where
    s : (n < k) + (succ n ＝ succ k)
    s = ≤-split (succ n) k l

    f : n < k → A n
    f = φ n

    g : succ n ＝ succ k → A n
    g p = transport A ((succ-lc p)⁻¹) a

  root : (ℕ → ℕ) → 𝓤₀ ̇
  root f = Σ n ꞉ ℕ , f n ＝ 0

  _has-no-root<_ : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  f has-no-root< k = (n : ℕ) → n < k → f n ≠ 0

  is-minimal-root : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  is-minimal-root f m = (f m ＝ 0) × (f has-no-root< m)

  at-most-one-minimal-root : (f : ℕ → ℕ) (m n : ℕ)
                           → is-minimal-root f m → is-minimal-root f n → m ＝ n

  at-most-one-minimal-root f m n (p , φ) (q , ψ) = c m n a b
   where
    a : ¬ (m < n)
    a u = ψ m u p

    b : ¬ (n < m)
    b v = φ n v q

    c : (m n : ℕ) → ¬ (m < n) → ¬ (n < m) → m ＝ n
    c m n u v = ≤-anti m n (not-<-gives-≥ m n v) (not-<-gives-≥ n m u)

  minimal-root : (ℕ → ℕ) → 𝓤₀ ̇
  minimal-root f = Σ m ꞉ ℕ , is-minimal-root f m

  minimal-root-is-root : ∀ f → minimal-root f → root f
  minimal-root-is-root f (m , p , _) = m , p

  bounded-ℕ-search : ∀ k f → (minimal-root f) + (f has-no-root< k)
  bounded-ℕ-search zero f = inr (λ n → !𝟘 (f n ≠ 0))
  bounded-ℕ-search (succ k) f = +-recursion φ γ (bounded-ℕ-search k f)
   where
    A : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
    A k f = (minimal-root f) + (f has-no-root< k)

    φ : minimal-root f → A (succ k) f
    φ = inl

    γ : f has-no-root< k → A (succ k) f
    γ u = +-recursion γ₀ γ₁ (ℕ-has-decidable-equality (f k) 0)
     where
      γ₀ : f k ＝ 0 → A (succ k) f
      γ₀ p = inl (k , p , u)

      γ₁ : f k ≠ 0 → A (succ k) f
      γ₁ v = inr (bounded-∀-next (λ n → f n ≠ 0) k v u)

  root-gives-minimal-root : ∀ f → root f → minimal-root f
  root-gives-minimal-root f (n , p) = γ
   where
    g : ¬ (f has-no-root< (succ n))
    g φ = φ n (≤-refl n) p

    γ : minimal-root f
    γ = right-fails-gives-left-holds (bounded-ℕ-search (succ n) f) g

infixr 30 _×_
infix   0 _∼_
infixl 70 _∘_
infix   0 Id
infix  10 _↔_
infixl 30 _∙_
infixr  0 _＝⟨_⟩_
infix   1 _∎
infix  40 _⁻¹
infixr -1 -Σ
infixr -1 -Π

\end{code}
