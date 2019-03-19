{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where

open import Universes

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇ )
            → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-induction' : (B : 𝓤 ̇ ) → B → (𝟙 → B)
𝟙-induction' B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇ ) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 x = ⋆

data 𝟘 : 𝓤₀ ̇  where

𝟘-induction : (A : 𝟘 → 𝓤 ̇ )
            → (x : 𝟘) → A x
𝟘-induction A ()

!𝟘 : (A : 𝓤 ̇ ) → 𝟘 → A
!𝟘 A a = 𝟘-induction (λ _ → A) a

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

data ℕ : 𝓤₀ ̇  where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

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
ℕ-iteration A a f = ℕ-recursion A a (λ _ a → f a)

module Arithmetic where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 0 _+_
  infixl 1 _×_

module Arithmetic' where

  _+_  _×_  : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 0 _+_
  infixl 1 _×_

module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

data _+_ {𝓤 𝓥} (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇ )
            → ((x : X) → A(inl x))
            → ((y : Y) → A(inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

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

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor _,_
  field
   x : X
   y : Y x

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A(x , y))
            → (z : Σ Y) → A z
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → ((z : Σ Y) → A z)
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ \(x : X) → Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

id : {X : 𝓤 ̇ } → X → X
id x = x

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

data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x

_≡_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≡ y = Id _ x y

J : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
J X A f x x (refl x) = f x

H : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
H x B b x (refl x) = b

J' : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
J' X A f x = H x (A x) (f x)

Js-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ≡ y)
             → J X A f x y p ≡ J' X A f x y p
Js-agreement X A f x x (refl x) = refl (f x)

transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl x) = id

transportJ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportJ {𝓤} {𝓥} {X} A {x} {y} = J X (λ x y _ → A x → A y) (λ x → id) x y

nondep-H : {X : 𝓤 ̇ } (x : X) (A : X → 𝓥 ̇ )
         → A x → (y : X) → x ≡ y → A y
nondep-H {𝓤} {𝓥} {X} x A = H x (λ y _ → A y)

transportH : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
           → x ≡ y → A x → A y
transportH {𝓤} {𝓥} {X} A {x} {y} p a = nondep-H x A a y p

transports-agreement : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → (transportH A p ≡ transportH A p)
                     × (transportJ A p ≡ transportH A p)
transports-agreement A (refl x) = refl (transport A (refl x)) ,
                                  refl (transport A (refl x))

lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (lhs p ≡_) q p

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f (lhs p) ≡ f -) p (refl (f (lhs p)))

_∼_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → A x) → ((x : X) → A x) → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬  A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

dni : {A : 𝓤 ̇ } → A → ¬¬ A
dni a u = u a

contrapositive : {A : 𝓤 ̇ } {B : 𝓤 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

tno : {A : 𝓤 ̇ } → ¬¬¬ A → ¬ A
tno = contrapositive dni

_≢_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)

≢-sym : {X : 𝓤 ̇ } {x y : X} → x ≢ y → y ≢ x
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)

𝟙-is-not-𝟘 : ¬(𝟙 ≡ 𝟘)
𝟙-is-not-𝟘 p = f p ⋆
 where
  f : 𝟙 ≡ 𝟘 → 𝟙 → 𝟘
  f = transport id

₁-is-not-₀ : ¬(₁ ≡ ₀)
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p

₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()

𝟚-has-decidable-equality : (m n : 𝟚) → (m ≡ n) + (m ≢ n)
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁

inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 r
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘
  r : 𝟙 ≡ 𝟘
  r = ap f p

module twin-primes where

 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ \(p : ℕ) → (p ≥ n) × is-prime p × is-prime (p ∔ 2)

is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton ⋆ ⋆ = refl ⋆

is-prop is-truth-value : 𝓤 ̇ → 𝓤 ̇
is-prop        = is-subsingleton
is-truth-value = is-subsingleton

is-set : 𝓤 ̇ → 𝓤 ̇
is-set X = (x y : X) → is-subsingleton (x ≡ y)

Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X × (X → X → X)

⟨_⟩ : Magma 𝓤 → 𝓤 ̇
⟨ X , i , _·_ ⟩ = X

magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
magma-operation ( X , i , _·_ ) = _·_

syntax magma-operation M x y = x ·⟨ M ⟩ y

is-magma-hom : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
is-magma-hom M N f = (x y : ⟨ M ⟩) → f (x ·⟨ M ⟩ y) ≡ f x ·⟨ N ⟩ f y

id-is-magma-hom : (M : Magma 𝓤) → is-magma-hom M M id
id-is-magma-hom M = λ (x y : ⟨ M ⟩) → refl (x ·⟨ M ⟩ y)

is-magma-iso : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
is-magma-iso M N f = is-magma-hom M N f
                   × Σ \(g : ⟨ N ⟩ → ⟨ M ⟩) → is-magma-hom N M g
                                            × (g ∘ f ∼ id)
                                            × (f ∘ g ∼ id)

id-is-magma-iso : (M : Magma 𝓤) → is-magma-iso M M id
id-is-magma-iso M = id-is-magma-hom M ,
                    id ,
                    id-is-magma-hom M ,
                    refl ,
                    refl

⌜_⌝ : {M N : Magma 𝓤} → M ≡ N → ⟨ M ⟩ → ⟨ N ⟩
⌜ p ⌝ = transport ⟨_⟩ p

⌜⌝-is-iso : {M N : Magma 𝓤} (p : M ≡ N) → is-magma-iso M N (⌜ p ⌝)
⌜⌝-is-iso (refl M) = id-is-magma-iso M

_≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
M ≅ₘ N = Σ \(f : ⟨ M ⟩ → ⟨ N ⟩) → is-magma-iso M N f

magma-≡-to-iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
magma-≡-to-iso p = (⌜ p ⌝ , ⌜⌝-is-iso p )

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ \(X : 𝓤 ̇ ) → X → X → X

left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
left-neutral {𝓤} {X} e _·_ = (x : X) → e · x ≡ x

right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
right-neutral {𝓤} {X} e _·_ = (x : X) → x ≡ e · x

associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
associative {𝓤} {X} _·_ = (x y z : X) → (x · y) · z ≡ x · (y · z)

Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoid 𝓤 = Σ \(X : 𝓤 ̇ ) → is-set X
                         × Σ \(_·_ : X → X → X)
                         → Σ \(e : X)
                         → left-neutral e _·_
                         × right-neutral e _·_
                         × associative _·_

refl-left : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p

∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)

⁻¹-left∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)

⁻¹-right∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

⁻¹-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)

transport∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p
transport∙ A p (refl y) = refl (transport A p)

_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x

data Color : 𝓤₀ ̇  where
 Black White : Color

dId : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y) → A x → A y → 𝓥 ̇
dId A p a b = transport A p a ≡ b

syntax dId A p a b = a ≡[ p / A ] b

≡[]-on-refl-is-≡ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x : X} (a b : A x)
                 → (a ≡[ refl x / A ] b) ≡ (a ≡ b)
≡[]-on-refl-is-≡ A {x} a b = refl (a ≡ b)

≡[]-on-refl-is-≡' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x : X} (a b : A x)
                → (a ≡[ refl x / A ] b) ≡ (a ≡ b)

≡[]-on-refl-is-≡' {𝓤} {𝓥} {X} A {x} a b = refl {𝓥 ⁺} {𝓥 ̇ } (a ≡ b)

to-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
       → (Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl x , refl a) = refl (x , a)

from-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
         → σ ≡ τ
         → Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ
from-Σ-≡ (refl (x , a)) = (refl x , refl a)

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)

is-singleton : 𝓤 ̇ → 𝓤 ̇
is-singleton X = Σ \(c : X) → (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl ⋆)

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0        = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , φ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ

singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y ⟩
                                             y ∎

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ ) → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = (x , s x)

EM EM' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM  𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X

EM-gives-EM' : EM 𝓤 → EM' 𝓤
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  γ (inr x) = inr x

EM'-gives-EM : EM' 𝓤 → EM 𝓤
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr x) = inr x

wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'

collapsible : 𝓤 ̇ → 𝓤 ̇
collapsible X = Σ \(f : X → X) → wconstant f

collapser : (X : 𝓤 ̇ ) → collapsible X → X → X
collapser X (f , w) = f

collapser-wconstancy : (X : 𝓤 ̇ ) (c : collapsible X) → wconstant (collapser X c)
collapser-wconstancy X (f , w) = w

hedberg : {X : 𝓤 ̇ } (x : X)
        → ((y : X) → collapsible (x ≡ y))
        → (y : X) → is-subsingleton (x ≡ y)
hedberg {𝓤} {X} x c y p q =
 p                       ≡⟨ a y p ⟩
 f x (refl x)⁻¹ ∙ f y p  ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 f x (refl x)⁻¹ ∙ f y q  ≡⟨ (a y q)⁻¹ ⟩
 q                       ∎
 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = pr₁ (c y)
  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = pr₂ (c y)
  a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
  a x (refl x) = (⁻¹-left∙ (f x (refl x)))⁻¹

≡-collapsible : 𝓤 ̇ → 𝓤 ̇
≡-collapsible X = (x y : X) → collapsible(x ≡ y)

sets-are-≡-collapsible : (X : 𝓤 ̇ ) → is-set X → ≡-collapsible X
sets-are-≡-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q

≡-collapsibles-are-sets : (X : 𝓤 ̇ ) → ≡-collapsible X → is-set X
≡-collapsibles-are-sets X c x = hedberg x (λ y → collapser (x ≡ y) (c x y) ,
                                                 collapser-wconstancy (x ≡ y) (c x y))

subsingletons-are-≡-collapsible : (X : 𝓤 ̇ ) → is-subsingleton X → ≡-collapsible X
subsingletons-are-≡-collapsible X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)

subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = ≡-collapsibles-are-sets X (subsingletons-are-≡-collapsible X s)

subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇ ) → is-subsingleton X → X is-of-hlevel 1
subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)

types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇ ) → X is-of-hlevel 1 → is-subsingleton X
types-of-hlevel-1-are-subsingletons X = f
 where
  f : ((x y : X) → is-singleton (x ≡ y)) → (x y : X) → x ≡ y
  f s x y = center (x ≡ y) (s x y)

sets-are-of-hlevel-2 : (X : 𝓤 ̇ ) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X = g
 where
  g : ((x y : X) → is-subsingleton (x ≡ y)) → (x y : X) → (x ≡ y) is-of-hlevel 1
  g t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)

types-of-hlevel-2-are-sets : (X : 𝓤 ̇ ) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X = f
 where
  f : ((x y : X) → (x ≡ y) is-of-hlevel 1) → (x y : X) → is-subsingleton (x ≡ y)
  f s x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (s x y)

hlevel-upper : (X : 𝓤 ̇ ) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper X zero = γ
 where
  γ : (h : is-singleton X) (x y : X) → is-singleton (x ≡ y)
  γ h x y = p , subsingletons-are-sets X k x y p
   where
    k : is-subsingleton X
    k = singletons-are-subsingletons X h
    p : x ≡ y
    p = k x y
hlevel-upper X (succ n) = λ h x y → hlevel-upper (x ≡ y) n (h x y)

positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙
  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred

ℕ-has-decidable-equality : (x y : ℕ) → (x ≡ y) + (x ≢ y)
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : (x ≡ y) + x ≢ y → (succ x ≡ succ y) + (succ x ≢ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))

ℕ-is-set : is-set ℕ
ℕ-is-set = ≡-collapsibles-are-sets ℕ ℕ-≡-collapsible
 where
  ℕ-≡-collapsible : ≡-collapsible ℕ
  ℕ-≡-collapsible x y = f (ℕ-has-decidable-equality x y) ,
                        κ (ℕ-has-decidable-equality x y)
   where
    f : (x ≡ y) + ¬(x ≡ y) → x ≡ y → x ≡ y
    f (inl p) q = p
    f (inr g) q = !𝟘 (x ≡ y) (g q)
    κ : (d : (x ≡ y) + ¬(x ≡ y)) → wconstant (f d)
    κ (inl p) q r = refl p
    κ (inr g) q r = !𝟘 (f (inr g) q ≡ f (inr g) r) (g q)

Nat : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = (x : domain A) → A x → B x

Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y) → τ y ∘ transport A p ≡ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)

NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ \(s : codomain r → domain r) → r ∘ s ∼ id

_◁_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ \(r : Y → X) → has-section r

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y) → retraction ρ ∘ section ρ ∼ id
retract-equation (r , s , η) = η

◁-refl : (X : 𝓤 ̇ ) → X ◁ X
◁-refl X = id , id , refl

_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z

(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , p)
 where
  p = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
            r (s x)           ≡⟨ η x ⟩
            x                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = ◁-refl X

Σ-retract : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
          → ((x : X) → (A x) ◁ (B x)) → Σ A ◁ Σ B
Σ-retract X A B ρ = NatΣ r , NatΣ s , η'
 where
  r : (x : X) → B x → A x
  r x = retraction (ρ x)
  s : (x : X) → A x → B x
  s x = section (ρ x)
  η : (x : X) (a : A x) → r x (s x a) ≡ a
  η x = retract-equation (ρ x)
  η' : (σ : Σ A) → NatΣ r (NatΣ s σ) ≡ σ
  η' (x , a) = x , r x (s x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
               x , a           ∎

Σ-retract-reindexing : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } (r : Y → X)
                     → has-section r
                     → (Σ \(x : X) → A x) ◁ (Σ \(y : Y) → A (r y))
Σ-retract-reindexing {𝓤} {𝓥} {𝓦} {X} {Y} {A} r (s , η) = γ , φ , γφ
 where
  γ : Σ (A ∘ r) → Σ A
  γ (y , a) = (r y , a)
  φ : Σ A → Σ (A ∘ r)
  φ (x , a) = (s x , transport A ((η x)⁻¹) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡ (η x , p)
   where
    p : transport A (η x) (transport A ((η x)⁻¹) a) ≡ a
    p = transport A (η x) (transport A ((η x)⁻¹) a) ≡⟨ (ap (λ - → - a) (transport∙ A ((η x)⁻¹) (η x)))⁻¹ ⟩
        transport A ((η x)⁻¹ ∙ η x ) a              ≡⟨ ap (λ - → transport A - a) (⁻¹-left∙ (η x)) ⟩
        transport A (refl x) a                      ≡⟨ refl a ⟩
        a                                           ∎

singleton-type : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type x = Σ \y → y ≡ x

singleton-type-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-type-center x = (x , refl x)

singleton-type-centered : {X : 𝓤 ̇ } (x y : X) (p : y ≡ x) → singleton-type-center x ≡ (y , p)
singleton-type-centered x x (refl x) = refl (singleton-type-center x)

singleton-types-are-singletons : {X : 𝓤 ̇ } (x : X) → is-singleton (singleton-type x)
singleton-types-are-singletons {𝓤} {X} x = singleton-type-center x , a
 where
  a : (σ : singleton-type x) → singleton-type-center x ≡ σ
  a (y , p) = singleton-type-centered x y p

retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → Y ◁ X → is-singleton X → is-singleton Y
retract-of-singleton (r , s , η) (c , φ) = r c , γ
 where
  γ : (y : codomain r) → r c ≡ y
  γ y = r c     ≡⟨ ap r (φ (s y)) ⟩
        r (s y) ≡⟨ η y ⟩
        y       ∎

invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
invertible f = Σ \g → (g ∘ f ∼ id) × (f ∘ g ∼ id)

fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → Y → 𝓤 ⊔ 𝓥 ̇
fiber f y = Σ \(x : domain f) → f x ≡ y

is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-equiv f = (y : codomain f) → is-singleton (fiber f y)

inverse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → (Y → X)
inverse f e y = pr₁ (center (fiber f y) (e y))

inverse-is-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                   → (y : Y) → f (inverse f e y) ≡ y
inverse-is-section f e y = pr₂ (center (fiber f y) (e y))

inverse-centrality : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f) (y : Y)
                   → (t : fiber f y) → (inverse f e y , inverse-is-section f e y) ≡ t
inverse-centrality f e y = centrality (fiber f y) (e y)

inverse-is-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                      → (x : X) → inverse f e (f x) ≡ x
inverse-is-retraction f e x = ap pr₁ (inverse-centrality f e (f x) (x , (refl (f x))))

equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → invertible f
equivs-are-invertible f e = (inverse f e , inverse-is-retraction f e , inverse-is-section f e)

invertibles-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → invertible f → is-equiv f
invertibles-are-equivs {𝓤} {𝓥} {X} {Y} f (g , η , ε) y₀ = γ
 where
  a : (y : Y) → (f (g y) ≡ y₀) ◁ (y ≡ y₀)
  a y = r , s , rs
   where
    r : y ≡ y₀ → f (g y) ≡ y₀
    r p = f (g y) ≡⟨ ε y ⟩
          y       ≡⟨ p ⟩
          y₀      ∎
    s : f (g y) ≡ y₀ → y ≡ y₀
    s q = y       ≡⟨ (ε y)⁻¹ ⟩
          f (g y) ≡⟨ q ⟩
          y₀      ∎
    rs : (q : f (g y) ≡ y₀) → r (s q) ≡ q
    rs q = ε y ∙ ((ε y)⁻¹ ∙ q) ≡⟨ (∙assoc (ε y) ((ε y)⁻¹) q)⁻¹ ⟩
           (ε y ∙ (ε y)⁻¹) ∙ q ≡⟨ ap (_∙ q) (⁻¹-right∙ (ε y)) ⟩
           refl (f (g y)) ∙ q  ≡⟨ refl-left ⟩
           q                   ∎
  b : fiber f y₀ ◁ singleton-type y₀
  b = (Σ \(x : X) → f x ≡ y₀)     ◁⟨ Σ-retract-reindexing g (f , η) ⟩
      (Σ \(y : Y) → f (g y) ≡ y₀) ◁⟨ Σ-retract Y (λ y → f (g y) ≡ y₀) (λ y → y ≡ y₀) a ⟩
      (Σ \(y : Y) → y ≡ y₀)       ◀
  γ : is-singleton (fiber f y₀)
  γ = retract-of-singleton b (singleton-types-are-singletons y₀)

inverse-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                 → is-equiv (inverse f e)
inverse-is-equiv f e = invertibles-are-equivs
                         (inverse f e)
                         (f , inverse-is-section f e , inverse-is-retraction f e)

id-invertible : (X : 𝓤 ̇ ) → invertible (id {𝓤} {X})
id-invertible X = id , refl , refl

∘-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {f' : Y → Z}
             → invertible f' → invertible f → invertible (f' ∘ f)
∘-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {f'} (g' , gf' , fg') (g , gf , fg)  = g ∘ g' , η , ε
 where
  η : (x : X) → g (g' (f' (f x))) ≡ x
  η x = g (g' (f' (f x))) ≡⟨ ap g (gf' (f x)) ⟩
        g (f x)           ≡⟨ gf x ⟩
        x                 ∎
  ε : (z : Z) → f' (f (g (g' z))) ≡ z
  ε z = f' (f (g (g' z))) ≡⟨ ap f' (fg (g' z)) ⟩
        f' (g' z)         ≡⟨ fg' z ⟩
        z                 ∎

id-is-equiv : (X : 𝓤 ̇ ) → is-equiv (id {𝓤} {X})
id-is-equiv X = singleton-types-are-singletons

∘-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
           → is-equiv g → is-equiv f → is-equiv (g ∘ f)
∘-is-equiv {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} i j = invertibles-are-equivs (g ∘ f)
                                                    (∘-invertible (equivs-are-invertible g i)
                                                                  (equivs-are-invertible f j))

_≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ≃ Y = Σ \(f : X → Y) → is-equiv f

Eq-to-fun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → X → Y
Eq-to-fun (f , e) = f

Eq-to-fun-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (e : X ≃ Y) → is-equiv (Eq-to-fun e)
Eq-to-fun-is-equiv (f , i) = i

≃-refl : (X : 𝓤 ̇ ) → X ≃ X
≃-refl X = id , id-is-equiv X

_●_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_●_ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} (f , d) (f' , e) = f' ∘ f , ∘-is-equiv e d

≃-sym : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ≃ Y → Y ≃ X
≃-sym (f , e) = inverse f e , inverse-is-equiv f e

_≃⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ≃ Y → Y ≃ Z → X ≃ Z
_ ≃⟨ d ⟩ e = d ● e

_■ : (X : 𝓤 ̇ ) → X ≃ X
_■ = ≃-refl

transport-is-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                   → is-equiv (transport A p)
transport-is-equiv A (refl x) = id-is-equiv (A x)

transport-≃ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
            → x ≡ y → A x ≃ A y
transport-≃ A p = transport A p , transport-is-equiv A p

transport-is-equiv' : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                    → is-equiv (transport A p)
transport-is-equiv' A p =
  invertibles-are-equivs
   (transport A p)
   (transport A (p ⁻¹) ,
    (λ a → transport A (p ⁻¹) (transport A p a) ≡⟨ (ap (λ - → - a) (transport∙ A p (p ⁻¹)))⁻¹ ⟩
           transport A (p ∙ p ⁻¹) a             ≡⟨ ap (λ - → transport A - a) (⁻¹-right∙ p) ⟩
           a                                    ∎) ,
     λ a → transport A p (transport A (p ⁻¹) a) ≡⟨ (ap (λ - → - a) (transport∙ A (p ⁻¹) p))⁻¹ ⟩
           transport A (p ⁻¹ ∙ p) a             ≡⟨ ap (λ - → transport A - a) (⁻¹-left∙ p) ⟩
           a                                    ∎)

Σ-≡-equivalence : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (σ τ : Σ A)
                → (σ ≡ τ) ≃ (Σ \(p : pr₁ σ ≡ pr₁ τ) → pr₂ σ ≡[ p / A ] pr₂ τ)
Σ-≡-equivalence  {𝓤} {𝓥} {X} {A}  σ τ = from-Σ-≡ ,
                                        invertibles-are-equivs from-Σ-≡ (to-Σ-≡ , ε , η)
 where
  η : (w : Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ) → from-Σ-≡ (to-Σ-≡ w) ≡ w
  η (refl p , refl q) = refl (refl p , refl q)
  ε : (q : σ ≡ τ) → to-Σ-≡ (from-Σ-≡ q) ≡ q
  ε (refl σ) = refl (refl σ)

Id-to-Eq : (X Y : 𝓤 ̇ ) → X ≡ Y → X ≃ Y
Id-to-Eq X X (refl X) = ≃-refl X

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → is-equiv (Id-to-Eq X Y)

Eq-to-Id : is-univalent 𝓤 → (X Y : 𝓤 ̇ ) → X ≃ Y → X ≡ Y
Eq-to-Id ua X Y = inverse (Id-to-Eq X Y) (ua X Y)

Id-to-fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-fun {𝓤} {X} {Y} p = Eq-to-fun (Id-to-Eq X Y p)

Id-to-fun' : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id-to-fun' = transport id

Id-to-funs-agree : {X Y : 𝓤 ̇ } (p : X ≡ Y)
                 → Id-to-fun p ≡ Id-to-fun' p
Id-to-funs-agree (refl X) = refl id

swap₂ : 𝟚 → 𝟚
swap₂ ₀ = ₁
swap₂ ₁ = ₀

swap₂-involutive : (n : 𝟚) → swap₂ (swap₂ n) ≡ n
swap₂-involutive ₀ = refl ₀
swap₂-involutive ₁ = refl ₁

swap₂-is-equiv : is-equiv swap₂
swap₂-is-equiv = invertibles-are-equivs swap₂ (swap₂ , swap₂-involutive , swap₂-involutive)

e₀ e₁ : 𝟚 ≃ 𝟚
e₀ = ≃-refl 𝟚
e₁ = swap₂ , swap₂-is-equiv

e₀-is-not-e₁ : e₀ ≢ e₁
e₀-is-not-e₁ p = ₁-is-not-₀ r
 where
  q : id ≡ swap₂
  q = ap pr₁ p
  r : ₁ ≡ ₀
  r = ap (λ - → - ₁) q

module _ (ua : is-univalent 𝓤₀) where

  p₀ p₁ : 𝟚 ≡ 𝟚
  p₀ = Eq-to-Id ua 𝟚 𝟚 e₀
  p₁ = Eq-to-Id ua 𝟚 𝟚 e₁

  p₀-is-not-p₁ : p₀ ≢ p₁
  p₀-is-not-p₁ q = e₀-is-not-e₁ r
   where
    r = e₀              ≡⟨ (inverse-is-section (Id-to-Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
        Id-to-Eq 𝟚 𝟚 p₀ ≡⟨ ap (Id-to-Eq 𝟚 𝟚) q ⟩
        Id-to-Eq 𝟚 𝟚 p₁ ≡⟨ inverse-is-section (Id-to-Eq 𝟚 𝟚) (ua 𝟚 𝟚) e₁ ⟩
        e₁              ∎

  𝓤₀-is-not-a-set :  ¬(is-set (𝓤₀ ̇ ))
  𝓤₀-is-not-a-set s = p₀-is-not-p₁ q
   where
    q : p₀ ≡ p₁
    q = s 𝟚 𝟚 p₀ p₁

left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
left-cancellable f = {x x' : domain f} → f x ≡ f x' → x ≡ x'

lc-maps-reflect-subsingletonness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → left-cancellable f
                                 → is-subsingleton Y
                                 → is-subsingleton X

has-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-retraction s = Σ \(r : codomain s → domain s) → r ∘ s ∼ id

sections-are-lc : {X : 𝓤 ̇ } {A : 𝓥 ̇ } (s : X → A) → has-retraction s → left-cancellable s

equivs-have-retractions : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-retraction f

equivs-have-sections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → has-section f

equivs-are-lc : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-equiv f → left-cancellable f

equiv-to-subsingleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → is-subsingleton Y
                      → is-subsingleton X

equiv-to-subsingleton' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → is-subsingleton X
                      → is-subsingleton Y

sections-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                        → has-retraction f
                        → g ∼ f
                        → has-retraction g

retractions-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                           → has-section f
                           → g ∼ f
                           → has-section g

is-joyal-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-joyal-equiv f = has-section f × has-retraction f

joyal-equivs-are-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                            → is-joyal-equiv f → invertible f

joyal-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-joyal-equiv f → is-equiv f

invertibles-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → invertible f → is-joyal-equiv f

equivs-are-joyal-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                        → is-equiv f → is-joyal-equiv f

equivs-closed-under-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                      → is-equiv f
                      → g ∼ f
                      → is-equiv g

equivs-closed-under-∼' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f g : X → Y)
                       → is-equiv f
                       → f ∼ g
                       → is-equiv g

≃-gives-◁ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → X ◁ Y

≃-gives-▷ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → Y ◁ X

equiv-to-singleton : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                   → X ≃ Y → is-singleton Y → is-singleton X

equiv-to-singleton' : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                   → X ≃ Y → is-singleton X → is-singleton Y

pr₁-equivalence : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ )
                → ((x : X) → is-singleton (A x))
                → is-equiv (λ (t : Σ A) → pr₁ t)

ΠΣ-distr-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {P : (x : X) → A x → 𝓦 ̇ }
           → (Π \(x : X) → Σ \(a : A x) → P x a) ≃ (Σ \(f : Π A) → Π \(x : X) → P x (f x))

Σ-cong : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
       → ((x : X) → A x ≃ B x) → Σ A ≃ Σ B

⁻¹-≃ : {X : 𝓤 ̇ } (x y : X) → (x ≡ y) ≃ (y ≡ x)

singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' x = Σ \y → x ≡ y

singleton-types-≃ : {X : 𝓤 ̇ } (x : X) → singleton-type' x ≃ singleton-type x

singleton-types-are-singletons' : {X : 𝓤 ̇ } (x : X) → is-singleton (singleton-type' x)

singletons-equivalent : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                      → is-singleton X → is-singleton Y → X ≃ Y

maps-of-singletons-are-equivs : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                              → is-singleton X → is-singleton Y → is-equiv f

NatΣ-fiber-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                 → (x : X) (b : B x) → fiber (φ x) b ≃ fiber (NatΣ φ) (x , b)

NatΣ-equiv-gives-fiberwise-equiv : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (φ : Nat A B)
                                 → is-equiv (NatΣ φ) → ((x : X) → is-equiv (φ x))

funext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ≡ g

transport-is-pre-comp : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (e : X ≃ Y) (g : Y → Z)
                      → transport (λ - → - → Z) ((Eq-to-Id ua X Y e)⁻¹) g ≡ g ∘ Eq-to-fun e

transport-is-pre-comp ua {X} {Y} {Z} e g = α e (Eq-to-Id ua X Y e) (refl (Eq-to-Id ua X Y e))
 where
  α : (e : X ≃ Y) (p : X ≡ Y)
    → p ≡ Eq-to-Id ua X Y e
    → transport (λ - → - → Z) (p ⁻¹) g ≡ g ∘ Eq-to-fun e
  α e (refl X) = γ
   where
    γ : refl X ≡ Eq-to-Id ua X X e → g ≡ g ∘ Eq-to-fun e
    γ q = ap (g ∘_) b
     where
      a : ≃-refl X ≡ e
      a = ≃-refl X                         ≡⟨ ap (Id-to-Eq X X) q ⟩
          Id-to-Eq X X (Eq-to-Id ua X X e) ≡⟨ inverse-is-section (Id-to-Eq X X) (ua X X) e ⟩
          e                                ∎
      b : id ≡ Eq-to-fun e
      b = ap Eq-to-fun a

pre-comp-is-equiv : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (f : X → Y)
                  → is-equiv f
                  → is-equiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv ua {X} {Y} {Z} f i = j
 where
  e : X ≃ Y
  e = (f , i)

  of-course : Eq-to-fun e ≡ f
  of-course = refl f

  φ γ : (Y → Z) → (X → Z)
  φ g = g ∘ f
  γ g = transport (λ - → - → Z) ((Eq-to-Id ua X Y e)⁻¹) g

  γ-is-equiv : is-equiv γ
  γ-is-equiv = transport-is-equiv (λ - → - → Z) ((Eq-to-Id ua X Y e)⁻¹)

  h' : (g : Y → Z) → transport (λ - → - → _) ((Eq-to-Id ua X Y e)⁻¹) g ≡ g ∘ Eq-to-fun e
  h' = transport-is-pre-comp ua e

  h : γ ∼ φ
  h = h'

  j : is-equiv φ
  j = equivs-closed-under-∼' γ φ γ-is-equiv h

pre-comp-is-equiv' : (ua : is-univalent 𝓤) {X Y Z : 𝓤 ̇ } (f : X → Y)
                   → is-equiv f
                   → is-equiv (λ (g : Y → Z) → g ∘ f)
pre-comp-is-equiv' ua {X} {Y} {Z} f i = equivs-closed-under-∼'
                                          (transport (λ - → - → Z) ((Eq-to-Id ua X Y (f , i))⁻¹))
                                          (_∘ f)
                                          (transport-is-equiv (λ - → - → Z) ((Eq-to-Id ua X Y (f , i))⁻¹))
                                          (transport-is-pre-comp ua (f , i))

univalence-gives-funext : is-univalent 𝓤 → funext 𝓥 𝓤
univalence-gives-funext ua {X} {Y} {f₀} {f₁} h = γ
 where
  Δ = Σ \(y₀ : Y) → Σ \(y₁ : Y) → y₀ ≡ y₁

  δ : Y → Δ
  δ y = (y , y , refl y)

  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁

  δ-is-equiv : is-equiv δ
  δ-is-equiv = invertibles-are-equivs δ (π₀ , η , ε)
   where
    η : (y : Y) → π₀ (δ y) ≡ y
    η y = refl y
    ε : (d : Δ) → δ (π₀ d) ≡ d
    ε (y , y , refl y) = refl (y , y , refl y)

  πδ : π₀ ∘ δ ≡ π₁ ∘ δ
  πδ = refl id

  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ

  φ-is-equiv : is-equiv φ
  φ-is-equiv = pre-comp-is-equiv ua δ δ-is-equiv

  π₀-equals-π₁ : π₀ ≡ π₁
  π₀-equals-π₁ = equivs-are-lc φ φ-is-equiv πδ

  γ : f₀ ≡ f₁
  γ = ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁

  γ' = f₀                              ≡⟨ refl _ ⟩
       (λ x → f₀ x)                    ≡⟨ refl _ ⟩
       (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁ ⟩
       (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl _ ⟩
       (λ x → f₁ x)                    ≡⟨ refl _ ⟩
       f₁                              ∎

dfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
dfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ≡ g

happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → f ≡ g → f ∼ g
happly f g p x = ap (λ - → - x) p

hfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
hfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly f g)

hfunext-gives-dfunext : hfunext 𝓤 𝓥 → dfunext 𝓤 𝓥
hfunext-gives-dfunext hfe {X} {A} {f} {g} = inverse (happly f g) (hfe f g)

vvfunext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → ((x : X) → is-singleton (A x)) → is-singleton (Π A)

dfunext-gives-vvfunext : dfunext 𝓤 𝓥 → vvfunext 𝓤 𝓥
dfunext-gives-vvfunext fe i = (λ x → pr₁ (i x)) , (λ f → fe (λ x → pr₂ (i x) (f x)))

post-comp-is-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
          → funext 𝓦 𝓤 → funext 𝓦 𝓥
          → (f : X → Y) → invertible f → invertible (λ (h : A → X) → f ∘ h)
post-comp-is-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} nfe nfe' f (g , η , ε) = (g' , η' , ε')
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = nfe (η ∘ h)
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = nfe' (ε ∘ k)

post-comp-is-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → funext 𝓦 𝓤 → funext 𝓦 𝓥
                   → (f : X → Y) → is-equiv f → is-equiv (λ (h : A → X) → f ∘ h)
post-comp-is-equiv fe fe' f e = invertibles-are-equivs
                                 (λ h → f ∘ h)
                                 (post-comp-is-invertible fe fe' f (equivs-are-invertible f e))

vvfunext-gives-hfunext : vvfunext 𝓤 𝓥 → hfunext 𝓤 𝓥
vvfunext-gives-hfunext {𝓤} {𝓥} vfe {X} {Y} f = γ
 where
  a : (x : X) → is-singleton (Σ \(y : Y x) → f x ≡ y)
  a x = singleton-types-are-singletons' (f x)
  c : is-singleton ((x : X) → Σ \(y : Y x) → f x ≡ y)
  c = vfe a
  R : (Σ \(g : Π Y) → f ∼ g) ◁ (Π \(x : X) → Σ \(y : Y x) → f x ≡ y)
  R = ≃-gives-▷ _ _ ΠΣ-distr-≃
  r : (Π \(x : X) → Σ \(y : Y x) → f x ≡ y) → Σ \(g : Π Y) → f ∼ g
  r = λ _ → f , (λ x → refl (f x))
  d : is-singleton (Σ \(g : Π Y) → f ∼ g)
  d = retract-of-singleton R c
  e : (Σ \(g : Π Y) → f ≡ g) → (Σ \(g : Π Y) → f ∼ g)
  e = NatΣ (happly f)
  i : is-equiv e
  i = maps-of-singletons-are-equivs (Σ (λ g → f ≡ g)) (Σ (λ g → f ∼ g)) e (singleton-types-are-singletons' f) d
  γ : (g : Π Y) → is-equiv (happly f g)
  γ = NatΣ-equiv-gives-fiberwise-equiv (λ g → f ≡ g) (λ g → f ∼ g) (happly f) i

funext-gives-vvfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → vvfunext 𝓤 𝓥
funext-gives-vvfunext {𝓤} {𝓥} fe fe' {X} {A} φ = retract-of-singleton (r , s , rs) i
  where
   f : Σ A → X
   f = pr₁
   f-is-equiv : is-equiv f
   f-is-equiv = pr₁-equivalence X A φ
   g : (X → Σ A) → (X → X)
   g h = f ∘ h
   g-is-equiv : is-equiv g
   g-is-equiv = post-comp-is-equiv fe fe' f f-is-equiv
   i : is-singleton (Σ \(h : X → Σ A) → f ∘ h ≡ id)
   i = g-is-equiv id
   r : (Σ \(h : X → Σ A) → f ∘ h ≡ id) → Π A
   r (h , p) x = transport A (happly (f ∘ h) id p x) (pr₂ (h x))
   s : Π A → (Σ \(h : X → Σ A) → f ∘ h ≡ id)
   s φ = (λ x → x , φ x) , refl id
   rs : ∀ φ → r (s φ) ≡ φ
   rs φ = refl (r (s φ))

funext-gives-hfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → hfunext 𝓤 𝓥
funext-gives-hfunext fe fe' = vvfunext-gives-hfunext (funext-gives-vvfunext fe fe')

funext-gives-dfunext : funext 𝓤 (𝓤 ⊔ 𝓥) → funext 𝓤 𝓤 → dfunext 𝓤 𝓥
funext-gives-dfunext fe fe' = hfunext-gives-dfunext (funext-gives-hfunext fe fe')

univalence-gives-hfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → hfunext 𝓤 𝓥
univalence-gives-hfunext' ua ua' = funext-gives-hfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

univalence-gives-vvfunext' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → vvfunext 𝓤 𝓥
univalence-gives-vvfunext' ua ua' = funext-gives-vvfunext
                                     (univalence-gives-funext ua')
                                     (univalence-gives-funext ua)

univalence-gives-hfunext : is-univalent 𝓤 → hfunext 𝓤 𝓤
univalence-gives-hfunext ua = univalence-gives-hfunext' ua ua

univalence-gives-dfunext : is-univalent 𝓤 → dfunext 𝓤 𝓤
univalence-gives-dfunext ua = hfunext-gives-dfunext (univalence-gives-hfunext ua)

univalence-gives-vvfunext : is-univalent 𝓤 → vvfunext 𝓤 𝓤
univalence-gives-vvfunext ua = univalence-gives-vvfunext' ua ua

Π-is-subsingleton : dfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  → ((x : X) → is-subsingleton (A x)) → is-subsingleton (Π A)
Π-is-subsingleton fe i f g = fe (λ x → i x (f x) (g x))

being-a-singleton-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-subsingleton (is-singleton X)
being-a-singleton-is-a-subsingleton fe {X} (x , φ) (y , γ) = to-Σ-≡ (φ y , fe (λ z → s y z _ _))
 where
  i : is-subsingleton X
  i = singletons-are-subsingletons X (y , γ)
  s : is-set X
  s = subsingletons-are-sets X i

being-an-equiv-is-a-subsingleton : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                                 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → is-subsingleton (is-equiv f)
being-an-equiv-is-a-subsingleton fe fe' f = Π-is-subsingleton fe (λ x → being-a-singleton-is-a-subsingleton fe')

univalence-is-a-subsingleton : is-univalent (𝓤 ⁺) → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingleton {𝓤} ua⁺ ua ua' = i ua ua'
 where
  fe₀ : funext 𝓤 𝓤
  fe₀ = univalence-gives-funext ua
  fe₁ : funext 𝓤 (𝓤 ⁺)
  fe₁ = univalence-gives-funext ua⁺
  fe₂ : funext (𝓤 ⁺) (𝓤 ⁺)
  fe₂ = univalence-gives-funext ua⁺
  dfe₁ : dfunext 𝓤 (𝓤 ⁺)
  dfe₁ = funext-gives-dfunext fe₁ fe₀
  dfe₂ : dfunext (𝓤 ⁺) (𝓤 ⁺)
  dfe₂ = funext-gives-dfunext fe₂ fe₂

  i : is-subsingleton (is-univalent 𝓤)
  i = Π-is-subsingleton dfe₂
       (λ X → Π-is-subsingleton dfe₂
               (λ Y → being-an-equiv-is-a-subsingleton dfe₁ dfe₂ (Id-to-Eq X Y)))

global-univalence : 𝓤ω
global-univalence = ∀ 𝓤 → is-univalent 𝓤

univalence-is-a-subsingleton₀ : global-univalence → is-subsingleton (is-univalent 𝓤)
univalence-is-a-subsingleton₀ {𝓤} α = univalence-is-a-subsingleton (α (𝓤 ⁺))

univalence-is-a-subsingleton₁ : global-univalence → is-singleton (is-univalent 𝓤)
univalence-is-a-subsingleton₁ {𝓤} α = pointed-subsingletons-are-singletons
                                        (is-univalent 𝓤)
                                        (α 𝓤)
                                        (univalence-is-a-subsingleton₀ α)

being-a-subsingleton-is-a-subsingleton : {X : 𝓤 ̇ } → dfunext 𝓤 𝓤 → is-subsingleton (is-subsingleton X)
being-a-subsingleton-is-a-subsingleton {𝓤} {X} fe i j = c
 where
  l : is-set X
  l = subsingletons-are-sets X i
  a : (x y : X) → i x y ≡ j x y
  a x y = l x y (i x y) (j x y)
  b : (x : X) → i x ≡ j x
  b x = fe (a x)
  c : i ≡ j
  c = fe b

Π-is-set : hfunext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set hfe s f g = b
 where
  a : is-subsingleton (f ∼ g)
  a p q = hfunext-gives-dfunext hfe ((λ x → s x (f x) (g x) (p x) (q x)))
  b : is-subsingleton(f ≡ g)
  b = equiv-to-subsingleton (happly f g) (hfe f g) a

being-set-is-a-subsingleton : dfunext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-subsingleton (is-set X)
being-set-is-a-subsingleton {𝓤} fe {X} = Π-is-subsingleton fe
                                          (λ x → Π-is-subsingleton fe
                                                  (λ y → being-a-subsingleton-is-a-subsingleton fe))

hlevel-relation-is-subsingleton : dfunext 𝓤 𝓤 → (n : ℕ) (X : 𝓤 ̇ ) → is-subsingleton (X is-of-hlevel n)
hlevel-relation-is-subsingleton {𝓤} fe zero     X = being-a-singleton-is-a-subsingleton fe
hlevel-relation-is-subsingleton {𝓤} fe (succ n) X = Π-is-subsingleton fe
                                                      (λ x → Π-is-subsingleton fe
                                                              (λ x' → hlevel-relation-is-subsingleton {𝓤} fe n (x ≡ x')))

𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
𝟚-has-𝟚-automorphisms fe =

 (f , invertibles-are-equivs f (g , η , ε))
 where
  f : (𝟚 ≃ 𝟚) → 𝟚
  f (h , e) = h ₀
  g : 𝟚 → (𝟚 ≃ 𝟚)
  g ₀ = id , id-is-equiv 𝟚
  g ₁ = swap₂ , swap₂-is-equiv
  η : (e : 𝟚 ≃ 𝟚) → g (f e) ≡ e
  η (h , e) = γ (h ₀) (h ₁) (refl (h ₀)) (refl (h ₁))
   where
    γ : (m n : 𝟚) → h ₀ ≡ m → h ₁ ≡ n → g (h ₀) ≡ (h , e)
    γ ₀ ₀ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₀   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))
    γ ₀ ₁ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₀) ₀     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₀) ₁     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)) ,
                being-an-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₀ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₁) ₀     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₁) ₁     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)) ,
                being-an-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₁ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₁   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))

  ε : (n : 𝟚) → f (g n) ≡ n
  ε ₀ = refl ₀
  ε ₁ = refl ₁

●-assoc : dfunext 𝓣 (𝓤 ⊔ 𝓣) → dfunext (𝓤 ⊔ 𝓣) (𝓤 ⊔ 𝓣) →
         {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {T : 𝓣 ̇ }
          (α : X ≃ Y) (β : Y ≃ Z) (γ : Z ≃ T)
        → α ● (β ● γ) ≡ (α ● β) ● γ
●-assoc fe fe' (f , a) (g , b) (h , c) = to-Σ-≡ (p , q)
 where
  p : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
  p = refl (h ∘ g ∘ f)

  d e : is-equiv (h ∘ g ∘ f)
  d = ∘-is-equiv (∘-is-equiv c b) a
  e = ∘-is-equiv c (∘-is-equiv b a)

  q : transport is-equiv p d ≡ e
  q = being-an-equiv-is-a-subsingleton fe fe' (h ∘ g ∘ f) _ _

inversion-involutive : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (e : is-equiv f)
                     → inverse (inverse f e) (inverse-is-equiv f e) ≡ f
inversion-involutive f e = refl f

≃-sym-involutive : dfunext 𝓥 (𝓤 ⊔ 𝓥) → dfunext (𝓥 ⊔ 𝓤) (𝓥 ⊔ 𝓤) →
                   {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (α : X ≃ Y)
                 → ≃-sym (≃-sym α) ≡ α
≃-sym-involutive fe fe' (f , a) = to-Σ-≡ (inversion-involutive f a ,
                                          being-an-equiv-is-a-subsingleton fe fe' f _ _)

is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P

global-dfunext : 𝓤ω
global-dfunext = ∀ 𝓤 𝓥 → dfunext 𝓤 𝓥

inhabitation-is-a-subsingleton : global-dfunext → (X : 𝓤 ̇ ) → is-subsingleton (is-inhabited X)
inhabitation-is-a-subsingleton {𝓤} fe X =
  Π-is-subsingleton (fe (𝓤 ⁺) 𝓤)
    λ P → Π-is-subsingleton (fe 𝓤 𝓤)
           (λ (s : is-subsingleton P)
                 → Π-is-subsingleton (fe 𝓤 𝓤) (λ (f : X → P) → s))

pointed-is-inhabited : (X : 𝓤 ̇ ) → X → is-inhabited X
pointed-is-inhabited X x = λ P s f → f x

inhabited-recursion : (X P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion X P s f φ = φ P s f

inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ ) → is-subsingleton P → is-inhabited P → P
inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s id

∃ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → (𝓤 ⊔ 𝓥)⁺ ̇
∃ {𝓤} {𝓥} {X} A = is-inhabited (Σ \(x : X) → A x)

image : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image f = Σ \(y : codomain f) → ∃ \(x : domain f) → f x ≡ y

restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇} (f : X → Y)
            → image f → Y
restriction f (y , _) = y

corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇} (f : X → Y)
            → X → image f
corestriction f x = f x , pointed-is-inhabited (fiber f (f x)) (x , refl (f x))

is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇} → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection f = (y : codomain f) → ∃ \(x : domain f) → f x ≡ y

record propositional-truncations-exist : 𝓤ω where
 field
  ∥_∥ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-a-prop : {𝓤 : Universe} {X : 𝓤 ̇ } → is-prop ∥ X ∥
  ∣_∣ : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇} → is-prop P → (X → P) → ∥ X ∥ → P

lc-maps-reflect-subsingletonness f l s x x' = l (s (f x) (f x'))

sections-are-lc s (r , ε) {x} {y} p = x       ≡⟨ (ε x)⁻¹ ⟩
                                      r (s x) ≡⟨ ap r p ⟩
                                      r (s y) ≡⟨ ε y ⟩
                                      y       ∎

equivs-have-retractions f e = (inverse f e , inverse-is-retraction f e)

equivs-have-sections f e = (inverse f e , inverse-is-section f e)

equivs-are-lc f e = sections-are-lc f (equivs-have-retractions f e)

equiv-to-subsingleton f e = lc-maps-reflect-subsingletonness f (equivs-are-lc f e)

equiv-to-subsingleton' f e = lc-maps-reflect-subsingletonness
                               (inverse f e)
                               (equivs-are-lc (inverse f e) (inverse-is-equiv f e))

sections-closed-under-∼ f g (r , rf) h = (r ,
                                          λ x → r (g x) ≡⟨ ap r (h x) ⟩
                                                r (f x) ≡⟨ rf x ⟩
                                                x       ∎)

retractions-closed-under-∼ f g (s , fs) h = (s ,
                                             λ y → g (s y) ≡⟨ h (s y) ⟩
                                                   f (s y) ≡⟨ fs y ⟩
                                                   y ∎)

joyal-equivs-are-invertible f ((s , fs) , (r , rf)) = (s , sf , fs)
 where
  sf = λ (x : domain f) → s(f x)       ≡⟨ (rf (s (f x)))⁻¹ ⟩
                          r(f(s(f x))) ≡⟨ ap r (fs (f x)) ⟩
                          r(f x)       ≡⟨ rf x ⟩
                          x            ∎

joyal-equivs-are-equivs f j = invertibles-are-equivs f (joyal-equivs-are-invertible f j)

invertibles-are-joyal-equivs f (g , gf , fg) = ((g , fg) , (g , gf))

equivs-are-joyal-equivs f e = invertibles-are-joyal-equivs f (equivs-are-invertible f e)

equivs-closed-under-∼ f g e h = joyal-equivs-are-equivs g
                                 (retractions-closed-under-∼ f g (equivs-have-sections f e) h ,
                                  sections-closed-under-∼ f g (equivs-have-retractions f e) h)

equivs-closed-under-∼' f g e h = equivs-closed-under-∼ f g e (λ x → (h x)⁻¹)

≃-gives-◁ X Y (f , e) = (inverse f e , f , inverse-is-retraction f e)

≃-gives-▷ X Y (f , e) = (f , inverse f e , inverse-is-section f e)

equiv-to-singleton X Y e = retract-of-singleton (≃-gives-◁ X Y e)

equiv-to-singleton' X Y e = retract-of-singleton (≃-gives-▷ X Y e)

pr₁-equivalence {𝓤} {𝓥} X A s = invertibles-are-equivs pr₁ (g , η , ε)
 where
  g : X → Σ A
  g x = x , pr₁(s x)
  ε : (x : X) → pr₁ (g x) ≡ x
  ε x = refl (pr₁ (g x))
  η : (σ : Σ A) → g (pr₁ σ) ≡ σ
  η (x , a) = to-Σ-≡ (ε x , singletons-are-subsingletons (A x) (s x) _ a)

ΠΣ-distr-≃ {𝓤} {𝓥} {𝓦} {X} {A} {P} = φ , invertibles-are-equivs φ (γ , η , ε)
 where
  φ : (Π \(x : X) → Σ \(a : A x) → P x a) → Σ \(f : Π A) → Π \(x : X) → P x (f x)
  φ g = ((λ x → pr₁ (g x)) , λ x → pr₂ (g x))

  γ : (Σ \(f : Π A) → Π \(x : X) → P x (f x)) → Π \(x : X) → Σ \(a : A x) → P x a
  γ (f , φ) x = f x , φ x
  η : γ ∘ φ ∼ id
  η = refl
  ε : φ ∘ γ ∼ id
  ε = refl

Σ-cong {𝓤} {𝓥} {𝓦} {X} {A} {B} φ = (NatΣ f , invertibles-are-equivs (NatΣ f) (NatΣ g , NatΣ-η , NatΣ-ε))
 where
  f : (x : X) → A x → B x
  f x = Eq-to-fun (φ x)
  g : (x : X) → B x → A x
  g x = inverse (f x) (Eq-to-fun-is-equiv (φ x))
  η : (x : X) (a : A x) → g x (f x a) ≡ a
  η x = inverse-is-retraction (f x) (Eq-to-fun-is-equiv (φ x))
  ε : (x : X) (b : B x) → f x (g x b) ≡ b
  ε x = inverse-is-section (f x) (Eq-to-fun-is-equiv (φ x))

  NatΣ-η : (w : Σ A) → NatΣ g (NatΣ f w) ≡ w
  NatΣ-η (x , a) = x , g x (f x a) ≡⟨ ap (λ - → x , -) (η x a) ⟩
                   x , a           ∎

  NatΣ-ε : (t : Σ B) → NatΣ f (NatΣ g t) ≡ t
  NatΣ-ε (x , b) = x , f x (g x b) ≡⟨ ap (λ - → x , -) (ε x b) ⟩
                   x , b           ∎

⁻¹-≃ x y = (_⁻¹ , invertibles-are-equivs _⁻¹ (_⁻¹ , ⁻¹-involutive , ⁻¹-involutive))

singleton-types-≃ x = Σ-cong (λ y → ⁻¹-≃ x y)

singleton-types-are-singletons' x = equiv-to-singleton
                                      (singleton-type' x)
                                      (singleton-type x)
                                      (singleton-types-≃ x)
                                      (singleton-types-are-singletons x)

singletons-equivalent X Y i j = f , invertibles-are-equivs f (g , η , ε)
 where
  f : X → Y
  f x = center Y j
  g : Y → X
  g y = center X i
  η : (x : X) → g (f x) ≡ x
  η = centrality X i
  ε : (y : Y) → f (g y) ≡ y
  ε = centrality Y j

maps-of-singletons-are-equivs X Y f i j = invertibles-are-equivs f (g , η , ε)
 where
  g : Y → X
  g y = center X i
  η : (x : X) → g (f x) ≡ x
  η = centrality X i
  ε : (y : Y) → f (g y) ≡ y
  ε y = singletons-are-subsingletons Y j (f (g y)) y

NatΣ-fiber-equiv A B φ x b = (f , invertibles-are-equivs f (g , ε , η))
 where
  f : fiber (φ x) b → fiber (NatΣ φ) (x , b)
  f (a , refl _) = ((x , a) , refl (x , φ x a))
  g : fiber (NatΣ φ) (x , b) → fiber (φ x) b
  g ((x , a) , refl _) = (a , refl (φ x a))
  ε : (w : fiber (φ x) b) → g (f w) ≡ w
  ε (a , refl _) = refl (a , refl (φ x a))
  η : (t : fiber (NatΣ φ) (x , b)) → f (g t) ≡ t
  η ((x , a) , refl _) = refl ((x , a) , refl (NatΣ φ (x , a)))

NatΣ-equiv-gives-fiberwise-equiv A B φ e x b = γ
 where
  γ : is-singleton (fiber (φ x) b)
  γ = equiv-to-singleton
         (fiber (φ x) b)
         (fiber (NatΣ φ) (x , b))
         (NatΣ-fiber-equiv A B φ x b)
         (e (x , b))

succ-no-fixed-point : (n : ℕ) → succ n ≢ n

positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)

data Up {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 up : X → Up 𝓥 X

Up-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇) (A : Up 𝓥 X → 𝓦 ̇)
             → ((x : X) → A (up x))
             → ((l : Up 𝓥 X) → A l)

Up-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇} {B : 𝓦 ̇}
             → (X → B) → Up 𝓥 X → B

down : {X : 𝓤 ̇} → Up 𝓥 X → X

down-up : {X : 𝓤 ̇} (x : X) → down {𝓤} {𝓥} (up x) ≡ x

up-down : {X : 𝓤 ̇} (l : Up 𝓥 X) → up (down l) ≡ l

Up-≃ : (X : 𝓤 ̇) → Up 𝓥 X ≃ X
Up-≃ {𝓤} {𝓥} X = down {𝓤} {𝓥} , invertibles-are-equivs down (up , up-down , down-up {𝓤} {𝓥})

Up-left-≃ : (X : 𝓤 ̇) (Y : 𝓥 ̇) → X ≃ Y → Up 𝓦 X ≃ Y

ap-Up-≃ : (X : 𝓤 ̇) (Y : 𝓥 ̇) → X ≃ Y → Up 𝓦 X ≃ Up 𝓣 Y

DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇) → is-subsingleton P → ¬¬ P → P

neg-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇) → is-subsingleton (¬ X)

emsanity : dfunext 𝓤 𝓤₀ → (P : 𝓤 ̇) → is-subsingleton P → is-subsingleton (P + ¬ P)

ne : (X : 𝓤 ̇) → ¬¬(X + ¬ X)

DNE-gives-EM : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤

EM-gives-DNE : EM 𝓤 → DNE 𝓤

SN : ∀ 𝓤 → 𝓤 ⁺ ̇
SN 𝓤 = (P : 𝓤 ̇) → is-subsingleton P → Σ \(X : 𝓤 ̇) → P ⇔ ¬ X

SN-gives-DNE : SN 𝓤 → DNE 𝓤

DNE-gives-SN : DNE 𝓤 → SN 𝓤

infixr 4 _,_
infixr 2 _×_
infixr 1 _+_
infixl 5 _∘_
infix  0 _≡_
infixl 2 _∙_
infix  3  _⁻¹
infixr 0 _≡⟨_⟩_
infix  1 _∎
infix  4  _∼_
infix  0 _◁_
infix  1 _◀
infixr 0 _◁⟨_⟩_
infix  0 _≃_
infixl 2 _●_
infixr 0 _≃⟨_⟩_
infix  1 _■

succ-no-fixed-point 0        = positive-not-zero 0
succ-no-fixed-point (succ n) = γ
 where
  IH : succ n ≢ n
  IH = succ-no-fixed-point n
  γ : succ (succ n) ≢ succ n
  γ p = IH (succ-lc p)

positive-cantors-diagonal e = (α , φ)
 where
  α : ℕ → ℕ
  α n = succ(e n n)
  φ : (n : ℕ) → α ≢ e n
  φ n p = succ-no-fixed-point (e n n) q
   where
    q = succ (e n n)  ≡⟨ refl (α n) ⟩
        α n           ≡⟨ ap (λ - → - n) p ⟩
        e n n         ∎

cantors-diagonal (e , γ) = c
 where
  α :  ℕ → ℕ
  α = pr₁ (positive-cantors-diagonal e)
  φ : (n : ℕ) → α ≢ e n
  φ = pr₂ (positive-cantors-diagonal e)
  b : Σ \(n : ℕ) → α ≡ e n
  b = γ α
  c : 𝟘
  c = φ (pr₁ b) (pr₂ b)

Up-induction 𝓥 X A φ (up x) = φ x

Up-recursion 𝓥 {X} {B} = Up-induction 𝓥 X (λ _ → B)

down = Up-recursion _ id

down-up = refl

up-down {𝓤} {𝓥} {X} = Up-induction 𝓥 X
                        (λ l → up (down l) ≡ l)
                        (λ x → up (down {𝓤} {𝓥} (up x)) ≡⟨ ap up (down-up {𝓤} {𝓥}x) ⟩
                               up x                      ∎)

Up-left-≃ {𝓤} {𝓥} {𝓦} X Y e = Up 𝓦 X ≃⟨ Up-≃ X ⟩
                                X    ≃⟨ e ⟩
                                Y    ■

ap-Up-≃ {𝓤} {𝓥} {𝓦} {𝓣} X Y e = Up 𝓦 X  ≃⟨ Up-left-≃ X Y e ⟩
                                 Y      ≃⟨ ≃-sym (Up-≃ Y) ⟩
                                 Up 𝓣 Y ■

neg-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))

emsanity fe P i (inl p) (inl q) = ap inl (i p q)
emsanity fe P i (inl p) (inr n) = !𝟘 (inl p ≡ inr n) (n p)
emsanity fe P i (inr m) (inl q) = !𝟘 (inr m ≡ inl q) (m q)
emsanity fe P i (inr m) (inr n) = ap inr (neg-is-subsingleton fe P m n)

ne X = λ (f : ¬(X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM fe dne P i = dne (P + ¬ P) (emsanity fe P i) (ne P)

EM-gives-DNE em P i = γ (em P i)
 where
  γ : P + ¬ P → ¬¬ P → P
  γ (inl p) φ = p
  γ (inr n) φ = !𝟘 P (φ n)

SN-gives-DNE {𝓤} sn P i = h
 where
  X : 𝓤 ̇
  X = pr₁ (sn P i)
  f : P → ¬ X
  f = pr₁ (pr₂ (sn P i))
  g : ¬ X → P
  g = pr₂ (pr₂ (sn P i))
  f' : ¬¬ P → ¬(¬¬ X)
  f' = contrapositive (contrapositive f)
  h : ¬¬ P → P
  h = g ∘ tno ∘ f'
  h' : ¬¬ P → P
  h' φ = g (λ (x : X) → φ (λ (p : P) → f p x))

DNE-gives-SN dne P i = (¬ P) , dni , dne P i

