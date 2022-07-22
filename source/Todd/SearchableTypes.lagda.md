```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}


open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module Todd.SearchableTypes (fe : FunExt) (pe : PropExt) where

open import MLTT.Two-Properties hiding (zero-is-not-one)
open import Naturals.Order
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import DedekindReals.IntegersB
open import DedekindReals.IntegersOrder
open import DedekindReals.IntegersAddition renaming (_+_ to _+ℤ_)
open import DedekindReals.IntegersNegation renaming (-_  to  −ℤ_)
open import UF.Subsingletons
open import Naturals.Order
open import NotionsOfDecidability.DecidableAndDetachable
open import UF.Equiv
open import UF.Subsingletons-FunExt
open import Todd.TernaryBoehmRealsPrelude fe
open import Todd.InfiniteSearch1 (dfunext (fe _ _))
  hiding (predicate;everywhere-decidable;decidable;trivial-predicate)

nonempty : 𝓤 ̇ → 𝓤 ̇ 
nonempty = id

```

We start with decidable predicates on a given type.

```agda
everywhere-prop-valued : {𝓦 𝓤 : Universe} {X : 𝓤 ̇}
                       → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ̇
everywhere-prop-valued {𝓦} {𝓤} {X} p 
 = Π x ꞉ X , is-prop (p x)

predicate : {𝓦 𝓤 : Universe} {X : 𝓤 ̇} → (𝓦 ⁺) ⊔ 𝓤 ̇
predicate {𝓦} {𝓤} {X} 
 = Σ p ꞉ (X → 𝓦 ̇ ) , everywhere-prop-valued p

everywhere-decidable : {𝓦 𝓤 : Universe} {X : 𝓤 ̇}
                     → (X → 𝓦 ̇ ) → 𝓦 ⊔ 𝓤 ̇
everywhere-decidable {𝓦} {𝓤} {X} p
 = Π x ꞉ X , decidable (p x)

decidable-predicate : {𝓦 𝓤 : Universe} → 𝓤 ̇ → (𝓦 ⁺) ⊔ 𝓤 ̇
decidable-predicate {𝓦} {𝓤} X
 = Σ p ꞉ (X → 𝓦 ̇ )
 , everywhere-decidable p × everywhere-prop-valued p
```

Some predicates use equivalence relations to determine
information about the predicate.

We define equivalence relations in the usual way.

```agda
record equivalence-relation {𝓥 𝓤 : Universe} (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇
  where field
    _≣_ : X → X → 𝓥 ̇
    ≣-refl  : (x     : X) → x ≣ x
    ≣-sym   : (x y   : X) → x ≣ y → y ≣ x
    ≣-trans : (x y z : X) → x ≣ y → y ≣ z → x ≣ z

open equivalence-relation

_≣⟨_⟩_ : {𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
       → X → equivalence-relation {𝓥} X → X → 𝓥 ̇
x ≣⟨ A ⟩ y = _≣_ A x y
```

The class of predicates quotiented (?) by a particular
equivalence relation is defined as follows.

```agda
_informs_ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
          → equivalence-relation {𝓥} X
          → decidable-predicate {𝓦} X → 𝓦 ⊔ 𝓤 ⊔ 𝓥 ̇
A informs (p , _) = ∀ x y → x ≣A y → p x → p y
 where _≣A_ = _≣_ A

p⟨_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
       → (A : equivalence-relation {𝓥} X) → Σ (A informs_)
       → (X → 𝓦 ̇ )
p⟨ _ - ((p , _ , _) , _) ⟩ = p

d⟨_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
       → (A : equivalence-relation {𝓥} X)
       → (pdiϕ : Σ (_informs_ {𝓦} A))
       → everywhere-decidable p⟨ A - pdiϕ ⟩
d⟨ _ - ((_ , d , _) , _) ⟩ = d

i⟨_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
       → (A : equivalence-relation {𝓥} X)
       → (pdiϕ : Σ (_informs_ {𝓦} A))
       → everywhere-prop-valued p⟨ A - pdiϕ ⟩
i⟨ _ - ((_ , _ , i) , _) ⟩ = i

ϕ⟨_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
       → (A : equivalence-relation {𝓥} X)
       → (pdiϕ : Σ (_informs_ {𝓦} A))
       → (x y : X) → _≣_ A x y → p⟨ A - pdiϕ ⟩ x → p⟨ A - pdiϕ ⟩ y
ϕ⟨ _ - ((_ , _ , _) , ϕ) ⟩ = ϕ

decidable-predicate-informed-by
 : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
 → equivalence-relation {𝓥} X
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
decidable-predicate-informed-by {𝓦} {𝓤} {𝓥} {X} A
 = Σ p ꞉ decidable-predicate {𝓦} X , A informs p
```

Trivially, identity informs every predicate.

```agda
Identity : (X : 𝓤 ̇ ) → equivalence-relation {𝓤} {𝓤} X
_≣_     (Identity X)       = _＝_
≣-refl  (Identity X) x     = refl
≣-sym   (Identity X) x y   = _⁻¹
≣-trans (Identity X) x y z = _∙_

Id-informs-everything : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                      → (p : decidable-predicate {𝓦} X)
                      → Identity X informs p
Id-informs-everything p x x refl = id
```

Therefore, decidable predicates on X are equivalent to decidable
predicates on X informed by identity; the quotienting by _＝_ does not
remove any decidable predicates.

```agda
informs-is-prop : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
                → (A : equivalence-relation {𝓥} X)
                → (p : decidable-predicate {𝓦} X)
                → is-prop (A informs p)
informs-is-prop A (p , _ , i)
 = Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _)
       (λ y → Π-is-prop (fe _ _)
         (λ _ → Π-is-prop (fe _ _)
           (λ _ → i y))))

to-subtype-≃ : {X : 𝓦 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → A x × is-prop (A x))
             → X ≃ Σ A
to-subtype-≃ {_} {_} {X} {A} fi
 = (λ x → x , f x)
 , ((pr₁ , λ (x , Ax) → ap (x ,_) (i x (f x) Ax))
 , ( pr₁ , λ _ → refl))
 where
   f = λ x → pr₁ (fi x)
   i = λ x → pr₂ (fi x)

to-subtype-≃' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓥' ̇ }
              → ((x : X) → A x → B x)
              → ((x : X) → B x → A x)
              → ((x : X) → is-prop (A x))
              → ((x : X) → is-prop (B x))
              → Σ A ≃ Σ B
to-subtype-≃' f' g' i j
 = f
 , (g , (λ (x , Bx) → to-subtype-＝ j refl))
 , (g , (λ (x , Ax) → to-subtype-＝ i refl))
 where
   f = λ (x , Ax) → x , (f' x Ax)
   g = λ (x , Bx) → x , (g' x Bx)

decidable-predicate-≃ : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                      → decidable-predicate  {𝓦} X
                      ≃ decidable-predicate-informed-by {𝓦} (Identity X)
decidable-predicate-≃ {𝓦} {𝓤} {X}
 = to-subtype-≃
     (λ p → Id-informs-everything p , informs-is-prop (Identity X) p)
```

We can also define a trivial equivalence relation that identifies
everything.

```agda
Trivial : {𝓥 𝓤 : Universe} (X : 𝓤 ̇ ) → equivalence-relation {𝓥} {𝓤} X
_≣_     (Trivial X)           = λ _ _ → 𝟙
≣-refl  (Trivial X) x         = ⋆
≣-sym   (Trivial X) x y   _   = ⋆ 
≣-trans (Trivial X) x y z _ _ = ⋆ 
```

The trivial predicate that satisfies everything, and the empty
predicate that satisfies nothing, is informed by the trivial
equivalence relation.

```agda
trivial-predicate : {𝓦 𝓤 : Universe} → (X : 𝓤 ̇ )
                  → decidable-predicate {𝓦} X
trivial-predicate X = (λ x → 𝟙) , (λ x → inl ⋆)    , (λ x → 𝟙-is-prop)

empty-predicate : {𝓦 𝓤 : Universe} → (X : 𝓤 ̇ )
                → decidable-predicate {𝓦} X
empty-predicate   X = (λ x → 𝟘) , (λ x → inr λ ()) , (λ x → 𝟘-is-prop)

Trivial-informs-trivial
 : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
 → (Trivial {𝓥} X) informs trivial-predicate {𝓦} X
Trivial-informs-trivial _ _ _ _ = ⋆

Trivial-informs-empty
 : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
 → (Trivial {𝓥} X) informs empty-predicate {𝓦} X
Trivial-informs-empty _ _ _ ()

trivial-not-empty : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                  → nonempty X
                  → trivial-predicate {𝓦} X
                  ≢   empty-predicate {𝓦} X
trivial-not-empty {𝓦} {𝓤} {X} x t＝e = ¬px ⋆
 where
   ¬px : ¬ pr₁ (trivial-predicate {𝓦} X) x
   ¬px = transport (λ - → ¬ (pr₁ -) x) (t＝e ⁻¹) λ ()
```

In fact, these are the *only* predicates informed by the trivial
equivalence relation.

```agda
use-propext : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
            → (p p' : X → 𝓦 ̇ )
            → everywhere-prop-valued p
            → everywhere-prop-valued p'
            → ((x : X) → p x ⇔ p' x)
            → p ＝ p'
use-propext {𝓦} p p' i i' γ
 = dfunext (fe _ _) (λ x → pe 𝓦 (i x) (i' x) (pr₁ (γ x)) (pr₂ (γ x)))

¬-is-prop : {X : 𝓤 ̇ } → is-prop (¬ X)
¬-is-prop = Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop)

everywhere-decidable-is-prop : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                             → (p : X → 𝓦 ̇ )
                             → everywhere-prop-valued p
                             → is-prop (everywhere-decidable p)
everywhere-decidable-is-prop p i
 = Π-is-prop (fe _ _)
     (λ x → +-is-prop (i x) ¬-is-prop (λ px ¬px → ¬px px))

is-prop-is-prop : {X : 𝓤 ̇ } → is-prop X → is-prop (is-prop X)
is-prop-is-prop i
 = Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _) (λ _ → props-are-sets i))

everywhere-prop-valued-is-prop : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                               → (p : X → 𝓦 ̇ )
                               → everywhere-prop-valued p
                               → is-prop (everywhere-prop-valued p)
everywhere-prop-valued-is-prop p i
 = Π-is-prop (fe _ _) (λ x → is-prop-is-prop (i x))

decidable-predicate-＝
 : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
 → ((p , d , i) (p' , d' , i') : decidable-predicate {𝓦} X)
 → ((x : X) → p x ⇔ p' x)
 → (p , d , i) ＝ (p' , d' , i')
decidable-predicate-＝ (p , d , i) (p' , d' , i') γ
 = to-subtype-＝
     (λ p (pd , pi) (pd' , pi')
      → ×-is-prop
          (everywhere-decidable-is-prop p pi)
          (everywhere-prop-valued-is-prop p pi)
          (pd , pi) (pd' , pi'))
     (use-propext p p' i i' γ)
```

Any predicate on 𝟘 is empty.

```agda
predicate-on-𝟘-is-empty : (p : decidable-predicate {𝓦} (𝟘 {𝓤}))
                        → p ＝ empty-predicate {𝓦} (𝟘 {𝓤})
predicate-on-𝟘-is-empty (p , d , i)
 = decidable-predicate-＝ (p , d , i) (empty-predicate 𝟘) (λ ())

constant-predicate : {𝓦 𝓤 : Universe} (X : 𝓤 ̇ ) → (𝓦 ⁺) ⊔ 𝓤 ̇
constant-predicate {𝓦} {𝓤} X
 = Σ (p , _) ꞉ decidable-predicate {𝓦} X
 , ((x : X) → p x) + ((x : X) → ¬ p x)

constant-predicates-are-trivial-or-empty
 : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
 → ((p , _) : constant-predicate {𝓦} X)
 → (x : X)
 → (p ＝ trivial-predicate {𝓦} X) + (p ＝ empty-predicate {𝓦} X)
constant-predicates-are-trivial-or-empty {𝓦} {𝓥} {𝓤} {X}
 ((p , d , i) , (inl f)) x
 = inl (decidable-predicate-＝ (p , d , i) (trivial-predicate X)
         (λ x → (λ _ → ⋆) , (λ _ → f x)))
constant-predicates-are-trivial-or-empty {𝓦} {𝓥} {𝓤} {X}
 ((p , d , i) , (inr g)) x
 = inr (decidable-predicate-＝ (p , d , i) (empty-predicate   X)
         (λ x → 𝟘-elim ∘ g x , λ ()))
         
trivial-no-info
 : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ } → (x : X)
 → constant-predicate {𝓦} X
 ≃ decidable-predicate-informed-by {𝓦} (Trivial {𝓥} X)
trivial-no-info x
 = to-subtype-≃'
     (λ (p , d , i) → cases
       (λ f _ y _ _  → f y)
       (λ g x _ _ px → 𝟘-elim (g x px)))
     (λ (p , d , i) Tp → Cases (d x)
       (λ  px → inl (λ y    →      Tp x y ⋆ px))
       (λ ¬px → inr (λ y py → ¬px (Tp y x ⋆ py))))
     (λ (p , d , i) → +-is-prop
       (Π-is-prop (fe _ _) i)
       (Π-is-prop (fe _ _) (λ _ → ¬-is-prop))
       (λ f g → g x (f x)))
     (informs-is-prop (Trivial _))
```

So quotienting a universe of predicates on X by identity does nothing,
and doing so by the trivial equivalence relation removes every
non-constant predicate.

Let's look at some other equivalence relations and see what predicates
fall out of the quotienting.

So-called 'continuous' predicates as defined by closeness functions
are informed by a particular equivalence relation.

First, recall our definition of closeness functions.

```agda
record closeness-function (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    c : X × X → ℕ∞ 
    eic : (x     : X) → c (x , x) ＝ ∞
    ice : (x y   : X) → c (x , y) ＝ ∞ → x ＝ y
    sym : (x y   : X) → c (x , y) ＝ c (y , x)
    ult : (x y z : X) → min (c (x , y)) (c (y , z)) ≼ c (x , z)

open closeness-function
open is-clofun

≼-min : ∀ x y z → x ≼ y → x ≼ z → x ≼ min y z
≼-min x y z x≼y x≼z n r = Lemma[a＝₁→b＝₁→min𝟚ab＝₁] (x≼y n r) (x≼z n r)

≼-trans : ∀ x y z → x ≼ y → y ≼ z → x ≼ z
≼-trans x y z p q n = q n ∘ p n

_-Close-via_ : {X : 𝓤 ̇ } (δ : ℕ) → closeness-function X
             → equivalence-relation X
_≣_     (δ -Close-via C) x y
 = (δ ↑) ≼ c C (x , y)
≣-refl  (δ -Close-via C) x
 = transport ((δ ↑) ≼_) (eic C x ⁻¹) (∞-maximal (δ ↑))
≣-sym   (δ -Close-via C) x y
 = transport ((δ ↑) ≼_) (sym C x y)
≣-trans (δ -Close-via C) x y z δ≼cxy δ≼cyz
 = ≼-trans (δ ↑) (min (c C (x , y)) (c C (y , z))) (c C (x , z))
     (≼-min (δ ↑) (c C (x , y)) (c C (y , z)) δ≼cxy δ≼cyz)
     (ult C x y z)
```

Continuous predicates are those for which there is some δ : ℕ
such that the equivalence relation of being δ-close via any
closeness function informs the predicate.

```agda
continuous-predicate : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                     → closeness-function X → (𝓦 ⁺) ⊔ 𝓤 ̇
continuous-predicate {𝓦} C
 = Σ δ ꞉ ℕ , decidable-predicate-informed-by {𝓦} (δ -Close-via C)

minℕ : ℕ → ℕ → ℕ
minℕ 0 0 = 0
minℕ 0 (succ y) = 0
minℕ (succ x) 0 = 0
minℕ (succ x) (succ y) = succ (minℕ x y)

min-preserves-min' : (a b : ℕ)
                   → pr₁ (minℕ a b ↑) ∼ pr₁ (min (a ↑) (b ↑))
min-preserves-min' 0        0        _ = refl
min-preserves-min' 0        (succ b) _ = refl
min-preserves-min' (succ a) 0        _ = Lemma[min𝟚ab＝₀] (inr refl) ⁻¹
min-preserves-min' (succ a) (succ b) 0 = refl
min-preserves-min' (succ a) (succ b) (succ i)
 = min-preserves-min' a b i

min-preserves-min : (a b : ℕ) → minℕ a b ↑ ＝ min (a ↑) (b ↑)
min-preserves-min a b = ℕ∞-equals (min-preserves-min' a b)

-- not sure about this. maybe we shouldnt have the sigma type in there

{-
Continuous-via : {X : 𝓤 ̇ } → closeness-function X
               → equivalence-relation X
_≣_     (Continuous-via C) x y
 = Σ δ ꞉ ℕ , (δ ↑) ≼ c (x , y)
 where open closeness-function C
≣-refl  (Continuous-via C) x
 = 0 , (transport ((0 ↑) ≼_) (eic x ⁻¹) (∞-maximal (0 ↑)))
 where open closeness-function C
≣-sym   (Continuous-via C) x y (δ , δ≼cxy)
 = δ , transport ((δ ↑) ≼_) (sym x y) δ≼cxy
 where open closeness-function C
≣-trans (Continuous-via C) x y z (δ₁ , δ≼cxy) (δ₂ , δ≼cyz)
 = minℕ δ₁ δ₂ , ≼-trans ((minℕ δ₁ δ₂) ↑)
                        (min (c (x , y)) (c (y , z)))
                        (c (x , z))
                        (transport (_≼ min (c (x , y)) (c (y , z)))
                          (min-preserves-min δ₁ δ₂ ⁻¹)
                          (≼-min2 (δ₁ ↑) (δ₂ ↑) (c (x , y)) (c (y , z))
                            δ≼cxy δ≼cyz))
                        (ult x y z)
 where open closeness-function C -}
```

0 information literally gives us zero information -- equiv to trivial
equivalence relation.

```agda
0-info' : {𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
        → (C : closeness-function X)
        → (x y : X)
        → (x ≣⟨ 0 -Close-via C ⟩ y) ⇔ (x ≣⟨ Trivial {𝓥} X ⟩ y)
0-info' C x y = (λ _ → ⋆) , (λ _ x ())

eq-close : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
        → (A B : equivalence-relation {𝓥} X)
        → ((x y : X) → x ≣⟨ A ⟩ y ⇔ x ≣⟨ B ⟩ y)
        → (p : decidable-predicate {𝓦} X)
        → (A informs p)
        ⇔ (B informs p)
eq-close A B γ p = (λ Ap x y Bxy → Ap x y (pr₂ (γ x y) Bxy))
                 , (λ Bp x y Axy → Bp x y (pr₁ (γ x y) Axy))
                 
eq-sim : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
       → (A B : equivalence-relation {𝓥} X)
       → ((x y : X) → x ≣⟨ A ⟩ y ⇔ x ≣⟨ B ⟩ y)
       → (p : decidable-predicate {𝓦} X)
       → (A informs p)
       ≃ (B informs p)
eq-sim A B γ p = logically-equivalent-props-are-equivalent
                   (informs-is-prop A p)
                   (informs-is-prop B p)
                   (pr₁ Ap⇔Bp) (pr₂ Ap⇔Bp)
 where Ap⇔Bp = eq-close A B γ p

0-info : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
       → (C : closeness-function X)
       → (p : decidable-predicate {𝓦} X)
       → ((0 -Close-via C) informs p)
       ≃ ((Trivial      X) informs p)
0-info {𝓦} {𝓤} {X} C = eq-sim (0 -Close-via C) (Trivial X) (0-info' C)
```

information is transitive

```agda
succ-info : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
       → (C : closeness-function X)
       → (p : decidable-predicate {𝓦} X)
       → (n : ℕ)
       → ((n      -Close-via C) informs p)
       → ((succ n -Close-via C) informs p)
succ-info {𝓦} {𝓤} {X} C (p , d , i) n ι x y sn≼cxy = ι x y n≼cxy
 where
   n≼cxy : (n ↑) ≼ c C (x , y)
   n≼cxy 0 r = sn≼cxy 0 refl
   n≼cxy (succ k) r = sn≼cxy (succ k) (pr₂ (n ↑) k r)   
```

If the underlying type X is discrete, every decidable predicate is
trivially continuous with any modulus of continuity using the discrete
sequence closeness function.

```agda
d-closeness : {X : 𝓤 ̇ } → is-discrete X → closeness-function X
c   (d-closeness ds) = discrete-clofun ds
eic (d-closeness ds) = equal→inf-close (discrete-is-clofun ds)
ice (d-closeness ds) = inf-close→equal (discrete-is-clofun ds)
sym (d-closeness ds) = symmetricity    (discrete-is-clofun ds)
ult (d-closeness ds) = ultrametric     (discrete-is-clofun ds)

1-close-informs-discrete : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
                         → (ds : is-discrete X)
                         → (p : decidable-predicate {𝓦} X)
                         → (1 -Close-via d-closeness ds) informs p
1-close-informs-discrete ds (p , _) x y 1≼cxy
 = transport p (γ (ds x y) 1≼cxy)
 where
   γ : (q : decidable (x ＝ y)) → (1 ↑) ≼ discrete-c' (x , y) q → x ＝ y
   γ (inl  x＝y) _ = x＝y
   γ (inr ¬x＝y) r = 𝟘-elim (zero-is-not-one (r 0 refl))

succ-close-informs-discrete
 : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
 → (n : ℕ)
 → (ds : is-discrete X)
 → (p : decidable-predicate {𝓦} X)
 → (succ n -Close-via d-closeness ds) informs p
succ-close-informs-discrete 0 = 1-close-informs-discrete
succ-close-informs-discrete (succ n) ds p
 = succ-info (d-closeness ds) p (succ n)
     (succ-close-informs-discrete n ds p)

decidable-discrete-predicate-≃
 : {𝓦 𝓤 : Universe} {X : 𝓤 ̇ }
 → (n : ℕ)
 → (ds : is-discrete X)
 → decidable-predicate  {𝓦} X
 ≃ decidable-predicate-informed-by {𝓦}
     (succ n -Close-via d-closeness ds)
decidable-discrete-predicate-≃ n ds
 = to-subtype-≃ (λ p → (succ-close-informs-discrete n ds p)
                     , (informs-is-prop
                         (succ n -Close-via d-closeness ds) p))
```

A searcher takes decidable predicates and returns something that,
if the predicate is answerable, answers the predicate.

It also returns a natural number denoting the number of times the
predicate was queried.

```agda
Searchable : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
           → equivalence-relation {𝓥} X
           → (𝓦 ⁺) ⊔ 𝓥 ⊔ 𝓤 ̇ 
Searchable {𝓦} {𝓥} {𝓤} {X} _≣_
 = Π ((p , _) , _) ꞉ decidable-predicate-informed-by {𝓦} _≣_
 , Σ (x₀ , n) ꞉ (X × ℕ) , (Σ p → p x₀)

ans⟨_-_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
           → (A : equivalence-relation {𝓥} X)
           → (𝓔 : Searchable {𝓦} A)
           → decidable-predicate-informed-by {𝓦} A
           → X
ans⟨ _ - 𝓔 - p ⟩ = pr₁ (pr₁ (𝓔 p))

n⟨_-_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
         → (A : equivalence-relation {𝓥} X)
         → (𝓔 : Searchable {𝓦} A)
         → decidable-predicate-informed-by {𝓦} A
         → ℕ
n⟨ _ - 𝓔 - p ⟩ = pr₂ (pr₁ (𝓔 p))

sol⟨_-_-_⟩ : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
           → (A : equivalence-relation {𝓥} X)
           → (𝓔 : Searchable {𝓦} A)
           → (pdiϕ : decidable-predicate-informed-by {𝓦} A)
           → let p = p⟨ A - pdiϕ ⟩ in
             Σ p → p ans⟨ A - 𝓔 - pdiϕ ⟩
sol⟨ _ - 𝓔 - p ⟩ = pr₂ (𝓔 p)
```

If a quotient of predicates is searchable, every quotient isomorphic
to that is of course equal.

```agda
≃-searchable : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
             → (A : equivalence-relation {𝓥 } X)
             → (B : equivalence-relation {𝓥'} Y)
             → Searchable {𝓦} A
             → decidable-predicate-informed-by {𝓦} A
             ≃ decidable-predicate-informed-by {𝓦} B
             → Searchable {𝓦} B
≃-searchable A B 𝓔x (f , (g , fg) , (h , hf)) pdiϕ
 = {!!} , {!!}
 where
   p* = g pdiϕ
```

For some types, all of their predicates (those quotiented by the
Identity equivalence relation) are searchable.

These types are called Escardó-searchable.

```agda
Escardó-Searchable : {𝓦 𝓤 : Universe} (X : 𝓤 ̇ )
               → (𝓦 ⁺) ⊔ 𝓤 ̇
Escardó-Searchable {𝓦} {𝓤} X = Searchable {𝓦} (Identity X) 

𝟙-is-searchable : {𝓦 𝓥 𝓤 : Universe} → Escardó-Searchable {𝓦} {𝓤} 𝟙
𝟙-is-searchable ((p , _) , _) = (⋆ , 0) , γ
 where
   γ : Σ p → p ⋆
   γ (⋆ , px) = px

+-equivalence-relation : {𝓥 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                       → equivalence-relation {𝓥}  X
                       → equivalence-relation {𝓥}      Y
                       → equivalence-relation {𝓥} (X + Y)
_≣_     (+-equivalence-relation A B) (inl x) (inl y)         = x ≣⟨ A ⟩ y
_≣_     (+-equivalence-relation A B) (inl x) (inr y)         = 𝟘
_≣_     (+-equivalence-relation A B) (inr x) (inl y)         = 𝟘
_≣_     (+-equivalence-relation A B) (inr x) (inr y)         = x ≣⟨ B ⟩ y
≣-refl  (+-equivalence-relation A B) (inl x)                 = ≣-refl A x
≣-refl  (+-equivalence-relation A B) (inr x)                 = ≣-refl B x
≣-sym   (+-equivalence-relation A B) (inl x) (inl y)         = ≣-sym A x y
≣-sym   (+-equivalence-relation A B) (inr x) (inr y)         = ≣-sym B x y
≣-trans (+-equivalence-relation A B) (inl x) (inl y) (inl z) = ≣-trans A x y z
≣-trans (+-equivalence-relation A B) (inr x) (inr y) (inr z) = ≣-trans B x y z

+-equivalence-relation-＝-id
 : {X Y : 𝓤 ̇ }
 → +-equivalence-relation (Identity X) (Identity Y)
 ＝ Identity (X + Y)
+-equivalence-relation-＝-id
  = {!refl!}

+-is-searchable : {𝓦 𝓥 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                → (A : equivalence-relation {𝓥 } X)
                → (B : equivalence-relation {𝓥} Y)
                → (𝓔x : Searchable {𝓦} A)
                → (𝓔y : Searchable {𝓦} B)
                → Searchable {𝓦} (+-equivalence-relation A B)
+-is-searchable = {!!}
```

The type Fin n is the type with n-many constructors.
All nonempty Fin types are Escardó-searchable.

```agda
Fin : ℕ → 𝓤 ̇
Fin 0 = 𝟘
Fin 1 = 𝟙
Fin {𝓤} (succ (succ n)) = Fin {𝓤} (succ n) + 𝟙 {𝓤}

Fin-nonempty : {𝓤 : Universe} → (n : ℕ) → nonempty (Fin {𝓤} (succ n))
Fin-nonempty 0        =     ⋆
Fin-nonempty (succ n) = inr ⋆

Fin-is-searchable : {𝓦 𝓤 : Universe}
                  → (n : ℕ) → nonempty (Fin {𝓤} n)
                  → Escardó-Searchable {𝓦} (Fin {𝓤} n)
Fin-is-searchable  {𝓦} {𝓤} 1               _
 = 𝟙-is-searchable {𝓦} {𝓤}
Fin-is-searchable  {𝓦} {𝓤} (succ (succ n)) _
 = transport Searchable (+-equivalence-relation-＝-id {𝓤})
     (+-is-searchable (Identity (Fin (succ n))) (Identity 𝟙)
       (Fin-is-searchable (succ n) (Fin-nonempty n))
       (𝟙-is-searchable {𝓦} {𝓤}))

≃-is-E-searchable : {𝓦 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                  → X ≃ Y
                  → Escardó-Searchable {𝓦} X
                  → Escardó-Searchable {𝓦} Y
≃-is-E-searchable {_} {_} {_} {X} (f , (g , fg) , _) 𝓔x ((p' , d' , i') , ϕ')
 = (f ans , n) , λ (y , py) → sol (g y , (transport p' (fg y ⁻¹) py))
 where   
   p = p' ∘ f
   d = d' ∘ f
   i = i' ∘ f
   ϕ = λ x y → ϕ' (f x) (f y) ∘ ap f
   p* = ((p , d , i) , ϕ)
   ans = ans⟨ Identity X - 𝓔x - p* ⟩
   n   =   n⟨ Identity X - 𝓔x - p* ⟩
   sol = sol⟨ Identity X - 𝓔x - p* ⟩

all-finite-types-are-Escardó-searchable
 : {𝓦 : Universe} → {X : 𝓤 ̇ } → (Σ n ꞉ ℕ , Fin {𝓤} n ≃ X) → nonempty X 
 → Escardó-Searchable {𝓦} X
all-finite-types-are-Escardó-searchable (n , X≃Fin) x
 = ≃-is-E-searchable X≃Fin
     (Fin-is-searchable n (pr₁ (pr₁ (pr₂ X≃Fin)) x))
```

All nonempty finite types are Escardó-searchable.

```agda
×-equivalence-relation : {𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                       → equivalence-relation {𝓥     }  X
                       → equivalence-relation {    𝓥'}      Y
                       → equivalence-relation {𝓥 ⊔ 𝓥'} (X × Y)
_≣_     (×-equivalence-relation A B)
 (x₁ , y₁) (x₂ , y₂) = (x₁ ≣⟨ A ⟩ x₂) × (y₁ ≣⟨ B ⟩ y₂)
≣-refl  (×-equivalence-relation A B)
 (x₁ , y₁) = ≣-refl A x₁ , ≣-refl B y₁
≣-sym   (×-equivalence-relation A B)
 (x₁ , y₁) (x₂ , y₂) (ex , ey) = ≣-sym A x₁ x₂ ex , ≣-sym B y₁ y₂ ey
≣-trans (×-equivalence-relation A B)
 (x₁ , y₁) (x₂ , y₂) (x₃ , y₃) (ex₁ , ey₁) (ex₂ , ey₂)
 = ≣-trans A x₁ x₂ x₃ ex₁ ex₂ , ≣-trans B y₁ y₂ y₃ ey₁ ey₂

×-equivalence-relation-elim-l
 : {𝓥 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
 → equivalence-relation {𝓥} (X × Y)
 → equivalence-relation {𝓥 ⊔ 𝓤'}  X
_≣_     (×-equivalence-relation-elim-l AB)
 x₁ x₂ = ∀ y → (x₁ , y) ≣⟨ AB ⟩ (x₂ , y)
≣-refl  (×-equivalence-relation-elim-l AB)
 x₁ y = ≣-refl AB (x₁ , y)
≣-sym   (×-equivalence-relation-elim-l AB)
 x₁ x₂ f y = ≣-sym AB (x₁ , y) (x₂ , y) (f y)
≣-trans (×-equivalence-relation-elim-l AB)
 x₁ x₂ x₃ f g y = ≣-trans AB (x₁ , y) (x₂ , y) (x₃ , y) (f y) (g y)
 
head-predicate* : {𝓦 𝓥 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                → (AB : equivalence-relation {𝓥} (X × Y))
                → decidable-predicate-informed-by {𝓦} AB
                → (y : Y)
                → decidable-predicate-informed-by {𝓦}
                    (×-equivalence-relation-elim-l AB)
head-predicate* AB ((p' , d' , i') , ϕ') y = (p , d , i) , ϕ
 where
   p = p' ∘ (_, y)
   d = d' ∘ (_, y)
   i = i' ∘ (_, y)
   ϕ : ×-equivalence-relation-elim-l AB informs (p , d , i)
   ϕ x₁ x₂ x≣y = ϕ' (x₁ , y) (x₂ , y) (x≣y y)
                           
fst-predicate : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
              → (A : equivalence-relation {𝓥 } X)
              → (B : equivalence-relation {𝓥'} Y)
              → decidable-predicate-informed-by {𝓦}
                  (×-equivalence-relation A B)
              → (y : Y)
              → decidable-predicate-informed-by {𝓦} A
fst-predicate A B ((p' , d' , i') , ϕ') y = (p , d , i) , ϕ
 where
   p = p' ∘ (_, y)
   d = d' ∘ (_, y)
   i = i' ∘ (_, y)
   ϕ : A informs (p , d , i)
   ϕ x₁ x₂ x₁≈x₂ = ϕ' (x₁ , y) (x₂ , y) (x₁≈x₂ , ≣-refl B y)

Searcher-preserves-equivalence-relation
 : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
 → (A : equivalence-relation {𝓥 } X)
 → (B : equivalence-relation {𝓥'} Y)
 → ((x : X) → decidable-predicate-informed-by {𝓦} B)
 → Searchable {𝓦} B
 → 𝓥 ⊔ 𝓥' ⊔ 𝓤 ̇ 
Searcher-preserves-equivalence-relation
 {𝓦} {𝓥} {𝓥'} {𝓤} {𝓤'} {X} {Y} A B ps 𝓔y
 = (x₁ x₂ : X) → x₁ ≣⟨ A ⟩ x₂ → ans⟨ ps x₁ ⟩ ≣⟨ B ⟩ ans⟨ ps x₂ ⟩
 where ans⟨_⟩ = ans⟨ B - 𝓔y -_⟩

snd-predicate : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
              → (A : equivalence-relation {𝓥 } X)
              → (B : equivalence-relation {𝓥'} Y)
              → (p : decidable-predicate-informed-by {𝓦}
                       (×-equivalence-relation A B))
              → (𝓔x : Searchable {𝓦} A)
              → Searcher-preserves-equivalence-relation {𝓦} B A
                  (fst-predicate A B p) 𝓔x
              → decidable-predicate-informed-by {𝓦} B
snd-predicate {_} {_} {_} {_} {_} {X} {Y}
 A B ((p' , d' , i') , ϕ') 𝓔x preserves = (p , d , i) , ϕ
 where
   ans-× : Y → X × Y
   ans-× y = ans⟨ A - 𝓔x - fst-predicate A B ((p' , d' , i') , ϕ') y ⟩
           , y
   p = p' ∘ ans-×
   d = d' ∘ ans-×
   i = i' ∘ ans-×
   ϕ : B informs (p , d , i)
   ϕ y₁ y₂ y₁≈y₂ = ϕ' (ans-× y₁) (ans-× y₂)
                      (preserves y₁ y₂ y₁≈y₂ , y₁≈y₂)
   
×-is-searchable-l : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                  → (A : equivalence-relation {𝓥 } X)
                  → (B : equivalence-relation {𝓥'} Y)
                  → (𝓔x : Searchable {𝓦} A)
                  →       Searchable {𝓦} B
                  → (∀ p → Searcher-preserves-equivalence-relation {𝓦}
                           B A (fst-predicate A B p) 𝓔x)
                  → Searchable {𝓦} (×-equivalence-relation A B)
×-is-searchable-l {𝓦} {𝓥} {𝓥'} {𝓤} {𝓤'} {X} {Y} A B 𝓔x 𝓔y preserves p
 = ((x₀→ y₀ , y₀) , nx→ y₀ +ℕ ny)
 , λ ((x , y) , pxy) → γy (y , (γx→ y (x , pxy)))
 where
   px = fst-predicate A B p
   py = snd-predicate A B p 𝓔x (preserves p)
   x₀→ = λ y → ans⟨ A - 𝓔x - px y ⟩
   nx→ = λ y →   n⟨ A - 𝓔x - px y ⟩
   γx→ = λ y → sol⟨ A - 𝓔x - px y ⟩
   y₀ = ans⟨ B - 𝓔y - py ⟩
   ny =   n⟨ B - 𝓔y - py ⟩
   γy = sol⟨ B - 𝓔y - py ⟩

swap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X × Y → Y × X
swap (x , y) = y , x

×-is-searchable-r : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                  → (A : equivalence-relation {𝓥 } X)
                  → (B : equivalence-relation {𝓥'} Y)
                  →       Searchable {𝓦} A
                  → (𝓔y : Searchable {𝓦} B)
                  → (∀ p → Searcher-preserves-equivalence-relation {𝓦}
                           A B (fst-predicate B A p) 𝓔y)
                  → Searchable {𝓦} (×-equivalence-relation A B)
×-is-searchable-r {𝓦} {𝓥} {𝓥'} {𝓤} {𝓤'} {X} {Y} A B 𝓔x 𝓔y
 preserves ((p' , d' , i') , ϕ')
 = (swap ans , n) , λ ((x , y) , p'xy) → sol ((y , x) , p'xy)
 where
   p : decidable-predicate-informed-by {𝓦}
         (×-equivalence-relation B A)
   p = (p' ∘ swap , d' ∘ swap , i' ∘ swap)
     , λ (x₁ , y₁) (x₂ , y₂) (x≣ , y≣)
     → ϕ' (y₁ , x₁) (y₂ , x₂) (y≣ , x≣)
   𝓔yx = ×-is-searchable-l B A 𝓔y 𝓔x preserves
   ans = ans⟨ ×-equivalence-relation B A - 𝓔yx - p ⟩
   n   =   n⟨ ×-equivalence-relation B A - 𝓔yx - p ⟩ 
   sol = sol⟨ ×-equivalence-relation B A - 𝓔yx - p ⟩

×-is-searchable : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                → (A : equivalence-relation {𝓥 } X)
                → (B : equivalence-relation {𝓥'} Y)
                → (𝓔x : Searchable {𝓦} A)
                → (𝓔y : Searchable {𝓦} B)
                → (∀ p → Searcher-preserves-equivalence-relation {𝓦}
                         B A (fst-predicate A B p) 𝓔x)
                + (∀ p → Searcher-preserves-equivalence-relation {𝓦}
                         A B (fst-predicate B A p) 𝓔y)
                → Searchable {𝓦} (×-equivalence-relation A B)
×-is-searchable      A B 𝓔x 𝓔y (inl preserves)
 = ×-is-searchable-l A B 𝓔x 𝓔y      preserves
×-is-searchable      A B 𝓔x 𝓔y (inr preserves)
 = ×-is-searchable-r A B 𝓔x 𝓔y      preserves

Identity-always-preserves
 : {𝓦 𝓦' 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
 → (B : equivalence-relation {𝓥'} Y)
 → (𝓔y : Searchable {𝓦} B)
 → (p : (x : X) → decidable-predicate-informed-by {𝓦} B)
 → Searcher-preserves-equivalence-relation {𝓦} (Identity X) B p 𝓔y
Identity-always-preserves B 𝓔y p x x refl
 = ≣-refl B (ans⟨ B - 𝓔y - p x ⟩)
```

splittable : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
           → (C : closeness-function {𝓥 } X)
           → ?
splittable {𝓦} {𝓥} {𝓥'} {𝓤} {𝓤'} {X} {Y} C
 = (δ : ℕ)
 → (p : decidable-predicate-informed-by (δ -Close-via C))
 → 

```agda
record equiv-of-setoids {𝓤 𝓤' 𝓥 𝓥' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
  (A : equivalence-relation {𝓥 } X)
  (B : equivalence-relation {𝓥'} Y)  : 𝓤 ⊔ 𝓤' ⊔ 𝓥 ⊔ 𝓥' ⁺  ̇ where
  field
    f : X → Y
    g : Y → X
    trans-A : (x : X) → x ≣⟨ A ⟩ g (f x)
    trans-B : (y : Y) → y ≣⟨ B ⟩ f (g y)
    lift-AB : (x₁ x₂ : X) → x₁ ≣⟨ A ⟩ x₂ → (f x₁) ≣⟨ B ⟩ (f x₂)
    lift-BA : (y₁ y₂ : Y) → y₁ ≣⟨ B ⟩ y₂ → (g y₁) ≣⟨ A ⟩ (g y₂)

open equiv-of-setoids

equiv-of-setoids-sym : {𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
                     → (A : equivalence-relation {𝓥 } X)
                     → (B : equivalence-relation {𝓥'} Y)
                     → equiv-of-setoids A B
                     → equiv-of-setoids B A
f (equiv-of-setoids-sym A B se) = g se
g (equiv-of-setoids-sym A B se) = f se
trans-A (equiv-of-setoids-sym A B se) = trans-B se
trans-B (equiv-of-setoids-sym A B se) = trans-A se
lift-AB (equiv-of-setoids-sym A B se) = lift-BA se
lift-BA (equiv-of-setoids-sym A B se) = lift-AB se

convert-predicates
 : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
 → (A : equivalence-relation {𝓥 } X)
 → (B : equivalence-relation {𝓥'} Y)
 → (FG : equiv-of-setoids A B)
 → (pdiϕA  : decidable-predicate-informed-by {𝓦} A)
 → Σ pdiϕB ꞉ decidable-predicate-informed-by {𝓦} B
 , ((x : X) → p⟨ A - pdiϕA ⟩ x → p⟨ B - pdiϕB ⟩ (f FG x))
convert-predicates A B FG ((p' , d' , i') , ϕ')
 = ((p' ∘ g FG , d' ∘ g FG , i' ∘ g FG)
 , (λ y₁ y₂ y₁≣y₂ → ϕ' (g FG y₁) (g FG y₂) (lift-BA FG y₁ y₂ y₁≣y₂)))
 , (λ y → ϕ' y (g FG (f FG y)) (trans-A FG y))

convert-searchable
 : {𝓦 𝓥 𝓥' 𝓤 𝓤' : Universe} {X : 𝓤 ̇ } {Y : 𝓤' ̇ }
 → (A : equivalence-relation {𝓥 } X)
 → (B : equivalence-relation {𝓥'} Y)
 → (FG : equiv-of-setoids A B)
 → Searchable {𝓦} B
 → Searchable {𝓦} A
convert-searchable {𝓦} A B FG 𝓔y pdiϕ
 = (g FG ans⟨ B - 𝓔y - p* ⟩ , n⟨ B - 𝓔y - p* ⟩)
 , λ (x , px) → sol⟨ B - 𝓔y - p* ⟩ (f FG x , pγ x px)
 where
   conv-preds = convert-predicates {𝓦} A B FG pdiϕ
   p* = pr₁ conv-preds
   pγ = pr₂ conv-preds
```

```agda
_≈_ : {X : ℕ → 𝓤 ̇ } → ((n : ℕ) → X n) → ((n : ℕ) → X n) → ℕ → 𝓤 ̇
(α ≈ β) n = (i : ℕ) → i <ℕ n → α i ＝ β i

sequence-relation-≈' : (X : ℕ → 𝓤 ̇ ) → (δ : ℕ)
                     → equivalence-relation {𝓤} ((n : ℕ) → X n)
_≣_     (sequence-relation-≈' X δ)
 α β = (α ≈ β) δ
≣-refl  (sequence-relation-≈' X δ)
 α             = λ i i<δ → refl
≣-sym   (sequence-relation-≈' X δ)
 α β   α≈β     = λ i i<δ → α≈β i i<δ ⁻¹
≣-trans (sequence-relation-≈' X δ)
 α β ζ α≈β β≈ζ = λ i i<δ → α≈β i i<δ ∙ β≈ζ i i<δ

-- sequence-relation-≈ should be countable union of sequence-relation-≈'
sequence-relation-c : (X : 𝓤 ̇ ) (δ : ℕ)
                    → equivalence-relation {𝓤₀} (ℕ → X)
sequence-relation-c X δ = δ -Close-via {!!}

hd : {X : ℕ → 𝓤 ̇ } → Π X → X 0
hd α = α 0

tl : {X : ℕ → 𝓤 ̇ } → Π X → Π (X ∘ succ)
tl α = α ∘ succ

_∷_ : {X : ℕ → 𝓤 ̇ } → X 0 → Π (X ∘ succ) → Π X
(αₕ ∷ αₜ) 0 = αₕ
(αₕ ∷ αₜ) (succ n) = αₜ n

split-ℕ→ : {X : ℕ → 𝓤 ̇ } → (δ : ℕ)
         → equiv-of-setoids
             (sequence-relation-≈' X (succ δ))
             (×-equivalence-relation
               (Identity (X 0))
               (sequence-relation-≈' (X ∘ succ) δ))
f (split-ℕ→ δ) α         = hd α , tl α
g (split-ℕ→ δ) (hα , tα) = hα ∷ tα
trans-A (split-ℕ→ δ) α 0        _ = refl
trans-A (split-ℕ→ δ) α (succ i) _ = refl
trans-B (split-ℕ→ δ) (hα , tα)    = refl , (λ i _ → refl)
lift-AB (split-ℕ→ δ) α β α≈β
 = α≈β 0 ⋆ , λ i → α≈β (succ i)
lift-BA (split-ℕ→ δ) (hα , tα) (hβ , tβ) (hα＝hβ , tα＝tβ) 0 _
 = hα＝hβ
lift-BA (split-ℕ→ δ) (hα , tα) (hβ , tβ) (hα＝hβ , tα＝tβ) (succ i)
 = tα＝tβ i

ℕ→D-Searchable : {𝓦 𝓤 : Universe} {X : ℕ → 𝓤 ̇ }
               → ((n : ℕ) → Escardó-Searchable {𝓦} (X n))
               → (δ : ℕ)
               → Searchable {𝓦} (sequence-relation-≈' X δ)
ℕ→D-Searchable {𝓦} {𝓤} {X} 𝓔xs 0 ((p , d , i) , ϕ)
 = ((λ i → ans⟨ Identity (X i) - 𝓔xs i - tp i , Id-informs-everything (tp i) ⟩) , 0)
 , (λ (α , pα) → ϕ α _ (λ _ ()) pα)
 where tp = trivial-predicate ∘ X
ℕ→D-Searchable {𝓦} {𝓤} {X} 𝓔xs (succ δ)
 = convert-searchable (sequence-relation-≈' X (succ δ))
     (×-equivalence-relation
       (Identity (X 0))
       (sequence-relation-≈' (X ∘ succ) δ))
       (split-ℕ→ δ)
       (×-is-searchable
         (Identity (X 0))
         (sequence-relation-≈' (X ∘ succ) δ)
         (𝓔xs 0)
         (ℕ→D-Searchable (𝓔xs ∘ succ) δ)
         (inr (λ p → Identity-always-preserves {𝓦} {𝓤}
           (sequence-relation-≈' (X ∘ succ) δ)
           (ℕ→D-Searchable (𝓔xs ∘ succ) δ)
           (fst-predicate
             (sequence-relation-≈' (X ∘ succ) δ)
             (Identity (X 0)) p))))

ℤ[_,_]-searchable : (l u : ℤ) → (n : ℕ) → l +pos n ＝ u
                  → Searchable {𝓦} (Identity ℤ[ l , u ])
ℤ[ l , l ]-searchable 0 refl ((p , d , i) , ϕ)
 = ((l , ℤ≤-refl l , ℤ≤-refl l) , 0)
 , λ ((z , l≤z≤u) , pz)
   → transport p (to-subtype-＝ ≤ℤ²-is-prop ((≤ℤ-antisym l z l≤z≤u) ⁻¹)) pz
ℤ[ l , .(succℤ (l +pos n)) ]-searchable (succ n) refl ((p , d , i) , ϕ)
 = Cases (d u*)
     (λ  pu → (u* , 1) , (λ _ → pu))
     (λ ¬pu → (ans , k)
            , λ ((z , l≤z , z≤u) , pz)
              → Cases (ℤ≤-split z u z≤u)
                (λ z<u → sol ((z , l≤z
                       , transport (z ≤ℤ_) (predsuccℤ _) (≤ℤ-back z u z<u))
                       , (transport p (to-subtype-＝ ≤ℤ²-is-prop refl) pz)))
                (λ z＝u → 𝟘-elim (¬pu
                         (transport p (to-subtype-＝ ≤ℤ²-is-prop z＝u) pz))))
 where
   u = succℤ (l +pos n)
   u* = u , (succ n , refl) , ℤ≤-refl u
   ι : ℤ[ l , l +pos n ] → ℤ[ l , u ]
   ι = ℤ[ l , l +pos n ]-succ
   IH = ℤ[ l , l +pos n ]-searchable n refl
          ((p ∘ ι , d ∘ ι , i ∘ ι) , λ x y x＝y → ϕ (ι x) (ι y) (ap ι x＝y))
   ans = ι (pr₁ (pr₁ IH))
   k = pr₂ (pr₁ IH)
   sol = pr₂ IH

ℕ→ℤ[_,_]-searchable : (ls us : ℕ → ℤ) → ((n : ℕ) → ls n ≤ℤ us n) → (δ : ℕ)
                    → Searchable {𝓦} (sequence-relation-≈' (λ n → ℤ[ ls n , us n ]) δ)
ℕ→ℤ[ ls , us ]-searchable ls≤us
 = ℕ→D-Searchable
     (λ n → ℤ[ ls n , us n ]-searchable (pr₁ (ls≤us n)) (pr₂ (ls≤us n)))
```

searcher : {𝓦 𝓥 𝓤 : Universe} {X : 𝓤 ̇ }
         → Σ 𝓔 
