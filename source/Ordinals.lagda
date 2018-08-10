Martin Escardo, 29 June 2018

The type Ordinals of ordinals in a universe U, and the subtype Ordinalsᵀ of
ordinals with a top element.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import OrdinalNotions hiding (_≤_)
open import UF-Embedding

module Ordinals
       (fe : ∀ U V → funext U V)
       where

Ordinal : ∀ U → U ′ ̇
Ordinal U = Σ \(X : U ̇) → Σ \(_<_ : X → X → U ̇) → is-well-order _<_

\end{code}

The underlying type of an ordinal (which happens to to be necessarily
a set):

\begin{code}

⟨_⟩ : ∀ {U} → Ordinal U → U ̇
⟨ X , _<_ , o ⟩ = X

underlying-order : ∀ {U} → (α : Ordinal U) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

underlying-porder : ∀ {U} → (α : Ordinal U) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-porder (X , _<_ , o) = _≼_ _<_

syntax underlying-order  α x y = x ≺⟨ α ⟩ y
syntax underlying-porder α x y = x ≼⟨ α ⟩ y

is-well-ordered : ∀ {U} → (α : Ordinal U) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

Prop-valuedness : ∀ {U} (τ : Ordinal U) → is-prop-valued (underlying-order τ)
Prop-valuedness τ = prop-valuedness (underlying-order τ) (is-well-ordered τ)

Transitivity : ∀ {U} (τ : Ordinal U) → is-transitive (underlying-order τ)
Transitivity τ = transitivity (underlying-order τ) (is-well-ordered τ)

Well-foundedness : ∀ {U} (τ : Ordinal U) (x : ⟨ τ ⟩) → is-accessible (underlying-order τ) x
Well-foundedness τ = well-foundedness (underlying-order τ) (is-well-ordered τ)

Extensionality : ∀ {U} (τ : Ordinal U) → is-extensional (underlying-order τ)
Extensionality τ = extensionality (underlying-order τ) (is-well-ordered τ)

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for searchable
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordinalᵀ : ∀ U → U ′ ̇
Ordinalᵀ U = Σ \(α : Ordinal U) → has-top (underlying-order α)

[_] : ∀ {U} → Ordinalᵀ U → Ordinal U
[ α , t ] = α

⟪_⟫ : ∀ {U} → Ordinalᵀ U → U ̇
⟪ (X , _<_ , o) , t ⟫ = X

tunderlying-order : ∀ {U} → (τ : Ordinalᵀ U) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : ∀ {U} → (τ : Ordinalᵀ U) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : ∀ {U} → (τ : Ordinalᵀ U) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued {U} τ x y l m = dfunext (fe U U₀) (λ x → 𝟘-elim (m x))

topped : ∀ {U} → (τ : Ordinalᵀ U) → has-top (tunderlying-order τ)
topped (α , t) = t

top : ∀ {U} → (τ : Ordinalᵀ U) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : ∀ {U} → (τ : Ordinalᵀ U) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : ∀ {U} → (τ : Ordinalᵀ U) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

\end{code}

Given an ordinal τ and a point x of its underlying set, any lower set
τ ↓ a of a point a : ⟨ τ ⟩ forms a (sub-)ordinal:

\begin{code}

_↓_ : ∀ {U} (τ : Ordinal U) → ⟨ τ ⟩ → Ordinal U
τ ↓ a = (Σ \(y : ⟨ τ ⟩) → y ≺⟨ τ ⟩ a) , _<_ , p , w , e , t
 where
  _<_ : (Σ \(x : ⟨ τ ⟩) → x ≺⟨ τ ⟩ a) → (Σ \(x : ⟨ τ ⟩) → x ≺⟨ τ ⟩ a) → _ ̇
  (y , _) < (z , _) = y ≺⟨ τ ⟩ z
  p : is-prop-valued _<_
  p (x , _) (y , _)  = Prop-valuedness τ x y
  w : is-well-founded _<_
  w (x , l) = γ x (Well-foundedness τ x) l
   where
    γ : ∀ x → is-accessible (underlying-order τ) x → ∀ l → is-accessible _<_ (x , l)
    γ x (next .x s) l = next (x , l) (λ σ m → γ (pr₁ σ) (s (pr₁ σ) m) (pr₂ σ))
  e : is-extensional _<_
  e (x , l) (y , m) f g =
   to-Σ-≡
    (Extensionality τ x y
      (λ u n → f (u , Transitivity τ u x a n l) n)
      (λ u n → g (u , Transitivity τ u y a n m) n) ,
    Prop-valuedness τ y a _ _)
  t : is-transitive _<_
  t (x , _) (y , _) (z , _) l m = Transitivity τ x y z l m

segment-inclusion : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
                  → ⟨ τ ↓ a ⟩ → ⟨ τ ⟩
segment-inclusion τ a = pr₁

\end{code}

Maps of ordinals.

\begin{code}

order-preserving
 order-reflecting
 order-embedding
 initial-segment
 simulation
  : ∀ {U} → (τ υ : Ordinal U) → (⟨ τ ⟩ → ⟨ υ ⟩) → U ̇

order-preserving τ υ f = (x y : ⟨ τ ⟩) → x ≺⟨ τ ⟩ y → f x ≺⟨ υ ⟩ f y
order-reflecting τ υ f = (x y : ⟨ τ ⟩) → f x ≺⟨ υ ⟩ f y → x ≺⟨ τ ⟩ y
order-embedding  τ υ f = order-preserving τ υ f × order-reflecting τ υ f
initial-segment  τ υ f = (x : ⟨ τ ⟩) (y : ⟨ υ ⟩)
                            → y ≺⟨ υ ⟩ f x → Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ x) × (f x' ≡ y)
simulation       τ υ f = initial-segment  τ υ f × order-preserving τ υ f

order-preserving-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                        → is-prop (order-preserving τ υ f)
order-preserving-is-prop {U} τ υ f =
 Π-is-prop (fe U U)
   (λ x → Π-is-prop (fe U U)
             (λ y → Π-is-prop (fe U U)
                      (λ l → Prop-valuedness υ (f x) (f y))))

order-reflecting-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                        → is-prop (order-reflecting τ υ f)
order-reflecting-is-prop {U} τ υ f =
 Π-is-prop (fe U U)
   (λ x → Π-is-prop (fe U U)
             (λ y → Π-is-prop (fe U U)
                      (λ l → Prop-valuedness τ x y)))

iplc : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
    → simulation τ υ f
    → left-cancellable f
iplc τ υ f (i , p) {x} {y} = γ x y (Well-foundedness τ x) (Well-foundedness τ y)
 where
  γ : ∀ x y → is-accessible (underlying-order τ) x → is-accessible (underlying-order τ) y
    → f x ≡ f y → x ≡ y
  γ x y (next .x s) (next .y t) r = Extensionality τ x y g h
   where
    g : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ x → u ≺⟨ τ ⟩ y
    g u l = d
     where
      a : f u ≺⟨ υ ⟩ f y
      a = transport (λ - → f u ≺⟨ υ ⟩ -) r (p u x l)
      b : Σ \(v : ⟨ τ ⟩) → (v ≺⟨ τ ⟩ y) × (f v ≡ f u)
      b = i y (f u) a
      c : u ≡ pr₁ b
      c = γ u (pr₁ b) (s u l) (t (pr₁ b) (pr₁(pr₂ b))) ((pr₂ (pr₂ b))⁻¹)
      d : u ≺⟨ τ ⟩ y
      d = transport (λ - → - ≺⟨ τ ⟩ y) (c ⁻¹) (pr₁(pr₂ b))
    h : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ y → u ≺⟨ τ ⟩ x
    h u l = d
     where
      a : f u ≺⟨ υ ⟩ f x
      a = transport (λ - → f u ≺⟨ υ ⟩ -) (r ⁻¹) (p u y l)
      b : Σ \(v : ⟨ τ ⟩) → (v ≺⟨ τ ⟩ x) × (f v ≡ f u)
      b = i x (f u) a
      c : pr₁ b ≡ u
      c = γ (pr₁ b) u (s (pr₁ b) (pr₁(pr₂ b))) (t u l) (pr₂(pr₂ b))
      d : u ≺⟨ τ ⟩ x
      d = transport (λ - → - ≺⟨ τ ⟩ x) c (pr₁(pr₂ b))

initial-segment-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                        → order-preserving τ υ f
                        → is-prop (initial-segment τ υ f)
initial-segment-is-prop {U} τ υ f p i =
 (Π-is-prop (fe U U)
    λ x → Π-is-prop (fe U U)
            λ z → Π-is-prop (fe U U)
                    λ l → γ x z l) i
  where
   γ : ∀ x z → z ≺⟨ υ ⟩ f x → is-prop(Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f y ≡ z))
   γ x z l (y , (m , r)) (y' , (m' , r')) = to-Σ-≡ (a , b)
    where
     c : f y ≡ f y'
     c = r ∙ r' ⁻¹
     a : y ≡ y'
     a = iplc τ υ f (i , p) c
     b : transport (λ - →  (- ≺⟨ τ ⟩ x) × (f - ≡ z)) a (m , r) ≡ m' , r'
     b = ×-is-prop
          (Prop-valuedness τ y' x)
          (extensional-gives-is-set
              (underlying-order υ) fe
              (Prop-valuedness υ)
              (Extensionality υ))
         (transport (λ - →  (- ≺⟨ τ ⟩ x) × (f - ≡ z)) a (m , r))
         (m' , r')

\end{code}

The simulations form a poset:

\begin{code}

simulation-is-prop : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                  → is-prop (simulation τ υ f)
simulation-is-prop τ υ f = ×-prop-criterion
                            (initial-segment-is-prop τ υ f ,
                             λ _ → order-preserving-is-prop τ υ f)

at-most-one-simulation : ∀ {U} (τ υ : Ordinal U) (f f' : ⟨ τ ⟩ → ⟨ υ ⟩)
                      → simulation τ υ f
                      → simulation τ υ f'
                      → f ∼ f'
at-most-one-simulation τ υ f f' (i , p) (i' , p') x =
 γ x (Well-foundedness τ x)
 where
  γ : ∀ x → is-accessible (underlying-order τ) x → f x ≡ f' x
  γ x (next .x u) = Extensionality υ (f x) (f' x) a b
   where
    IH : ∀ y → y ≺⟨ τ ⟩ x → f y ≡ f' y
    IH y l = γ y (u y l)
    a : (z : ⟨ υ ⟩) → z ≺⟨ υ ⟩ f x → z ≺⟨ υ ⟩ f' x
    a z l = transport (λ - → - ≺⟨ υ ⟩ f' x) t m
     where
      s : Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f y ≡ z)
      s = i x z l
      y : ⟨ τ ⟩
      y = pr₁ s
      m : f' y ≺⟨ υ ⟩ f' x
      m = p' y x (pr₁(pr₂ s))
      t : f' y ≡ z
      t = (IH y (pr₁(pr₂ s)))⁻¹ ∙ pr₂(pr₂ s)
    b : (z : ⟨ υ ⟩) → z ≺⟨ υ ⟩ f' x → z ≺⟨ υ ⟩ f x
    b z l = transport (λ - → - ≺⟨ υ ⟩ f x) t m
     where
      s : Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f' y ≡ z)
      s = i' x z l
      y : ⟨ τ ⟩
      y = pr₁ s
      m : f y ≺⟨ υ ⟩ f x
      m = p y x (pr₁(pr₂ s))
      t : f y ≡ z
      t = IH y (pr₁(pr₂ s)) ∙ pr₂(pr₂ s)

_⊴_ : ∀ {U} → Ordinal U → Ordinal U → U ̇
τ ⊴ υ = Σ \(f : ⟨ τ ⟩ → ⟨ υ ⟩) → simulation τ υ f

⊴-is-prop : ∀ {U} (τ υ : Ordinal U) → is-prop (τ ⊴ υ)
⊴-is-prop {U} τ υ (f , s) (g , t) =
 to-Σ-≡ (dfunext (fe U U) (at-most-one-simulation τ υ f g s t) ,
         simulation-is-prop τ υ g _ _)

⊴-refl : ∀ {U} (τ : Ordinal U) → τ ⊴ τ
⊴-refl τ = id ,
           (λ x z l → z , l , refl) ,
           (λ x y l → l)

⊴-trans : ∀ {U} (τ υ φ : Ordinal U) → τ ⊴ υ → υ ⊴ φ → τ ⊴ φ
⊴-trans τ υ φ (f , i , p) (g , j , q) =
 g ∘ f ,
 k ,
 (λ x y l → q (f x) (f y) (p x y l))
 where
  k : (x : ⟨ τ ⟩) (z : ⟨ φ ⟩) →  z ≺⟨ φ ⟩ (g (f x))
    → Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ x) × (g (f x') ≡ z)
  k x z l = pr₁ b , pr₁(pr₂ b) , (ap g (pr₂(pr₂ b)) ∙ pr₂(pr₂ a))
   where
    a : Σ \(y : ⟨ υ ⟩) → (y ≺⟨ υ ⟩ f x) × (g y ≡ z)
    a = j (f x) z l
    y : ⟨ υ ⟩
    y = pr₁ a
    b : Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ x) × (f x' ≡ y)
    b = i x y (pr₁ (pr₂ a))

\end{code}

A consequence of univalence is that this order is antisymmetric.
Without abstracting the implementation, the proof that the ordinals
form a set, given below, doesn't type check in feasible time (I am not
sure why).

\begin{code}

open import UF-Univalence
open import UF-Equiv

abstract
 ⊴-antisym : ∀ {U} → is-univalent U → (τ υ : Ordinal U)
           → τ ⊴ υ → υ ⊴ τ → τ ≡ υ
 ⊴-antisym {U} ua τ υ (f , s) (g , t) = to-Σ-≡ (p , q)
  where
   fgs : simulation υ υ (f ∘ g)
   fgs = pr₂ (⊴-trans υ τ υ (g , t) (f , s))
   fg : (y : ⟨ υ ⟩) → f (g y) ≡ y
   fg = at-most-one-simulation υ υ (f ∘ g) id fgs (pr₂ (⊴-refl υ))
   gfs : simulation τ τ (g ∘ f)
   gfs = pr₂ (⊴-trans τ υ τ (f , s) (g , t))
   gf : (x : ⟨ τ ⟩) → g (f x) ≡ x
   gf = at-most-one-simulation τ τ (g ∘ f) id gfs (pr₂ (⊴-refl τ))
   e : ⟨ τ ⟩ ≃ ⟨ υ ⟩
   e = (f , ((g , fg) , g , gf))
   p : ⟨ τ ⟩ ≡ ⟨ υ ⟩
   p = eqtoid ua ⟨ τ ⟩ ⟨ υ ⟩ e
   A : (X Y : U ̇) → X ≃ Y → U ′ ̇
   A X Y e = (ρ : Σ \(_<_ : X → X → U ̇) → is-well-order _<_) (σ : Σ \(_<_ : Y → Y → U ̇) → is-well-order _<_)
          → ((x x' : X) → pr₁ ρ x x' → pr₁ σ (equiv-to-fun e x) (equiv-to-fun e x'))
          → ((y y' : Y) → pr₁ σ y y' → pr₁ ρ (back-equiv-to-fun e y) (back-equiv-to-fun e y'))
          → transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) (eqtoid ua X Y e) ρ ≡ σ
   b : ∀ X → A X X (ideq X)
   b X ρ σ φ ψ = γ
    where
     d : ∀ x x' → pr₁ ρ x x' ≡ pr₁ σ x x'
     d x x' = UA-gives-propext ua
              (prop-valuedness (pr₁ ρ) (pr₂ ρ) x x')
              (prop-valuedness (pr₁ σ) (pr₂ σ) x x')
              (φ x x')
              (ψ x x')
     c : pr₁ ρ ≡ pr₁ σ
     c = dfunext (fe U (U ′)) (λ x → dfunext (fe U (U ′)) (d x))
     a : ρ ≡ σ
     a = pr₁-lc (λ {_<_} → ordinal-is-prop _<_ fe) c
     r : eqtoid ua X X (idtoeq X X refl) ≡ refl
     r = eqtoid-idtoeq' ua X X refl
     γ : transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) (eqtoid ua X X (ideq X)) ρ ≡ σ
     γ = back-transport (λ - → transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) - ρ ≡ σ) r a
   h : ∀ X Y (e : X ≃ Y) → A X Y e
   h X = JEq ua X (A X) (b X)
   q : transport (λ - → Σ \(_<_ : - → - → U ̇) → is-well-order _<_) p (pr₂ τ) ≡ pr₂ υ
   q = h ⟨ τ ⟩ ⟨ υ ⟩ e (pr₂ τ) (pr₂ υ) (pr₂ s) (pr₂ t)

segment-inclusion-simulation : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
                            → simulation (τ ↓ a) τ (segment-inclusion τ a)
segment-inclusion-simulation τ a = i , p
 where
  i : initial-segment (τ ↓ a) τ (segment-inclusion τ a)
  i (x , l) z m = (z , Transitivity τ z x a m l) , m , refl
  p : order-preserving (τ ↓ a) τ (segment-inclusion τ a)
  p x y = id

segment-⊴ : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
          → (τ ↓ a) ⊴ τ
segment-⊴ τ a = segment-inclusion τ a , segment-inclusion-simulation τ a

\end{code}

One of the many applications of the univalence axiom is to manufacture
examples of types which are not sets. Here we use it to prove that a
certain type is a set.

\begin{code}

Ordinal-is-set : ∀ {U} → is-univalent U → is-set (Ordinal U)
Ordinal-is-set {U} ua = identification-collapsible-is-set pc
 where
  i : (τ υ : Ordinal U) → is-prop (τ ⊴ υ × υ ⊴ τ)
  i τ υ = ×-is-prop (⊴-is-prop τ υ) (⊴-is-prop υ τ)
  g : (τ υ : Ordinal U) → τ ≡ υ → τ ⊴ υ × υ ⊴ τ
  g τ υ p = transport (λ - → τ ⊴ -) p (⊴-refl τ) , back-transport (λ - → υ ⊴ -) p (⊴-refl υ)
  h : (τ υ : Ordinal U) → τ ⊴ υ × υ ⊴ τ → τ ≡ υ
  h τ υ (l , m) = ⊴-antisym {U} ua τ υ l m
  hc : (τ υ : Ordinal U) (w t : τ ⊴ υ × υ ⊴ τ) → h τ υ w ≡ h τ υ t
  hc τ υ w t = ap (h τ υ) (i τ υ w t)
  f  : (τ υ : Ordinal U) → τ ≡ υ → τ ≡ υ
  f τ υ p = h τ υ (g τ υ p)
  fc : (τ υ : Ordinal U) (p q : τ ≡ υ) → f τ υ p ≡ f τ υ q
  fc τ υ p q = hc τ υ (g τ υ p) (g τ υ q)
  pc : {τ υ : Ordinal U} → Σ \(f : τ ≡ υ → τ ≡ υ) → constant f
  pc {τ} {υ} = (f τ υ , fc τ υ)

open import UF-Equiv

↓-⊴-lc : ∀ {U} (τ : Ordinal U) (a b : ⟨ τ ⟩)
           → (τ ↓ a)  ⊴  (τ ↓ b )
           → a ≼⟨ τ ⟩ b
↓-⊴-lc {U} τ a b (f , s) u l = γ
 where
  h : segment-inclusion τ a ∼ segment-inclusion τ b ∘ f
  h = at-most-one-simulation (τ ↓ a) τ
        (segment-inclusion τ a)
        (segment-inclusion τ b ∘ f)
        (segment-inclusion-simulation τ a)
        (pr₂ (⊴-trans (τ ↓ a) (τ ↓ b) τ
                 (f , s)
                 (segment-⊴ τ b)))
  v : ⟨ τ ⟩
  v = segment-inclusion τ b (f (u , l))
  m : v ≺⟨ τ ⟩ b
  m = pr₂ (f (u , l))
  q : u ≡ v
  q = h (u , l)
  γ : u ≺⟨ τ ⟩ b
  γ = back-transport (λ - → - ≺⟨ τ ⟩ b) q m

↓-lc : ∀ {U} (τ : Ordinal U) (a b : ⟨ τ ⟩)
     → τ ↓ a ≡ τ ↓ b
     → a ≡ b
↓-lc τ a b p =
 Extensionality τ a b
  (↓-⊴-lc τ a b (transport (λ - → (τ ↓ a) ⊴ -) p (⊴-refl (τ ↓ a))))
  (↓-⊴-lc τ b a (back-transport (λ - → (τ ↓ b) ⊴ -) p (⊴-refl (τ ↓ b))))

_⊲_ : ∀ {U} → Ordinal U → Ordinal U → U ′ ̇
τ ⊲ υ = Σ \(b : ⟨ υ ⟩) → τ ≡ (υ ↓ b)

⊲-prop-valued : ∀ {U} → is-univalent U
              → (τ υ : Ordinal U) → is-prop (τ ⊲ υ)
⊲-prop-valued {U} ua τ υ  (b , p) (b' , p') = to-Σ-≡ (r , s)
 where
  r : b ≡ b'
  r = ↓-lc υ b b' (p ⁻¹ ∙ p')
  s : transport (λ - → τ ≡ (υ ↓ -)) r p ≡ p'
  s = Ordinal-is-set ua _ _

down : ∀ {U} (τ : Ordinal U) (b u : ⟨ τ ⟩) (l : u ≺⟨ τ ⟩ b)
    → ((τ ↓ b ) ↓ (u , l)) ⊴ (τ ↓ u)
down {U} τ b u l = f , (i , p)
 where
  f : ⟨ (τ ↓ b) ↓ (u , l) ⟩ → ⟨ τ ↓ u ⟩
  f ((x , m) , n) = x , n
  i : (w : ⟨ (τ ↓ b) ↓ (u , l) ⟩) (t : ⟨ τ ↓ u ⟩)
    → t ≺⟨ τ ↓ u ⟩ f w → Σ \(w' : ⟨ (τ ↓ b) ↓ (u , l) ⟩) → (w' ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ w) × (f w' ≡ t)
  i ((x , m) , n) (x' , m') n' = ((x' , Transitivity τ x' u b m' l) , m') ,
                                 (n' , refl)
  p : (w w' : ⟨ (τ ↓ b) ↓ (u , l) ⟩) → w ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ w' → f w ≺⟨ τ ↓ u ⟩ (f w')
  p w w' = id

up : ∀ {U} (τ : Ordinal U) (b u : ⟨ τ ⟩) (l : u ≺⟨ τ ⟩ b)
  → (τ ↓ u) ⊴ ((τ ↓ b ) ↓ (u , l))
up {U} τ b u l = f , (i , p)
 where
  f : ⟨ τ ↓ u ⟩ → ⟨ (τ ↓ b) ↓ (u , l) ⟩
  f (x , n) = ((x , Transitivity τ x u b n l) , n)
  i : (t : ⟨ τ ↓ u ⟩) (w : ⟨ (τ ↓ b) ↓ (u , l) ⟩)
    → w ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ f t → Σ \(t' : ⟨ τ ↓ u ⟩) → (t' ≺⟨ τ ↓ u ⟩ t) × (f t' ≡ w)
  i (x , n) ((x' , m') , n') o = (x' , n') ,
                                 (o , to-Σ-≡
                                       (to-Σ-≡' (Prop-valuedness τ x' b _ _) ,
                                       Prop-valuedness τ x' u _ _))
  p : (t t' : ⟨ τ ↓ u ⟩) → t ≺⟨ τ ↓ u ⟩ t' → f t ≺⟨ (τ ↓ b) ↓ (u , l) ⟩ f t'
  p t t' = id

iterated-↓ : ∀ {U} → is-univalent U → (τ : Ordinal U) (b u : ⟨ τ ⟩) (l : u ≺⟨ τ ⟩ b)
          → ((τ ↓ b ) ↓ (u , l)) ≡ (τ ↓ u)
iterated-↓ ua τ b u l = ⊴-antisym ua ((τ ↓ b) ↓ (u , l)) (τ ↓ u) (down τ b u l) (up τ b u l)

↓-⊲-lc : ∀ {U} → is-univalent U → (τ : Ordinal U) (a b : ⟨ τ ⟩)
        → (τ ↓ a) ⊲ (τ ↓ b)
        → a ≺⟨ τ ⟩ b
↓-⊲-lc {U} ua τ a b ((u , l) , p) = back-transport (λ - → - ≺⟨ τ ⟩ b) r l
 where
  q : (τ ↓ a) ≡ (τ ↓ u)
  q = p ∙ iterated-↓ ua τ b u l
  r : a ≡ u
  r = ↓-lc τ a u q

↓-⊲-op : ∀ {U} → is-univalent U → (τ : Ordinal U) (a b : ⟨ τ ⟩)
        → a ≺⟨ τ ⟩ b
        → (τ ↓ a) ⊲ (τ ↓ b)
↓-⊲-op ua τ a b l = (a , l) , ((iterated-↓ ua τ b a l)⁻¹)

{- TODO. Problem with lack of cumulativity
≺-is-⊲ : ∀ {U} → is-univalent U → (τ : Ordinal U) (a b : ⟨ τ ⟩)
       → (a ≺⟨ τ ⟩ b) ≡ ((τ ↓ a) ⊲ (τ ↓ b))
≺-is-⊲ = ?
-}

{-
↓-accessible : ∀ {U} (τ : Ordinal U) (a : ⟨ τ ⟩)
             → is-accessible _⊲_ (τ ↓ a)
↓-accessible {U} τ a = γ a (Well-foundedness τ a)
 where
  γ : (a : ⟨ τ ⟩) → is-accessible (underlying-order τ) a → is-accessible _⊲_ (τ ↓ a)
  γ a (next .a s) = next (τ ↓ a) g
   where
    IH : (b : ⟨ τ ⟩) → (τ ↓ b) ⊲ (τ ↓ a) → is-accessible _⊲_ (τ ↓ b)
    IH b l = γ b (s b (↓-⊲-lc τ b a l))
    g : (υ : Ordinal U) → υ ⊲ (τ ↓ a) → is-accessible _⊲_ υ
    g υ (b , p) = h
     where
      q : υ ≡ (τ ↓ a) ↓ b
      q = p
      blah : is-accessible _⊲_ ((τ ↓ a) ↓ b)
      blah = next ((τ ↓ a) ↓ b) (λ y x → {!!})
      h' : is-accessible _⊲_ ((τ ↓ a) ↓ b)
      h' = {!!}
      h : is-accessible _⊲_ υ
      h = {!!}
-}

\end{code}

And here are some additional observations:

\begin{code}

ilcr : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
    → initial-segment τ υ f
    → left-cancellable f
    → order-reflecting τ υ f
ilcr τ υ f i c x y l = γ
 where
  a : Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ y) × (f x' ≡ f x)
  a = i y (f x) l
  γ : x ≺⟨ τ ⟩ y
  γ = transport (λ - → - ≺⟨ τ ⟩ y) (c (pr₂(pr₂ a))) (pr₁(pr₂ a))

ipr : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
   → simulation τ υ f
   → order-reflecting τ υ f
ipr τ υ f (i , p) = ilcr τ υ f i (iplc τ υ f (i , p))

order-embedding-lc : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                  → order-embedding τ υ f
                  → left-cancellable f
order-embedding-lc τ υ f (p , r) {x} {y} s = Extensionality τ x y a b
 where
  a : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ x → u ≺⟨ τ ⟩ y
  a u l = r u y j
   where
    i : f u ≺⟨ υ ⟩ f x
    i = p u x l
    j : f u ≺⟨ υ ⟩ f y
    j = transport (λ - → f u ≺⟨ υ ⟩ -) s i
  b : (u : ⟨ τ ⟩) → u ≺⟨ τ ⟩ y → u ≺⟨ τ ⟩ x
  b u l = r u x j
   where
    i : f u ≺⟨ υ ⟩ f y
    i = p u y l
    j : f u ≺⟨ υ ⟩ f x
    j = back-transport (λ - → f u ≺⟨ υ ⟩ -) s i

order-embedding-is-embedding : ∀ {U} (τ υ : Ordinal U) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                             → order-embedding τ υ f
                             → is-embedding f
order-embedding-is-embedding τ υ f (p , r) =
 lc-embedding f
  (order-embedding-lc τ υ f (p , r))
  (extensional-gives-is-set
    (underlying-order υ) fe
    (Prop-valuedness υ)
    (Extensionality υ))

\end{code}
