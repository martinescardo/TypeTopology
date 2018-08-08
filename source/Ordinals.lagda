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

Ordinal : ∀ {U} → U ′ ̇
Ordinal {U} = Σ \(X : U ̇) → Σ \(_<_ : X → X → U ̇) → is-well-order _<_

⟨_⟩ : ∀ {U} → Ordinal {U} → U ̇
⟨ X , _<_ , o ⟩ = X

underlying-order : ∀ {U} → (α : Ordinal {U}) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

syntax underlying-order α x y = x ≺⟨ α ⟩ y

is-well-ordered : ∀ {U} → (α : Ordinal {U}) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for searchable
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordinalᵀ : ∀ {U} → U ′ ̇
Ordinalᵀ {U} = Σ \(α : Ordinal {U}) → has-top (underlying-order α)

[_] : ∀ {U} → Ordinalᵀ {U} → Ordinal {U}
[ α , t ] = α

⟪_⟫ : ∀ {U} → Ordinalᵀ {U} → U ̇
⟪ (X , _<_ , o) , t ⟫ = X

tunderlying-order : ∀ {U} → (τ : Ordinalᵀ {U}) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : ∀ {U} → (τ : Ordinalᵀ {U}) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : ∀ {U} → (τ : Ordinalᵀ {U}) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued {U} τ x y l m = dfunext (fe U U₀) (λ x → 𝟘-elim (m x))

topped : ∀ {U} → (τ : Ordinalᵀ {U}) → has-top (tunderlying-order τ)
topped (α , t) = t

top : ∀ {U} → (τ : Ordinalᵀ {U}) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : ∀ {U} → (τ : Ordinalᵀ {U}) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : ∀ {U} → (τ : Ordinalᵀ {U}) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

\end{code}

Maps.

\begin{code}

order-preserving  order-reflecting  order-embedding initial-segment simulation
 : ∀ {U} → (τ υ : Ordinal {U}) → (⟨ τ ⟩ → ⟨ υ ⟩) → U ̇

order-preserving τ υ f = (x y : ⟨ τ ⟩) → x ≺⟨ τ ⟩ y → f x ≺⟨ υ ⟩ f y
order-reflecting τ υ f = (x y : ⟨ τ ⟩) → f x ≺⟨ υ ⟩ f y → x ≺⟨ τ ⟩ y
order-embedding  τ υ f = order-preserving τ υ f × order-reflecting τ υ f
initial-segment  τ υ f = (x : ⟨ τ ⟩) (z : ⟨ υ ⟩)
                            → z ≺⟨ υ ⟩ f x → Σ \(y : ⟨ τ ⟩) → (y ≺⟨ τ ⟩ x) × (f y ≡ z)
simulation       τ υ f = initial-segment  τ υ f × order-preserving τ υ f

order-preserving-is-prop : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                        → is-prop (order-preserving τ υ f)
order-preserving-is-prop {U} τ υ f =
 Π-is-prop (fe U U)
   (λ x → Π-is-prop (fe U U)
             (λ y → Π-is-prop (fe U U)
                      (λ l → prop-valuedness
                              (underlying-order υ)
                              (is-well-ordered υ) (f x) (f y))))

order-reflecting-is-prop : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                        → is-prop (order-reflecting τ υ f)
order-reflecting-is-prop {U} τ υ f =
 Π-is-prop (fe U U)
   (λ x → Π-is-prop (fe U U)
             (λ y → Π-is-prop (fe U U)
                      (λ l → prop-valuedness
                              (underlying-order τ)
                              (is-well-ordered τ) x y)))


iplc : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
    → simulation τ υ f
    → left-cancellable f
iplc τ υ f (i , p) {x} {y} = γ x y
                              (well-foundedness (underlying-order τ) (is-well-ordered τ) x)
                              (well-foundedness (underlying-order τ) (is-well-ordered τ) y)
 where
  γ : ∀ x y → is-accessible (underlying-order τ) x → is-accessible (underlying-order τ) y
    → f x ≡ f y → x ≡ y
  γ x y (next .x s) (next .y t) r = extensionality (underlying-order τ) (is-well-ordered τ) x y g h
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

initial-segment-is-prop : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
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
          (prop-valuedness
            (underlying-order τ)
            (is-well-ordered τ) y' x)
            (extensional-gives-is-set
              (underlying-order υ) fe
                (prop-valuedness
                  (underlying-order υ)
                    (is-well-ordered υ))
                (extensionality
                  (underlying-order υ)
                  (is-well-ordered υ)))
         (transport (λ - →  (- ≺⟨ τ ⟩ x) × (f - ≡ z)) a (m , r))
         (m' , r')

simulation-is-prop : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                  → is-prop (simulation τ υ f)
simulation-is-prop τ υ f = ×-prop-criterion
                            (initial-segment-is-prop τ υ f ,
                             λ _ → order-preserving-is-prop τ υ f)

at-most-one-simulation : ∀ {U} (τ υ : Ordinal {U}) (f f' : ⟨ τ ⟩ → ⟨ υ ⟩)
                      → simulation τ υ f
                      → simulation τ υ f'
                      → f ∼ f'
at-most-one-simulation τ υ f f' (i , p) (i' , p') x =
 γ x (well-foundedness (underlying-order τ) (is-well-ordered τ) x)
 where
  γ : ∀ x → is-accessible (underlying-order τ) x → f x ≡ f' x
  γ x (next .x u) = extensionality (underlying-order υ) (is-well-ordered υ) (f x) (f' x) a b
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

_⊴_ : ∀ {U} → Ordinal {U} → Ordinal {U} → U ̇
τ ⊴ υ = Σ \(f : ⟨ τ ⟩ → ⟨ υ ⟩) → simulation τ υ f

⊴-is-prop : ∀ {U} (τ υ : Ordinal {U}) → is-prop (τ ⊴ υ)
⊴-is-prop {U} τ υ (f , s) (g , t) =
 to-Σ-≡ (dfunext (fe U U) (at-most-one-simulation τ υ f g s t) ,
         simulation-is-prop τ υ g _ _)

⊴-refl : ∀ {U} (τ : Ordinal {U}) → τ ⊴ τ
⊴-refl τ = id ,
           (λ x z l → z , l , refl) ,
           (λ x y l → l)

⊴-trans : ∀ {U} (τ υ φ : Ordinal {U}) → τ ⊴ υ → υ ⊴ φ → τ ⊴ φ
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

_↓_ : ∀ {U} (τ : Ordinal {U}) → ⟨ τ ⟩ → Ordinal {U}
τ ↓ a = (Σ \(y : ⟨ τ ⟩) → y ≺⟨ τ ⟩ a) , _<_ , p , w , e , t
 where
  _<_ : (Σ \(x : ⟨ τ ⟩) → x ≺⟨ τ ⟩ a) → (Σ \(x : ⟨ τ ⟩) → x ≺⟨ τ ⟩ a) → _ ̇
  (y , _) < (z , _) = y ≺⟨ τ ⟩ z
  p : is-prop-valued _<_
  p (x , _) (y , _)  = prop-valuedness (underlying-order τ) (is-well-ordered τ) x y
  w : is-well-founded _<_
  w (x , l) = γ x (well-foundedness (underlying-order τ) (is-well-ordered τ) x) l
   where
    γ : ∀ x → is-accessible (underlying-order τ) x → ∀ l → is-accessible _<_ (x , l)
    γ x (next .x s) l = next (x , l) (λ σ m → γ (pr₁ σ) (s (pr₁ σ) m) (pr₂ σ))
  e : is-extensional _<_
  e (x , l) (y , m) f g =
   to-Σ-≡
    (extensionality
     (underlying-order τ)
     (is-well-ordered τ)
     x
     y
     (λ u n → f (u , transitivity (underlying-order τ) (is-well-ordered τ) u x a n l) n)
     (λ u n → g (u , transitivity (underlying-order τ) (is-well-ordered τ) u y a n m) n) ,
    prop-valuedness (underlying-order τ) (is-well-ordered τ) y a _ _)
  t : is-transitive _<_
  t (x , _) (y , _) (z , _) l m = transitivity
                                   (underlying-order τ)
                                   (is-well-ordered τ)
                                   x y z l m

{- TODO next time.
_⊲_ : ∀ {U} → Ordinal {U} → Ordinal {U} → U ̇
τ ⊲ υ = {!!}
-}

\end{code}

And here are some additional observations:

\begin{code}

ilcr : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
    → initial-segment τ υ f
    → left-cancellable f
    → order-reflecting τ υ f
ilcr τ υ f i c x y l = γ
 where
  a : Σ \(x' : ⟨ τ ⟩) → (x' ≺⟨ τ ⟩ y) × (f x' ≡ f x)
  a = i y (f x) l
  γ : x ≺⟨ τ ⟩ y
  γ = transport (λ - → - ≺⟨ τ ⟩ y) (c (pr₂(pr₂ a))) (pr₁(pr₂ a))

ipr : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
   → simulation τ υ f
   → order-reflecting τ υ f
ipr τ υ f (i , p) = ilcr τ υ f i (iplc τ υ f (i , p))

order-embedding-lc : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                  → order-embedding τ υ f
                  → left-cancellable f
order-embedding-lc τ υ f (p , r) {x} {y} s = extensionality
                                              (underlying-order τ)
                                              (is-well-ordered τ)
                                              x y a b
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

order-embedding-is-embedding : ∀ {U} (τ υ : Ordinal {U}) (f : ⟨ τ ⟩ → ⟨ υ ⟩)
                             → order-embedding τ υ f
                             → is-embedding f
order-embedding-is-embedding τ υ f (p , r) = lc-embedding f
                                              (order-embedding-lc τ υ f (p , r))
                                              (extensional-gives-is-set
                                                (underlying-order υ)
                                                fe
                                                (prop-valuedness
                                                  (underlying-order υ)
                                                  (is-well-ordered υ))
                                                (extensionality
                                                  (underlying-order υ)
                                                  (is-well-ordered υ)))

\end{code}
