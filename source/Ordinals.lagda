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

order-preserving  order-reflecting  order-embedding initial-segment
 : ∀ {U} → (τ υ : Ordinalᵀ {U}) → (⟪ τ ⟫ → ⟪ υ ⟫) → U ̇

order-preserving τ υ f = (x y : ⟪ τ ⟫) → x ≺⟪ τ ⟫ y → f x ≺⟪ υ ⟫ f y
order-reflecting τ υ f = (x y : ⟪ τ ⟫) → f x ≺⟪ υ ⟫ f y → x ≺⟪ τ ⟫ y
order-embedding  τ υ f = order-preserving τ υ f × order-reflecting τ υ f
initial-segment  τ υ f = (x : ⟪ τ ⟫) (z : ⟪ υ ⟫)
                           → z ≺⟪ υ ⟫ f x → Σ \(y : ⟪ τ ⟫) → (y ≺⟪ τ ⟫ x) × (f y ≡ z)

iplc : ∀ {U} (τ υ : Ordinalᵀ {U}) (f : ⟪ τ ⟫ → ⟪ υ ⟫)
    → initial-segment τ υ f
    → order-preserving τ υ f
    → left-cancellable f
iplc τ υ f i p {x} {y} = γ x y
                           (well-foundedness (tunderlying-order τ) (tis-well-ordered τ) x)
                           (well-foundedness (tunderlying-order τ) (tis-well-ordered τ) y)
 where
  γ : ∀ x y → is-accessible (tunderlying-order τ) x → is-accessible (tunderlying-order τ) y
    → f x ≡ f y → x ≡ y
  γ x y (next .x s) (next .y t) r = extensionality (tunderlying-order τ) (tis-well-ordered τ) x y g h
   where
    g : (u : ⟪ τ ⟫) → u ≺⟪ τ ⟫ x → u ≺⟪ τ ⟫ y
    g u l = d
     where
      a : f u ≺⟪ υ ⟫ f y
      a = transport (λ - → f u ≺⟪ υ ⟫ -) r (p u x l)
      b : Σ \(v : ⟪ τ ⟫) → (v ≺⟪ τ ⟫ y) × (f v ≡ f u)
      b = i y (f u) a
      c : u ≡ pr₁ b
      c = γ u (pr₁ b) (s u l) (t (pr₁ b) (pr₁(pr₂ b))) ((pr₂ (pr₂ b))⁻¹)
      d : u ≺⟪ τ ⟫ y
      d = transport (λ - → - ≺⟪ τ ⟫ y) (c ⁻¹) (pr₁(pr₂ b))
    h : (u : ⟪ τ ⟫) → u ≺⟪ τ ⟫ y → u ≺⟪ τ ⟫ x
    h u l = d
     where
      a : f u ≺⟪ υ ⟫ f x
      a = transport (λ - → f u ≺⟪ υ ⟫ -) (r ⁻¹) (p u y l)
      b : Σ \(v : ⟪ τ ⟫) → (v ≺⟪ τ ⟫ x) × (f v ≡ f u)
      b = i x (f u) a
      c : pr₁ b ≡ u
      c = γ (pr₁ b) u (s (pr₁ b) (pr₁(pr₂ b))) (t u l) (pr₂(pr₂ b))
      d : u ≺⟪ τ ⟫ x
      d = transport (λ - → - ≺⟪ τ ⟫ x) c (pr₁(pr₂ b))

initial-segment-is-prop : ∀ {U} (τ υ : Ordinalᵀ {U}) (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                       → order-preserving τ υ f
                       → is-prop (initial-segment τ υ f)
initial-segment-is-prop {U} τ υ f p i =
 (Π-is-prop (fe U U)
    λ x → Π-is-prop (fe U U)
            λ z → Π-is-prop (fe U U)
                    λ l → γ x z l) i
  where
   γ : ∀ x z → z ≺⟪ υ ⟫ f x → is-prop(Σ \(y : ⟪ τ ⟫) → (y ≺⟪ τ ⟫ x) × (f y ≡ z))
   γ x z l (y , (m , r)) (y' , (m' , r')) = to-Σ-≡ (a , b)
    where
     c : f y ≡ f y'
     c = r ∙ r' ⁻¹
     a : y ≡ y'
     a = iplc τ υ f i p c
     b : transport (λ - →  (- ≺⟪ τ ⟫ x) × (f - ≡ z)) a (m , r) ≡ m' , r'
     b = ×-is-prop
          (prop-valuedness
            (tunderlying-order τ)
            (tis-well-ordered τ) y' x)
            (extensional-gives-is-set
              (tunderlying-order υ) fe
                (prop-valuedness
                  (tunderlying-order υ)
                    (tis-well-ordered υ))
                (extensionality
                  (tunderlying-order υ)
                  (tis-well-ordered υ)))
         (transport (λ - →  (- ≺⟪ τ ⟫ x) × (f - ≡ z)) a (m , r))
         (m' , r')

ilcr : ∀ {U} (τ υ : Ordinalᵀ {U}) (f : ⟪ τ ⟫ → ⟪ υ ⟫)
    → initial-segment τ υ f
    → left-cancellable f
    → order-reflecting τ υ f
ilcr τ υ f i c x y l = γ
 where
  a : Σ \(x' : ⟪ τ ⟫) → (x' ≺⟪ τ ⟫ y) × (f x' ≡ f x)
  a = i y (f x) l
  γ : x ≺⟪ τ ⟫ y
  γ = transport (λ - → - ≺⟪ τ ⟫ y) (c (pr₂(pr₂ a))) (pr₁(pr₂ a))

ipr : ∀ {U} (τ υ : Ordinalᵀ {U}) (f : ⟪ τ ⟫ → ⟪ υ ⟫)
   → initial-segment τ υ f
   → order-preserving τ υ f
   → order-reflecting τ υ f
ipr τ υ f i p = ilcr τ υ f i (iplc τ υ f i p)

order-embedding-lc : ∀ {U} (τ υ : Ordinalᵀ {U}) (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                  → order-embedding τ υ f
                  → left-cancellable f
order-embedding-lc τ υ f (p , r) {x} {y} s = extensionality
                                              (tunderlying-order τ)
                                              (tis-well-ordered τ)
                                              x y a b
 where
  a : (u : ⟪ τ ⟫) → u ≺⟪ τ ⟫ x → u ≺⟪ τ ⟫ y
  a u l = r u y j
   where
    i : f u ≺⟪ υ ⟫ f x
    i = p u x l
    j : f u ≺⟪ υ ⟫ f y
    j = transport (λ - → f u ≺⟪ υ ⟫ -) s i
  b : (u : ⟪ τ ⟫) → u ≺⟪ τ ⟫ y → u ≺⟪ τ ⟫ x
  b u l = r u x j
   where
    i : f u ≺⟪ υ ⟫ f y
    i = p u y l
    j : f u ≺⟪ υ ⟫ f x
    j = back-transport (λ - → f u ≺⟪ υ ⟫ -) s i

order-embedding-is-embedding : ∀ {U} (τ υ : Ordinalᵀ {U}) (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                             → order-embedding τ υ f
                             → is-embedding f
order-embedding-is-embedding τ υ f (p , r) = lc-embedding f
                                              (order-embedding-lc τ υ f (p , r))
                                              (extensional-gives-is-set
                                                (tunderlying-order υ)
                                                fe
                                                (prop-valuedness
                                                  (tunderlying-order υ)
                                                  (tis-well-ordered υ))
                                                (extensionality
                                                  (tunderlying-order υ)
                                                  (tis-well-ordered υ)))

\end{code}
