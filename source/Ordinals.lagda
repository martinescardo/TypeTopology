Martin Escardo, 29 June 2018

Some operations and constructions on ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module Ordinals
        (fe : ∀ U V → funext U V)
       where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Subsingletons
open import OrdinalNotions hiding (_≤_)
open import WellOrderArithmetic
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder hiding (_≤_) renaming (_<_ to _≺[ℕ]_)
open import UF-Embedding
open import UF-InjectiveTypes fe
open import SquashedSum fe
open import UF-Retracts
open import InfSearchable
open import LexicographicOrder
open import LexicographicSearch
open import ConvergentSequenceInfSearchable
open import PropInfTychonoff

U = U₀
V = U₁

Ord : V ̇
Ord = Σ \(X : U ̇) → Σ \(_<_ : X → X → U ̇) → is-well-order _<_

⟨_⟩ : Ord → U ̇
⟨ X , _<_ , o ⟩ = X

underlying-order : (α : Ord) → ⟨ α ⟩ → ⟨ α ⟩ → U ̇
underlying-order (X , _<_ , o) = _<_

syntax underlying-order α x y = x ≺⟨ α ⟩ y

is-well-ordered : (α : Ord) → is-well-order (underlying-order α)
is-well-ordered (X , _<_ , o) = o

subsingleton-ordinal : (P : U ̇) → is-prop P → Ord
subsingleton-ordinal P isp = P , subsingleton.order P isp , subsingleton.well-order P isp

𝟘ₒ 𝟙ₒ ℕₒ ℕ∞ₒ : Ord
𝟘ₒ = subsingleton-ordinal 𝟘 𝟘-is-prop
𝟙ₒ = subsingleton-ordinal 𝟙 𝟙-is-prop
ℕₒ = (ℕ , _≺[ℕ]_ , ℕ-ordinal)
ℕ∞ₒ = (ℕ∞ , _≺[ℕ∞]_ , ℕ∞-ordinal fe₀)

_+ₒ_ : Ord → Ord → Ord
(X , _<_ , o) +ₒ (Y , _≺_ , p) = (X + Y) ,
                                 plus.order _<_ _≺_ ,
                                 plus.well-order _<_ _≺_ o p

_×ₒ_ : Ord → Ord → Ord
(X , _<_ , o) ×ₒ (Y , _≺_ , p) = (X × Y) ,
                                 times.order _<_ _≺_ ,
                                 times.well-order _<_ _≺_ fe o p

prop-indexed-product : {P : U ̇} → is-prop P → (P → Ord) → Ord
prop-indexed-product {P} isp α = Π X ,
                                 _≺_ ,
                                 pip.well-order fe₀ P isp X _<_ (λ p → is-well-ordered (α p))
 where
  X : P → U ̇
  X p = ⟨ α p ⟩
  _<_ : {p : P} → X p → X p → U ̇
  _<_ {p} x y = x ≺⟨ α p ⟩ y
  _≺_ : Π X → Π X → U ̇
  f ≺ g = Σ \(p : P) → f p < g p

\end{code}

To get closure under sums constructively, we need further
assumptions. Having a top element is a simple sufficient condition,
which holds in the applications we have in mind (for searchable
ordinals).  Classically, these are the successor
ordinals. Constructively, ℕ∞ is an example of an ordinal with a top
element, which is not a successor ordinal, as its top element is not
isolated.

\begin{code}

Ordᵀ : V ̇
Ordᵀ = Σ \(α : Ord) → has-top (underlying-order α)

[_] : Ordᵀ → Ord
[ α , t ] = α

⟪_⟫ : Ordᵀ → U ̇
⟪ (X , _<_ , o) , t ⟫ = X

tunderlying-order : (τ : Ordᵀ) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-order ((X , _<_ , o) , t) = _<_

syntax tunderlying-order τ x y = x ≺⟪ τ ⟫ y

tunderlying-rorder : (τ : Ordᵀ) → ⟪ τ ⟫ → ⟪ τ ⟫ → U ̇
tunderlying-rorder τ x y = ¬(y ≺⟪ τ ⟫ x)

syntax tunderlying-rorder τ x y = x ≼⟪ τ ⟫ y

≼-prop-valued : (τ : Ordᵀ) (x y : ⟪ τ ⟫) → is-prop (x ≼⟪ τ ⟫ y)
≼-prop-valued τ x y l m = dfunext fe₀ (λ x → 𝟘-elim (m x))


topped : (τ : Ordᵀ) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordᵀ) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : (τ : Ordᵀ) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordᵀ) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

succₒ : Ord → Ordᵀ
succₒ α = α +ₒ 𝟙ₒ  ,
          plus.top-preservation
           (underlying-order α)
           (underlying-order 𝟙ₒ)
           (subsingleton.topped 𝟙 𝟙-is-prop *)

𝟙ᵒ 𝟚ᵒ ℕ∞ᵒ : Ordᵀ
𝟙ᵒ = 𝟙ₒ , subsingleton.topped 𝟙 𝟙-is-prop *
𝟚ᵒ = succₒ 𝟙ₒ
ℕ∞ᵒ = (ℕ∞ₒ , ∞ , ∞-top)

\end{code}

Sum of an ordinal indexed family of ordinals:

\begin{code}

∑ : {τ : Ordᵀ} → (⟪ τ ⟫ → Ordᵀ) → Ordᵀ
∑ {(X , _<_ , o) , t} υ = ((Σ \(x : X) → ⟪ υ x ⟫) ,
                            Sum.order ,
                            Sum.well-order o (λ x → tis-well-ordered (υ x))) ,
                          Sum.top-preservation t
 where
  _≺_ : {x : X} → ⟪ υ x ⟫ → ⟪ υ x ⟫ → U ̇
  y ≺ z = y ≺⟪ υ _ ⟫ z
  module Sum = sum-top fe _<_ _≺_ (λ x → top (υ x)) (λ x → top-is-top (υ x))

\end{code}

Addition and multiplication can be reduced to ∑, given the ordinal 𝟚ᵒ
defined above:

\begin{code}

_+ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ +ᵒ υ = ∑ {𝟚ᵒ} (cases (λ _ → τ) (λ _ → υ))

_×ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ ×ᵒ υ = ∑ {τ} \(_ : ⟪ τ ⟫) → υ

\end{code}

Extension of a family X → Ordᵀ along an embedding j : X → A to get a
family A → Ordᵀ. (This can also be done for Ord-valued families.)
This uses the module UF-InjectiveTypes to calculate Y / j.

\begin{code}

_↗_ : {X A : U ̇} → (X → Ordᵀ) → (Σ \(j : X → A) → is-embedding j) → (A → Ordᵀ)
τ ↗ (j , e) = λ a → ((Y / j) a ,
                     Extension.order a ,
                     Extension.well-order a (λ x → tis-well-ordered (τ x))) ,
                     Extension.top-preservation a (λ x → topped (τ x))
 where
  Y : dom τ → U ̇
  Y x = ⟪ τ x ⟫
  module Extension = extension fe Y j e (λ {x} → tunderlying-order (τ x))

\end{code}

Sum of a countable family with an added non-isolated top element. We
first extend the family to ℕ∞ and then take the ordinal-indexed sum of
ordinals defined above.

\begin{code}

∑¹ : (ℕ → Ordᵀ) → Ordᵀ
∑¹ τ = ∑ {ℕ∞ᵒ} (τ ↗ (under , under-embedding fe₀))

\end{code}

And now with an isolated top element:

\begin{code}

∑₁ : (ℕ → Ordᵀ) → Ordᵀ
∑₁ τ = ∑ {succₒ ℕₒ} (τ ↗ (over , over-embedding))

\end{code}

Some maps and their order preservation, used to show that the
embedding of the discrete ordinals into the searchable ordinals is
order preserving.

\begin{code}

order-preserving : (τ υ : Ordᵀ) →  (⟪ τ ⟫ → ⟪ υ ⟫) → U ̇
order-preserving τ υ f = (x y : ⟪ τ ⟫) → x ≺⟪ τ ⟫ y → f x ≺⟪ υ ⟫ f y

open import UF-Embedding

comp-order-preserving : (τ υ φ : Ordᵀ)  (f : ⟪ τ ⟫ → ⟪ υ ⟫) (g : ⟪ υ ⟫ → ⟪ φ ⟫)
                     → order-preserving τ υ f
                     → order-preserving υ φ g
                     → order-preserving τ φ (g ∘ f)
comp-order-preserving τ υ φ f g p q x y l = q (f x) (f y) (p x y l)

pair-fun-order-preserving : (τ υ : Ordᵀ) (A : ⟪ τ ⟫ → Ordᵀ) (B : ⟪ υ ⟫ → Ordᵀ)
                            (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                            (g  : (x : ⟪ τ ⟫) → ⟪ A x ⟫ → ⟪ B (f x) ⟫)
                         → order-preserving τ υ f
                         → ((x : ⟪ τ ⟫) → order-preserving (A x) (B (f x)) (g x))
                         → order-preserving (∑ {τ} A) (∑ {υ} B) (pair-fun f g)

pair-fun-order-preserving τ υ A B f g φ γ (x , a) (y , b) (inl l) = inl (φ x y l)
pair-fun-order-preserving τ υ A B f g φ γ (x , a) (.x , b) (inr (refl , l)) = inr (refl , γ x a b l)

under𝟙ᵒ : ⟪ succₒ ℕₒ ⟫ → ⟪ ℕ∞ᵒ ⟫
under𝟙ᵒ = under𝟙

under𝟙ᵒ-order-preserving : order-preserving (succₒ ℕₒ) ℕ∞ᵒ under𝟙ᵒ
under𝟙ᵒ-order-preserving (inl n) (inl m) l = under-order-preserving n m l
under𝟙ᵒ-order-preserving (inl n) (inr *) * = n , (refl , refl)
under𝟙ᵒ-order-preserving (inr *) (inl m) ()
under𝟙ᵒ-order-preserving (inr *) (inr *) ()

over-under-map-order-preserving  : (τ : ℕ → Ordᵀ) (z : ℕ + 𝟙)
                                → order-preserving
                                    ((τ ↗ (over , over-embedding)) z)
                                    ((τ ↗ (under , under-embedding fe₀)) (under𝟙 z))
                                    (over-under-map (λ n → ⟪ τ n ⟫) z)
over-under-map-order-preserving τ (inl n) x y ((.n , refl) , l) = (n , refl) , γ
 where
  γ : over-under-map (λ n → ⟪ τ n ⟫) (inl n) x (n , refl) ≺⟪ τ n ⟫
      over-under-map (λ n → ⟪ τ n ⟫) (inl n) y (n , refl)
  γ = back-transport₂
        (λ a b → tunderlying-order (τ n) a b)
        (over-under-map-left (λ n → ⟪ τ n ⟫) n x)
        (over-under-map-left (λ n → ⟪ τ n ⟫) n y)
        l
over-under-map-order-preserving τ (inr *) x y ((n , ()) , l)

∑-up : (τ : ℕ → Ordᵀ) → ⟪ ∑₁ τ ⟫ → ⟪ ∑¹ τ ⟫
∑-up τ = Σ-up (λ n → ⟪ τ n ⟫)

∑-up-order-preserving : (τ : ℕ → Ordᵀ)
                    → order-preserving (∑₁ τ) (∑¹ τ) (∑-up τ)
∑-up-order-preserving τ  = pair-fun-order-preserving
                            (succₒ ℕₒ)
                            ℕ∞ᵒ
                            (τ ↗ (over , over-embedding))
                            (τ  ↗ (under , under-embedding fe₀))
                            under𝟙ᵒ
                            (over-under-map (λ n → ⟪ τ n ⟫))
                            under𝟙ᵒ-order-preserving
                            (over-under-map-order-preserving τ)

∑↑ : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → ⟪ ∑₁ τ ⟫ → ⟪ ∑¹ υ ⟫
∑↑ τ υ = Σ↑ (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫)

Overᵒ : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → (z : ℕ + 𝟙) → ⟪ (τ ↗ (over , over-embedding)) z ⟫ → ⟪ (υ ↗ (over , over-embedding)) z ⟫
Overᵒ τ υ = Over (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫)

Overᵒ-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → ((n : ℕ) → order-preserving (τ n) (υ n) (f n))
   → (z : ℕ + 𝟙) → order-preserving
                      ((τ ↗ (over , over-embedding)) z)
                      ((υ ↗ (over , over-embedding)) z)
                      (Overᵒ τ υ f z)
Overᵒ-order-preserving τ υ f p (inl n) x y ((.n , refl) , l) = (n , refl) , p n _ _ l
Overᵒ-order-preserving τ υ f p (inr *) x y ((n , ()) , l)

∑₁-functor : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
           → ⟪ ∑₁ τ ⟫ → ⟪ ∑₁ υ ⟫
∑₁-functor τ ν = Σ₁-functor (λ n → ⟪ τ n ⟫) (λ n → ⟪ ν n ⟫)

∑₁-functor-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                            → ((n : ℕ) → order-preserving (τ n) (υ n) (f n))
                            → order-preserving (∑₁ τ) (∑₁ υ) (∑₁-functor τ υ f)
∑₁-functor-order-preserving τ υ f p =
 pair-fun-order-preserving
  (succₒ ℕₒ)
  (succₒ ℕₒ)
  (τ ↗ (over , over-embedding))
  (υ ↗ (over , over-embedding))
  id
  (Over (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫) f)
  (λ x y l → l)
  (Overᵒ-order-preserving τ υ f p)

∑↑-order-preserving : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                    → ((n : ℕ) → order-preserving (τ n) (υ n) (f n))
                    → order-preserving (∑₁ τ) (∑¹ υ) (∑↑ τ υ f)
∑↑-order-preserving τ υ f p = comp-order-preserving
                                 (∑₁ τ)
                                 (∑₁ υ )
                                 (∑¹ υ)
                                 (Σ₁-functor
                                    (λ n → ⟪ τ n ⟫)
                                    (λ n → ⟪ υ n ⟫)
                                    f)
                                 (∑-up υ)
                                 (∑₁-functor-order-preserving τ υ f p)
                                 (∑-up-order-preserving υ)
\end{code}

And now order reflection.

\begin{code}

order-reflecting : (τ υ : Ordᵀ) →  (⟪ τ ⟫ → ⟪ υ ⟫) → U ̇
order-reflecting τ υ f = (x y : ⟪ τ ⟫) → f x ≺⟪ υ ⟫ f y → x ≺⟪ τ ⟫ y

open import UF-Embedding

comp-order-reflecting : (τ υ φ : Ordᵀ)  (f : ⟪ τ ⟫ → ⟪ υ ⟫) (g : ⟪ υ ⟫ → ⟪ φ ⟫)
                     → order-reflecting τ υ f
                     → order-reflecting υ φ g
                     → order-reflecting τ φ (g ∘ f)
comp-order-reflecting τ υ φ f g p q x y l = p x y (q (f x) (f y) l)

pair-fun-order-reflecting : (τ υ : Ordᵀ) (A : ⟪ τ ⟫ → Ordᵀ) (B : ⟪ υ ⟫ → Ordᵀ)
                            (f : ⟪ τ ⟫ → ⟪ υ ⟫)
                            (g  : (x : ⟪ τ ⟫) → ⟪ A x ⟫ → ⟪ B (f x) ⟫)
                         → order-reflecting τ υ f
                         → is-embedding f
                         → ((x : ⟪ τ ⟫) → order-reflecting (A x) (B (f x)) (g x))
                         → order-reflecting (∑ {τ} A) (∑ {υ} B) (pair-fun f g)

pair-fun-order-reflecting τ υ A B f g φ e γ (x , a) (y , b) (inl l) = inl (φ x y l)
pair-fun-order-reflecting τ υ A B f g φ e γ (x , a) (y , b) (inr (r , l)) = inr (c r , p)
 where
  e' : is-equiv (ap f)
  e' = embedding-embedding' f e x y
  c : f x ≡ f y → x ≡ y
  c = pr₁(pr₁ e')
  η : (q : f x ≡ f y) → ap f (c q) ≡ q
  η = pr₂(pr₁ e')
  i : transport (λ - → ⟪ B (f -) ⟫) (c r) (g x a)
   ≡ transport (λ - → ⟪ B - ⟫) (ap f (c r)) (g x a)
  i = transport-ap (λ - → ⟪ B - ⟫) f (c r)
  j : transport (λ - → ⟪ B - ⟫) (ap f (c r)) (g x a) ≺⟪ B (f y) ⟫ (g y b)
  j = back-transport (λ - → transport (λ - → ⟪ B - ⟫) - (g x a) ≺⟪ B (f y) ⟫ (g y b)) (η r) l
  k : transport (λ - → ⟪ B (f -) ⟫) (c r) (g x a) ≺⟪ B (f y) ⟫ (g y b)
  k = back-transport (λ - → - ≺⟪ B (f y) ⟫ (g y b)) i j
  h : {x y : ⟪ τ ⟫} (s : x ≡ y) {a : ⟪ A x ⟫} {b : ⟪ A y ⟫}
   → transport (λ - → ⟪ B (f -) ⟫) s (g x a) ≺⟪ B (f y) ⟫ (g y b)
   → transport (λ - → ⟪ A - ⟫) s a ≺⟪ A y ⟫ b
  h {x} refl {a} {b} = γ x a b
  p : transport (λ - → ⟪ A - ⟫) (c r) a ≺⟪ A y ⟫ b
  p = h (c r) k

under𝟙ᵒ-order-reflecting : order-reflecting (succₒ ℕₒ) ℕ∞ᵒ under𝟙ᵒ
under𝟙ᵒ-order-reflecting (inl n) (inl m) l = under-order-reflecting n m l
under𝟙ᵒ-order-reflecting (inl n) (inr *) l = *
under𝟙ᵒ-order-reflecting (inr *) (inl m) (n , (p , l)) = 𝟘-elim (∞-is-not-ℕ n p)
under𝟙ᵒ-order-reflecting (inr *) (inr *) (n , (p , l)) = 𝟘-elim (∞-is-not-ℕ n p)

over-under-map-order-reflecting  : (τ : ℕ → Ordᵀ) (z : ℕ + 𝟙)
                                → order-reflecting
                                    ((τ ↗ (over , over-embedding)) z)
                                    ((τ ↗ (under , under-embedding fe₀)) (under𝟙 z))
                                    (over-under-map (λ n → ⟪ τ n ⟫) z)
over-under-map-order-reflecting τ (inl n) x y ((m , p) , l) = (n , refl) , q
 where
  x' : ⟪ τ n ⟫
  x' = over-under-map (λ n → ⟪ τ n ⟫) (inl n) x (n , refl)
  y' : ⟪ τ n ⟫
  y' = over-under-map (λ n → ⟪ τ n ⟫) (inl n) y (n , refl)
  r : n , refl ≡ m , p
  r = under-embedding fe₀ (under n) (n , refl) (m , p)
  t : ⟪ τ n ⟫ → ⟪ τ m ⟫
  t = transport (λ - → ⟪ τ (pr₁ -) ⟫) r
  tr : {w t : fiber under (under n)} (r : w ≡ t)
     → order-reflecting (τ (pr₁ w)) (τ (pr₁ t)) ((transport (λ - → ⟪ τ (pr₁ -) ⟫) r))
  tr refl x y l = l
  a : t x' ≡ over-under-map (λ n → ⟪ τ n ⟫) (inl n) x (m , p)
  a = apd (over-under-map (λ n → ⟪ τ n ⟫) (inl n) x) r
  b : t y' ≡ over-under-map (λ n → ⟪ τ n ⟫) (inl n) y (m , p)
  b = apd (over-under-map (λ n → ⟪ τ n ⟫) (inl n) y) r
  c : t x' ≺⟪ τ m ⟫ t y'
  c = back-transport₂ (λ a b → a ≺⟪ τ m ⟫ b) a b l
  d : x' ≺⟪ τ n ⟫ y'
  d = tr r _ _ c
  q : x (n , refl) ≺⟪ τ n ⟫ y (n , refl)
  q = transport₂
       (λ a b → a ≺⟪ τ n ⟫ b)
       (over-under-map-left (λ n → ⟪ τ n ⟫) n x)
       (over-under-map-left (λ n → ⟪ τ n ⟫) n y)
       d
over-under-map-order-reflecting τ (inr *) x y ((m , p) , l) = 𝟘-elim (∞-is-not-ℕ m (p ⁻¹))

∑-up-order-reflecting : (τ : ℕ → Ordᵀ)
                    → order-reflecting (∑₁ τ) (∑¹ τ) (∑-up τ)
∑-up-order-reflecting τ  = pair-fun-order-reflecting
                            (succₒ ℕₒ)
                            ℕ∞ᵒ
                            (τ ↗ (over , over-embedding))
                            (τ  ↗ (under , under-embedding fe₀))
                            under𝟙ᵒ
                            (over-under-map (λ n → ⟪ τ n ⟫))
                            under𝟙ᵒ-order-reflecting
                            (under𝟙-embedding fe₀)
                            (over-under-map-order-reflecting τ)

Overᵒ-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
   → ((n : ℕ) → order-reflecting (τ n) (υ n) (f n))
   → (z : ℕ + 𝟙) → order-reflecting
                      ((τ ↗ (over , over-embedding)) z)
                      ((υ ↗ (over , over-embedding)) z)
                      (Overᵒ τ υ f z)
Overᵒ-order-reflecting τ υ f p (inl n) x y ((.n , refl) , l) = (n , refl) , p n _ _ l
Overᵒ-order-reflecting τ υ f p (inr *) x y ((n , ()) , l)

∑₁-functor-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                            → ((n : ℕ) → order-reflecting (τ n) (υ n) (f n))
                            → order-reflecting (∑₁ τ) (∑₁ υ) (∑₁-functor τ υ f)
∑₁-functor-order-reflecting τ υ f p =
 pair-fun-order-reflecting
  (succₒ ℕₒ)
  (succₒ ℕₒ)
  (τ ↗ (over , over-embedding))
  (υ ↗ (over , over-embedding))
  id
  (Over (λ n → ⟪ τ n ⟫) (λ n → ⟪ υ n ⟫) f)
  (λ x y l → l)
  id-is-embedding
  (Overᵒ-order-reflecting τ υ f p)

∑↑-order-reflecting : (τ υ : ℕ → Ordᵀ) (f : (n : ℕ) → ⟪ τ n ⟫ → ⟪ υ n ⟫)
                    → ((n : ℕ) → order-reflecting (τ n) (υ n) (f n))
                    → order-reflecting (∑₁ τ) (∑¹ υ) (∑↑ τ υ f)
∑↑-order-reflecting τ υ f p = comp-order-reflecting
                                 (∑₁ τ)
                                 (∑₁ υ )
                                 (∑¹ υ)
                                 (Σ₁-functor
                                    (λ n → ⟪ τ n ⟫)
                                    (λ n → ⟪ υ n ⟫)
                                    f)
                                 (∑-up υ)
                                 (∑₁-functor-order-reflecting τ υ f p)
                                 (∑-up-order-reflecting υ)
\end{code}

28 July 2018. Inf searchability basics.

\begin{code}

𝟙ᵒ-inf-searchable : inf-searchable (λ x y → x ≼⟪ 𝟙ᵒ ⟫ y)
𝟙ᵒ-inf-searchable p = * , f , g , h
 where
  f : (Σ \(x : 𝟙) → p x ≡ ₀) → p * ≡ ₀
  f (* , r) = r
  g : (x : 𝟙) → p x ≡ ₀ → * ≼⟪ 𝟙ᵒ ⟫ x
  g * r ()
  h : (x : 𝟙) → root-lower-bound (λ x y → x ≼⟪ 𝟙ᵒ ⟫ y) p x
    → x ≼⟪ 𝟙ᵒ ⟫ *
  h * φ ()

𝟚ᵒ-inf-searchable : inf-searchable (λ x y → x ≼⟪ 𝟚ᵒ ⟫ y)
𝟚ᵒ-inf-searchable p = 𝟚-equality-cases φ γ
 where
  _≤_ : 𝟙 + 𝟙 → 𝟙 + 𝟙 → U ̇
  x ≤ y = x ≼⟪ 𝟚ᵒ ⟫ y
  φ : (r : p (inl *) ≡ ₀) → Σ \(x : 𝟙 + 𝟙) → conditional-root _≤_ p x × roots-infimum _≤_ p x
  φ r = inl * , f , g , h
   where
    f : (Σ \(x : 𝟙 + 𝟙) → p x ≡ ₀) → p (inl *) ≡ ₀
    f (inl * , s) = s
    f (inr * , s) = r
    g : (x : 𝟙 + 𝟙) → p x ≡ ₀ → inl * ≤ x
    g (inl *) s ()
    g (inr *) s ()
    h : (x : 𝟙 + 𝟙) → root-lower-bound _≤_ p x → x ≤ inl *
    h (inl *) φ ()
    h (inr *) φ * = φ (inl *) r *

  γ : (r : p (inl *) ≡ ₁) → Σ \(x : 𝟙 + 𝟙) → conditional-root _≤_ p x × roots-infimum _≤_ p x
  γ r = inr * , f , g , h
   where
    f : (Σ \(x : 𝟙 + 𝟙) → p x ≡ ₀) → p (inr *) ≡ ₀
    f (inl * , s) = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
    f (inr * , s) = s
    g : (x : 𝟙 + 𝟙) → p x ≡ ₀ → inr * ≤ x
    g (inl *) s l = 𝟘-elim (zero-is-not-one (s ⁻¹ ∙ r))
    g (inr *) s ()
    h : (x : 𝟙 + 𝟙) → root-lower-bound _≤_ p x → x ≤ inr *
    h (inl *) φ ()
    h (inr *) φ ()

\end{code}

It is not necessary to use propositional extensionality to prove the
following, but it is simpler to do so given that we have already
proved the inf-searchability for various types using different,
logically equivalent orders.

\begin{code}

∑-inf-searchable : propext U₀
                → (τ : Ordᵀ) (υ : ⟪ τ ⟫ → Ordᵀ)
                → inf-searchable (λ x y → x ≼⟪ τ ⟫ y)
                → ((x : ⟪ τ ⟫) → inf-searchable (λ a b → a ≼⟪ υ x ⟫ b))
                → inf-searchable (λ z t → z ≼⟪ ∑ {τ} υ ⟫ t)
∑-inf-searchable pe τ υ ε δ = γ
 where
  _≤_ : ⟪ ∑ {τ} υ ⟫ → ⟪ ∑ {τ} υ ⟫ → U₀ ̇
  _≤_ = lex-order (λ x y → x ≼⟪ τ ⟫ y) (λ {x} a b → a ≼⟪ υ x ⟫ b)
  ≤-prop-valued : (z t : ⟪ ∑ {τ} υ ⟫) → is-prop (z ≤ t)
  ≤-prop-valued (x , a) (y , b) (p , u) (q , v) =
   to-Σ-≡
    (≼-prop-valued τ x y p q ,
    dfunext fe₀ (λ r → ≼-prop-valued (υ y) _ _ _ _))
  φ : inf-searchable _≤_
  φ = Σ-inf-searchable ((λ x y → x ≼⟪ τ ⟫ y)) ((λ {x} a b → a ≼⟪ υ x ⟫ b)) ε δ
  open commutation (tunderlying-order τ) (λ {x} → tunderlying-order (υ x)) (𝟘 {U₀}) hiding (_≤_)
  i : (z t : ⟪ ∑ {τ} υ ⟫) → z ≤ t → z ≼⟪ ∑ {τ} υ ⟫ t
  i (x , a) (y , b) = back y x b a
  j : (z t : ⟪ ∑ {τ} υ ⟫) → z ≼⟪ ∑ {τ} υ ⟫ t → z ≤ t
  j (x , a) (y , b) = forth y x b a
  k : (z t : ⟪ ∑ {τ} υ ⟫) → z ≤ t ≡ z ≼⟪ ∑ {τ} υ ⟫ t
  k z t = pe (≤-prop-valued z t) (≼-prop-valued (∑ {τ} υ) z t) (i z t) (j z t)
  l : _≤_ ≡ (λ z t → z ≼⟪ ∑ {τ} υ ⟫ t)
  l = dfunext (fe U₀ U₁) λ z → dfunext (fe U₀ U₁) (k z)
  γ : inf-searchable (λ z t → z ≼⟪ ∑ {τ} υ ⟫ t)
  γ = transport inf-searchable l φ

∑₁-inf-searchable : propext U₀
                 → (τ : ℕ → Ordᵀ)
                 → ((n : ℕ) → inf-searchable λ x y → x ≼⟪ τ n ⟫ y)
                 → inf-searchable (λ z t → z ≼⟪ ∑¹ τ ⟫ t)
∑₁-inf-searchable pe τ ε =
 ∑-inf-searchable pe
 ℕ∞ᵒ
 (λ (x : ℕ∞) → (τ ↗ (under , under-embedding fe₀)) x)
 a
 b
 where
  p : GenericConvergentSequence._≼_ ≡ tunderlying-rorder ℕ∞ᵒ
  p = dfunext (fe U₀ U₁)
       (λ u → dfunext (fe U₀ U₁)
                (λ v → pe (≼-is-prop fe₀ u v)
                           (≼-prop-valued ℕ∞ᵒ u v)
                           (≼-not-≺ u v)
                           (not-≺-≼ fe₀ u v)))
  a : inf-searchable (tunderlying-rorder ℕ∞ᵒ)
  a = transport inf-searchable p (ℕ∞-inf-searchable fe₀)
  b : (x : ⟪ ℕ∞ᵒ ⟫) → inf-searchable
                         (tunderlying-rorder
                         ((τ ↗ (under , under-embedding fe₀)) x))
  b x = prop-inf-tychonoff fe (under-embedding fe₀ x)
         (λ {w} x y → x ≺⟪ τ (pr₁ w) ⟫ y)
         (λ w → ε (pr₁ w))

\end{code}
