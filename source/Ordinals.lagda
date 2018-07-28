Martin Escardo, 29 June 2018

Some operations and constructions on ordinals.

\begin{code}

open import UF-FunExt

module Ordinals
        (fe : ∀ U V → funext U V)
       where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import OrdinalNotions
open import WellOrderArithmetic
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder renaming (_<_ to _≺[ℕ]_)
open import UF-Embedding
open import UF-InjectiveTypes fe
open import SquashedSum fe

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
