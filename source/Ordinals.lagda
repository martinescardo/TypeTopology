Martin Escardo, 29 June 2018

Some operations on ordinals, and some of their preservation properties.

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
open import ConvergentSequenceSearchable
open import NaturalsOrder renaming (_<_ to _≺[ℕ]_)
open import UF-Embedding
open import UF-InjectiveTypes fe
open import SearchableTypes
open import SquashedSum fe
open import DiscreteAndSeparated
open import UF-SetExamples

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
ℕ∞ₒ = (ℕ∞ , _≺[ℕ∞]_ , ℕ∞-ordinal (fe U U))

_+ₒ_ : Ord → Ord → Ord
(X , _<_ , o) +ₒ (Y , _≺_ , p) = (X + Y) ,
                                 plus.order _<_ _≺_ ,
                                 plus.well-order _<_ _≺_ o p
succₒ : Ord → Ord
succₒ X = X +ₒ 𝟙ₒ

_×ₒ_ : Ord → Ord → Ord
(X , _<_ , o) ×ₒ (Y , _≺_ , p) = (X × Y) ,
                                 times.order _<_ _≺_ ,
                                 times.well-order _<_ _≺_ fe o p

prop-indexed-product : {P : U ̇} → is-prop P → (P → Ord) → Ord
prop-indexed-product {P} isp α = Π X ,
                                 _≺_ ,
                                 pip.well-order (fe U U) P isp X _<_ (λ p → is-well-ordered (α p))
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

topped : (τ : Ordᵀ) → has-top (tunderlying-order τ)
topped (α , t) = t

top : (τ : Ordᵀ) → ⟪ τ ⟫
top (α , (x , i)) = x

top-is-top : (τ : Ordᵀ) → is-top (tunderlying-order τ) (top τ)
top-is-top (α , (x , i)) = i

tis-well-ordered : (τ : Ordᵀ) → is-well-order (tunderlying-order τ)
tis-well-ordered ((X , _<_ , o) , t) = o

𝟙º 𝟚º ℕ∞º : Ordᵀ
𝟙º = 𝟙ₒ , subsingleton.topped 𝟙 𝟙-is-prop *
𝟚º = 𝟙ₒ +ₒ 𝟙ₒ ,
     plus.top-preservation (underlying-order 𝟙ₒ) (underlying-order 𝟙ₒ) (topped 𝟙º)
ℕ∞º = (ℕ∞ₒ , ∞ , ∞-top)

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

Addition and multiplication can be reduced to ∑, given the ordinal 𝟚º
defined above:

\begin{code}

_+º_ : Ordᵀ → Ordᵀ → Ordᵀ
τ +º υ = ∑ {𝟚º} (cases (λ _ → τ) (λ _ → υ))

_×º_ : Ordᵀ → Ordᵀ → Ordᵀ
τ ×º υ = ∑ {τ} \(_ : ⟪ τ ⟫) → υ

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
∑¹ τ = ∑ {ℕ∞º} (τ ↗ (under , under-embedding (fe U U)))

\end{code}

And now with an isolated top element:

\begin{code}

∑₁ : (ℕ → Ordᵀ) → Ordᵀ
∑₁ ν = (((Σ X) + 𝟙) , _<_ , w) ,
       (inr * , ist)
 where
  X : ℕ → U ̇
  X n = ⟪ ν n ⟫
  _≺_ : Σ X → Σ X → U ̇
  _≺_ = sum.order _≺[ℕ]_ (λ {n} → tunderlying-order (ν n))
  _<_ : (Σ X) + 𝟙 → (Σ X) + 𝟙 → U ̇
  _<_ = plus.order _≺_ (underlying-order 𝟙ₒ)
  w : is-well-order _<_
  w = plus.well-order _≺_ (underlying-order 𝟙ₒ)
       (sum-cotransitive.well-order fe _≺[ℕ]_ (λ {n} → tunderlying-order (ν n))
         ℕ-cotransitive
         ℕ-ordinal
         (λ n → is-well-ordered [ ν n ]))
       (is-well-ordered 𝟙ₒ)
  ist : is-top _<_ (inr *)
  ist (inl σ) ()
  ist (inr *) ()

\end{code}

Preservation of searchability of underlying sets.

\begin{code}

usearchable : Ordᵀ → U ̇
usearchable τ = searchable ⟪ τ ⟫

𝟙-usearchable : usearchable 𝟙º
𝟙-usearchable = 𝟙-searchable

𝟚-usearchable : usearchable 𝟚º
𝟚-usearchable = 𝟙+𝟙-searchable

ℕ∞-usearchable : usearchable ℕ∞º
ℕ∞-usearchable = ℕ∞-searchable (fe U U)

∑-usearchable : (τ : Ordᵀ)
             → (υ : ⟪ τ ⟫ → Ordᵀ)
             → usearchable τ
             → ((x : ⟪ τ ⟫) → usearchable (υ x))
             → usearchable (∑ {τ} υ)
∑-usearchable τ υ = Σ-searchable

+º-usearchable : (τ υ : Ordᵀ)
              → usearchable τ
              → usearchable υ
              → usearchable (τ +º υ)
+º-usearchable τ υ ε δ = ∑-usearchable 𝟚º (cases (λ _ → τ) (λ _ → υ)) 𝟚-usearchable g
 where
  g : (x : 𝟙 + 𝟙) → usearchable (cases (λ _ → τ) (λ _ → υ) x)
  g (inl *) = ε
  g (inr *) = δ

×º-usearchable : (τ υ : Ordᵀ)
              → usearchable τ
              → usearchable υ
              → usearchable (τ ×º υ)
×º-usearchable τ υ ε δ = ∑-usearchable τ (λ _ → υ) ε (λ _ → δ)

∑¹-usearchable : (τ : ℕ → Ordᵀ)
               → ((n : ℕ) → usearchable (τ n))
               → usearchable (∑¹ τ)
∑¹-usearchable τ = squashed-sum-searchable (λ n → ⟪ τ n ⟫)

\end{code}

Preservation of the discreteness of underlying sets:

\begin{code}

udiscrete : Ordᵀ → U ̇
udiscrete τ = discrete ⟪ τ ⟫

𝟙-udiscrete : udiscrete 𝟙º
𝟙-udiscrete = 𝟙-discrete

𝟚-udiscrete : udiscrete 𝟚º
𝟚-udiscrete = +discrete 𝟙-discrete 𝟙-discrete

∑-udiscrete : (τ : Ordᵀ)
             → (υ : ⟪ τ ⟫ → Ordᵀ)
             → udiscrete τ
             → ((x : ⟪ τ ⟫) → udiscrete (υ x))
             → udiscrete (∑ {τ} υ)
∑-udiscrete τ υ = Σ-discrete

+udiscrete : (τ υ : Ordᵀ)
           → udiscrete τ
           → udiscrete υ
           → udiscrete (τ +º υ)
+udiscrete τ υ ε δ = ∑-udiscrete 𝟚º (cases (λ _ → τ) (λ _ → υ)) 𝟚-udiscrete g
 where
  g : (x : 𝟙 + 𝟙) → udiscrete (cases (λ _ → τ) (λ _ → υ) x)
  g (inl *) = ε
  g (inr *) = δ

×udiscrete : (τ υ : Ordᵀ)
            → udiscrete τ
            → udiscrete υ
            → udiscrete (τ ×º υ)
×udiscrete τ υ ε δ = ∑-udiscrete τ (λ _ → υ) ε (λ _ → δ)

∑₁-udiscrete : (τ : ℕ → Ordᵀ)
             → ((n : ℕ) → udiscrete (τ n))
             → udiscrete (∑₁ τ)
∑₁-udiscrete τ d = +discrete (Σ-discrete ℕ-discrete d) 𝟙-discrete

\end{code}

It is no use for a type to be searchable if it doesn't have enough
functions into the booleans to separate the points, that is, if it
fails to be totally separated.

Our proof method is to show that it preserves a stronger condition
(interesting on its own right), namely being a retract of the cantor
type (ℕ → 𝟚), as retractions preserve total separatedness.

A direct proof doesn't seem to be possible, as in general sums don't
preserve total separatedness, as illustrated by a simple example in
the module FailureOfTotalSeparatedness.

\begin{code}

open import SquashedCantor fe
open import UF-Retracts
open import UF-Retracts-FunExt

Cantor-retract : Ordᵀ → U ̇
Cantor-retract τ = retract ⟪ τ ⟫ of Cantor

𝟙-Cantor-retract : Cantor-retract 𝟙º
𝟙-Cantor-retract = (λ _ → *) , (λ _ → λ n → ₀) , (λ x → 𝟙-is-prop * x)

ℕ∞-Cantor-retract : Cantor-retract ℕ∞º
ℕ∞-Cantor-retract = ℕ∞-retract-of-Cantor fe₀

\end{code}

The complication of the following proof is that the ordinal 𝟚º has
underlying set 𝟙+𝟙 rather than 𝟚, and that (hence) we defined the
ordinal +º as a sum indexed by 𝟙+𝟙 rather than as a co-product. This
saved lots of code elsewhere, but adds labour here (and in some helper
lemmas/constructions that we added in other modules for this
purpose). Notice that +' is the sum indexed by 𝟚, defined in the
module SpartanMLTT.

\begin{code}

+º-Cantor-retract : (τ ν : Ordᵀ)
                 → Cantor-retract τ
                 → Cantor-retract ν
                 → Cantor-retract (τ +º ν)
+º-Cantor-retract τ ν ρ σ = retracts-compose d e
 where
  a : retract (Cantor +' Cantor) of (Cantor + Cantor)
  a = +'-retract-of-+
  b : retract (Cantor +' Cantor) of Cantor
  b = retracts-compose +-Cantor-retract a
  c : retract ⟪ τ ⟫ +' ⟪ ν ⟫ of (Cantor +' Cantor)
  c = +'-retract ρ σ
  d : retract ⟪ τ ⟫ +' ⟪ ν ⟫ of Cantor
  d = retracts-compose b c
  e : retract ⟪ τ +º ν ⟫ of (⟪ τ ⟫ +' ⟪ ν ⟫)
  e = transport (λ - → retract ⟪ τ +º ν ⟫ of (Σ -)) (dfunext (fe U₀ (U₀ ′)) l) h
   where
    f : 𝟚 → 𝟙 + 𝟙
    f = 𝟚-cases (inl *) (inr *)
    g : 𝟙 + 𝟙 → 𝟚
    g = cases (λ x → ₀) (λ x → ₁)
    fg : (x : 𝟙 + 𝟙) → f (g x) ≡ x
    fg (inl *) = ap inl refl
    fg (inr *) = ap inr refl
    h : retract ⟪ τ +º ν ⟫ of (Σ \(i : 𝟚) → ⟪ cases (λ _ → τ) (λ _ → ν) (f i) ⟫)
    h = Σ-reindex-retract f (g , fg)
    l : (i : 𝟚) → ⟪ cases (λ _ → τ) (λ _ → ν) (f i) ⟫
                ≡ 𝟚-cases ⟪ τ ⟫ ⟪ ν ⟫ i
    l ₀ = refl
    l ₁ = refl

×º-Cantor-retract : (τ ν : Ordᵀ)
                 → Cantor-retract τ
                 → Cantor-retract ν
                 → Cantor-retract (τ ×º ν)
×º-Cantor-retract τ ν ρ σ = retracts-compose a b
 where
  a : retract (Cantor × Cantor) of Cantor
  a = pair-seq-retract fe₀
  b : retract ⟪ τ ⟫ × ⟪ ν ⟫ of (Cantor × Cantor)
  b = ×-retract ρ σ

∑¹-Cantor-retract : (τ : ℕ → Ordᵀ)
                 → ((n : ℕ) → Cantor-retract (τ n))
                 → Cantor-retract (∑¹ τ)
∑¹-Cantor-retract τ = squashed-Cantor-retract (λ n → ⟪ τ n ⟫)

\end{code}
