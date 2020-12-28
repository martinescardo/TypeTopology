Martin Escardo, 29 June 2018

Some operations and constructions on ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module OrdinalArithmetic
        (fe : FunExt)
       where

open import SpartanMLTT
open import OrdinalNotions
open import OrdinalsType
open import OrdinalsWellOrderArithmetic
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder hiding (_≤_) renaming (_<_ to _≺[ℕ]_)

open import UF-Subsingletons

prop-ordinal : (P : 𝓤 ̇ ) → is-prop P → Ordinal 𝓤
prop-ordinal P i = P , prop.order P i , prop.well-order P i

\end{code}

Here the subscript is the letter "o":

\begin{code}

𝟘ₒ 𝟙ₒ : {𝓤 : Universe} → Ordinal 𝓤
𝟙ₒ = prop-ordinal 𝟙 𝟙-is-prop
𝟘ₒ = prop-ordinal 𝟘 𝟘-is-prop

\end{code}

Here the subscript is the number "0" on the left and the letter "o" on
the righthand side of the equality sign:

\begin{code}

𝟘₀ 𝟙₀ : Ord
𝟘₀ = 𝟘ₒ
𝟙₀ = 𝟙ₒ

\end{code}

Here the subscript is the letter "o":

\begin{code}

ℕₒ ℕ∞ₒ : Ord
ℕₒ = (ℕ , _≺[ℕ]_ , ℕ-ordinal)
ℕ∞ₒ = (ℕ∞ , _≺[ℕ∞]_ , ℕ∞-ordinal (fe 𝓤₀ 𝓤₀))

\end{code}

There is trouble generalizing the type of the following definition of
ordinal addition to Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥). Check
plus.order to see why.

\begin{code}

_+ₒ_ : Ordinal 𝓤  → Ordinal 𝓤 → Ordinal 𝓤
(X , _<_ , o) +ₒ (Y , _≺_ , p) = (X + Y) ,
                                 plus.order _<_ _≺_ ,
                                 plus.well-order _<_ _≺_ o p

_×ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
(X , _<_ , o) ×ₒ (Y , _≺_ , p) = (X × Y) ,
                                 times.order _<_ _≺_ ,
                                 times.well-order _<_ _≺_ fe o p

prop-indexed-product : {P : 𝓤 ̇ }
                     → is-prop P
                     → (P → Ordinal 𝓥)
                     → Ordinal (𝓤 ⊔ 𝓥)
prop-indexed-product {𝓤} {𝓥} {P} i α = Π X , _≺_ , w
 where
  X : P → 𝓥 ̇
  X p = ⟨ α p ⟩

  _<_ : {p : P} → X p → X p → 𝓥 ̇
  _<_ {p} x y = x ≺⟨ α p ⟩ y

  _≺_ : Π X → Π X → 𝓤 ⊔ 𝓥 ̇
  f ≺ g = Σ p ꞉ P , f p < g p

  w : is-well-order _≺_
  w = pip.well-order (fe 𝓤 𝓥) P i X _<_ (λ p → is-well-ordered (α p))

\end{code}

Miscelanea:

\begin{code}

less-is-left : (α : Ord) (x y : ⟨ α +ₒ 𝟙ₒ ⟩)
             → x ≺⟨ α +ₒ 𝟙ₒ ⟩ y
             → Σ a ꞉ ⟨ α ⟩ , x ≡ inl a
less-is-left α (inl a) y l = a , refl
less-is-left α (inr *) (inl a) l = 𝟘-elim l
less-is-left α (inr *) (inr *) l = 𝟘-elim l

right-is-not-smaller : (α : Ord) (y : ⟨ α +ₒ 𝟙ₒ ⟩)
                     → ¬ (inr * ≺⟨ α +ₒ 𝟙ₒ ⟩ y)
right-is-not-smaller α (inl a) l = 𝟘-elim l
right-is-not-smaller α (inr *) l = 𝟘-elim l

\end{code}
