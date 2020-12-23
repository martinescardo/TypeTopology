Martin Escardo, 29 June 2018

Some operations and constructions on ordinals.

TODO. Generalize this from 𝓤₀ to an arbitrary universe. The
(practical) problem is that the type of natural numbers is defined at
𝓤₀. We could (1) either using universe lifting, or (2) define the type
in any universe (like we did for the the types 𝟘 and 𝟙). But (1) is
cumbersome and (2) requires much work in other modules.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalArithmetic
        (fe : FunExt)
       where


open import OrdinalsType fe
open import OrdinalsWellOrderArithmetic
open import GenericConvergentSequence renaming (_≺_ to _≺[ℕ∞]_)
open import NaturalsOrder hiding (_≤_) renaming (_<_ to _≺[ℕ]_)
open import UF-Subsingletons
open import UF-Embeddings

Ord  = Ordinal  𝓤₀

prop-ordinal : (P : 𝓤₀ ̇ ) → is-prop P → Ord
prop-ordinal P i = P , prop.order P i , prop.well-order P i

𝟘ₒ 𝟙ₒ ℕₒ ℕ∞ₒ : Ord
𝟘ₒ = prop-ordinal 𝟘 𝟘-is-prop
𝟙ₒ = prop-ordinal 𝟙 𝟙-is-prop
ℕₒ = (ℕ , _≺[ℕ]_ , ℕ-ordinal)
ℕ∞ₒ = (ℕ∞ , _≺[ℕ∞]_ , ℕ∞-ordinal (fe 𝓤₀ 𝓤₀))

_+ₒ_ : Ord → Ord → Ord
(X , _<_ , o) +ₒ (Y , _≺_ , p) = (X + Y) ,
                                 plus.order _<_ _≺_ ,
                                 plus.well-order _<_ _≺_ o p

_×ₒ_ : Ord → Ord → Ord
(X , _<_ , o) ×ₒ (Y , _≺_ , p) = (X × Y) ,
                                 times.order _<_ _≺_ ,
                                 times.well-order _<_ _≺_ fe o p

prop-indexed-product : {P : 𝓤₀ ̇ } → is-prop P → (P → Ord) → Ord
prop-indexed-product {P} i α = Π X ,
                               _≺_ ,
                               pip.well-order (fe 𝓤₀ 𝓤₀) P i X _<_
                                  (λ p → is-well-ordered (α p))
 where
  X : P → 𝓤₀ ̇
  X p = ⟨ α p ⟩

  _<_ : {p : P} → X p → X p → 𝓤₀ ̇
  _<_ {p} x y = x ≺⟨ α p ⟩ y

  _≺_ : Π X → Π X → 𝓤₀ ̇
  f ≺ g = Σ p ꞉ P , f p < g p

\end{code}

Miscelanea:

\begin{code}

less-is-left : (α : Ord) (x y : ⟨ α +ₒ 𝟙ₒ ⟩)
             → x ≺⟨ α +ₒ 𝟙ₒ ⟩ y
             → Σ a ꞉ ⟨ α ⟩ , x ≡ inl a
less-is-left α (inl a) y l = a , refl
less-is-left α (inr *) (inl a) l = 𝟘-elim l
less-is-left α (inr *) (inr *) l = 𝟘-elim l

right-is-not-smaller : (α : Ord) (y : ⟨ α +ₒ 𝟙ₒ ⟩) → ¬ (inr * ≺⟨ α +ₒ 𝟙ₒ ⟩ y)
right-is-not-smaller α (inl a) l = 𝟘-elim l
right-is-not-smaller α (inr *) l = 𝟘-elim l

\end{code}
