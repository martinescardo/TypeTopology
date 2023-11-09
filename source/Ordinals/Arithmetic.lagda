Martin Escardo, 29 June 2018

Some operations and constructions on ordinals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Ordinals.Arithmetic
        (fe : FunExt)
       where

open import CoNaturals.GenericConvergentSequence
open import MLTT.Spartan
open import Naturals.Order
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderArithmetic
open import UF.SubtypeClassifier
open import UF.Subsingletons

prop-ordinal : (P : 𝓤 ̇ ) → is-prop P → Ordinal 𝓤
prop-ordinal P i = P , prop.order P i , prop.well-order P i

Ω-to-ordinal : Ω 𝓤 → Ordinal 𝓤
Ω-to-ordinal (P , i) = prop-ordinal P i

prop-ordinal-is-trichotomous : (p : Ω 𝓤)
                             → is-trichotomous (Ω-to-ordinal p)
prop-ordinal-is-trichotomous (P , i) = prop.trichotomous P i

\end{code}

Here the subscript is the letter "o":

\begin{code}

𝟘ₒ 𝟙ₒ : {𝓤 : Universe} → Ordinal 𝓤
𝟘ₒ = Ω-to-ordinal ⊥
𝟙ₒ = Ω-to-ordinal ⊤

𝟘ₒ-is-not-𝟙ₒ : 𝟘ₒ {𝓤} ≠ 𝟙ₒ {𝓤}
𝟘ₒ-is-not-𝟙ₒ e = 𝟘-is-not-𝟙 (ap ⟨_⟩ e)

𝟘ₒ-is-trichotomous : is-trichotomous (𝟘ₒ {𝓤})
𝟘ₒ-is-trichotomous = prop-ordinal-is-trichotomous ⊥

𝟙ₒ-is-trichotomous : is-trichotomous (𝟙ₒ {𝓤})
𝟙ₒ-is-trichotomous = prop-ordinal-is-trichotomous ⊤

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

ω ℕ∞ₒ : Ord
ω = (ℕ , _<ℕ_ , ℕ-ordinal)
ℕ∞ₒ = (ℕ∞ , _≺ℕ∞_ , ℕ∞-ordinal (fe 𝓤₀ 𝓤₀))

ω-is-trichotomous : is-trichotomous ω
ω-is-trichotomous = <-trichotomous

\end{code}

There is trouble generalizing the type of the following definition of
ordinal addition to Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥). Check
plus.order to see why.

\begin{code}

_+ₒ_ : Ordinal 𝓤  → Ordinal 𝓤 → Ordinal 𝓤
(X , _<_ , o) +ₒ (Y , _≺_ , p) = (X + Y) ,
                                 plus.order _<_ _≺_ ,
                                 plus.well-order _<_ _≺_ o p

+ₒ-is-trichotomous : (α β : Ordinal 𝓤)
                   → is-trichotomous α
                   → is-trichotomous β
                   → is-trichotomous (α +ₒ β)
+ₒ-is-trichotomous α β = plus.trichotomy-preservation _ _

_×ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)
(X , _<_ , o) ×ₒ (Y , _≺_ , p) = (X × Y) ,
                                 times.order _<_ _≺_ ,
                                 times.well-order _<_ _≺_ fe o p

×ₒ-is-trichotomous : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                   → is-trichotomous α
                   → is-trichotomous β
                   → is-trichotomous (α ×ₒ β)
×ₒ-is-trichotomous α β = times.trichotomy-preservation _ _

𝟚ₒ : {𝓤 : Universe} → Ordinal 𝓤
𝟚ₒ = 𝟙ₒ +ₒ 𝟙ₒ

𝟚ₒ-is-trichotomous : is-trichotomous (𝟚ₒ {𝓤})
𝟚ₒ-is-trichotomous = +ₒ-is-trichotomous 𝟙ₒ 𝟙ₒ
                       𝟙ₒ-is-trichotomous
                       𝟙ₒ-is-trichotomous

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
             → Σ a ꞉ ⟨ α ⟩ , x ＝ inl a
less-is-left α (inl a) y l = a , refl
less-is-left α (inr *) (inl a) l = 𝟘-elim l
less-is-left α (inr *) (inr *) l = 𝟘-elim l

right-is-not-smaller : (α : Ord) (y : ⟨ α +ₒ 𝟙ₒ ⟩)
                     → ¬ (inr ⋆ ≺⟨ α +ₒ 𝟙ₒ ⟩ y)
right-is-not-smaller α (inl a) l = 𝟘-elim l
right-is-not-smaller α (inr ⋆) l = 𝟘-elim l

\end{code}

Added 3rd May 2022. Sums of ordinals indexed by ordinals don't always
exist. See the module OrdinalsShulmanTaboo. They do exist for
trichotomous and cotransitive ordinals. See the module
Ordinals.WellOrderArithmetic. Notice that trichotomy implies
cotransitivity. See the module OrdinalNotions. Both trichotomy and
cotransitivity are implied by excluded middle.

\begin{code}

open import UF.ExcludedMiddle

module sums-assuming-EM (em : EM 𝓤) where

 ∑ : (α : Ordinal 𝓤) → (⟨ α ⟩ → Ordinal 𝓤) → Ordinal 𝓤
 ∑ α@(X , _<_ , o) β = (Σ x ꞉ X , ⟨ β x ⟩) ,
                       Sum.order  ,
                       Sum.well-order o (λ x → is-well-ordered (β x))
  where
   _≺_ : {x : X} → ⟨ β x ⟩ → ⟨ β x ⟩ → 𝓤  ̇
   y ≺ z = y ≺⟨ β _ ⟩ z

   module Sum = sum-cotransitive fe _<_ _≺_ (em-gives-cotrans _<_ fe em (is-well-ordered α))

\end{code}

Added 23rd May 2022.

TODO. It is not in general possible to find a least element of an
inhabited ordinal. In fact, consider the ordinal P + 𝟙 where P is a
proposition. Then if we can find a least element of this ordinal, we
can decide whether P or ¬ P. Similarly, we can't find a top element,
unless excluded middle holds, by considering the ordinal 𝟙 + P.
