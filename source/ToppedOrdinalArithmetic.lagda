Martin Escardo, 29 June 2018

To get closure under sums constructively, we need to restrict to
particular kinds of ordinals. Having a top element is a simple
sufficient condition, which holds in the applications we have in mind
(for compact ordinals).  Classically, ordinals with a top element are
precisely the successor ordinals. Constructively, ℕ∞ is an example of
an ordinal with a top element, which "is not" a successor ordinal, as
its top element is not isolated.

TODO. Generalize this from 𝓤₀ to an arbitrary universe. The
(practical) problem is that the type of natural numbers is defined at
𝓤₀. We could (1) either using universe lifting, or (2) define the type
in any universe (like we did for the the types 𝟘 and 𝟙). But (1) is
cumbersome and (2) requires much work in other modules.


\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module ToppedOrdinalArithmetic
        (fe : FunExt)
       where

open import UF-Subsingletons

open import SpartanMLTT
open import OrdinalsType
open import OrdinalArithmetic fe
open import OrdinalsWellOrderArithmetic
open import ToppedOrdinalsType fe
open import OrdinalsType-Injectivity fe
open import GenericConvergentSequence
open import SquashedSum fe
open import CanonicalMapNotation

Ordᵀ = Ordinalᵀ 𝓤₀

succₒ : Ord → Ordᵀ
succₒ α = α +ₒ 𝟙ₒ  ,
          plus.top-preservation
           (underlying-order α)
           (underlying-order 𝟙ₒ)
           (prop.topped 𝟙 𝟙-is-prop ⋆)

succₒ-is-trichotomous : (α : Ord)
                      → is-trichotomous α
                      → is-trichotomous [ succₒ α ]
succₒ-is-trichotomous α t = +ₒ-is-trichotomous α 𝟙ₒ t 𝟙ₒ-is-trichotomous

𝟙ᵒ 𝟚ᵒ ℕ∞ᵒ : Ordᵀ
𝟙ᵒ  = 𝟙ₒ , prop.topped 𝟙 𝟙-is-prop ⋆
𝟚ᵒ  = succₒ 𝟙ₒ
ℕ∞ᵒ = (ℕ∞ₒ , ∞ , ∞-top)

\end{code}

Sum of an ordinal-indexed family of ordinals:

\begin{code}

∑ : (τ : Ordᵀ) → (⟪ τ ⟫ → Ordᵀ) → Ordᵀ
∑ ((X , _<_ , o) , t) υ = ((Σ x ꞉ X , ⟪ υ x ⟫) ,
                              Sum.order ,
                              Sum.well-order o (λ x → tis-well-ordered (υ x))) ,
                          Sum.top-preservation t
 where
  _≺_ : {x : X} → ⟪ υ x ⟫ → ⟪ υ x ⟫ → 𝓤₀ ̇
  y ≺ z = y ≺⟪ υ _ ⟫ z

  module Sum = sum-top fe _<_ _≺_ (λ x → top (υ x)) (λ x → top-is-top (υ x))

∑-is-trichotomous : (τ : Ordᵀ) (υ : ⟪ τ ⟫ → Ordᵀ)
                  → is-trichotomous [ τ ]
                  → ((x : ⟪ τ ⟫) → is-trichotomous [ υ x ])
                  → is-trichotomous [ ∑ τ υ ]
∑-is-trichotomous τ υ = sum.trichotomy-preservation _ _

\end{code}

Addition and multiplication can be reduced to ∑, given the ordinal 𝟚ᵒ
defined above:

\begin{code}

_+ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ +ᵒ υ = ∑ 𝟚ᵒ (cases (λ _ → τ) (λ _ → υ))

+ᵒ-is-trichotomous : (τ υ : Ordᵀ)
                   → is-trichotomous [ τ ]
                   → is-trichotomous [ υ ]
                   → is-trichotomous [ τ +ᵒ υ ]
+ᵒ-is-trichotomous τ υ t u = ∑-is-trichotomous 𝟚ᵒ (cases (λ _ → τ) (λ _ → υ))
                              𝟚ₒ-is-trichotomous
                              (dep-cases (λ _ → t) (λ _ → u))

_×ᵒ_ : Ordᵀ → Ordᵀ → Ordᵀ
τ ×ᵒ υ = ∑ τ  (λ (_ : ⟪ τ ⟫) → υ)

×ᵒ-is-trichotomous : (τ υ : Ordᵀ)
                   → is-trichotomous [ τ ]
                   → is-trichotomous [ υ ]
                   → is-trichotomous [ τ ×ᵒ υ ]
×ᵒ-is-trichotomous τ υ t u = ∑-is-trichotomous τ (λ _ → υ) t (λ _ → u)

\end{code}

Extension of a family X → Ordᵀ along an embedding j : X → A to get a
family A → Ordᵀ. (This can also be done for Ord-valued families.)
This uses the module UF-InjectiveTypes to calculate Y / j.

Sum of a countable family with an added non-isolated top element. We
first extend the family to ℕ∞ and then take the ordinal-indexed sum of
ordinals defined above.

\begin{code}

open topped-ordinals-injectivity

∑¹ : (ℕ → Ordᵀ) → Ordᵀ
∑¹ τ = ∑ ℕ∞ᵒ (τ ↗ embedding-ℕ-to-ℕ∞ (fe 𝓤₀ 𝓤₀))

\end{code}

And now with an isolated top element:

\begin{code}

∑₁ : (ℕ → Ordᵀ) → Ordᵀ
∑₁ τ = ∑ (succₒ ω) (τ ↗ (over , over-embedding))

\end{code}
