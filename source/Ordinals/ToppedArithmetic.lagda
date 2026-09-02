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

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Ordinals.ToppedArithmetic
        (fe : FunExt)
       where

open import CoNaturals.Type
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.Injectivity
open import Ordinals.Notions
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderArithmetic
open import TypeTopology.SquashedSum fe
open import UF.ClassicalLogic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

private
 fe₀ = fe 𝓤₀ 𝓤₀

Ordᵀ = Ordinalᵀ 𝓤₀

succₒ : Ordinal 𝓤 → Ordinalᵀ 𝓤
succₒ α = α +ₒ 𝟙ₒ  ,
          plus.top-preservation
           (underlying-order α)
           (underlying-order 𝟙ₒ)
           (prop.topped 𝟙 𝟙-is-prop ⋆)

succₒ-is-trichotomous : (α : Ordinal 𝓤)
                      → is-trichotomous α
                      → is-trichotomous [ succₒ α ]
succₒ-is-trichotomous α t = +ₒ-is-trichotomous α 𝟙ₒ t 𝟙ₒ-is-trichotomous

𝟙ᵒ 𝟚ᵒ : Ordinalᵀ 𝓤
𝟙ᵒ = 𝟙ₒ , prop.topped 𝟙 𝟙-is-prop ⋆
𝟚ᵒ = succₒ 𝟙ₒ

ℕ∞ᵒ : Ordᵀ
ℕ∞ᵒ = (ℕ∞ₒ , ∞ , ∞-top)

\end{code}

Sum of an ordinal-indexed family of ordinals:

\begin{code}

∑ : (τ : Ordinalᵀ 𝓤) → (⟨ τ ⟩ → Ordinalᵀ 𝓤) → Ordinalᵀ 𝓤
∑ {𝓤} ((X , _<_ , o) , t) υ = ((Σ x ꞉ X , ⟨ υ x ⟩) ,
                               Sum.order ,
                               Sum.well-order o (λ x → tis-well-ordered (υ x))) ,
                              Sum.top-preservation t
 where
  _≺_ : {x : X} → ⟨ υ x ⟩ → ⟨ υ x ⟩ → 𝓤 ̇
  y ≺ z = y ≺⟨ υ _ ⟩ z

  module Sum = sum-top fe _<_ _≺_ (λ x → top (υ x)) (λ x → top-is-top (υ x))

∑-is-trichotomous : (τ : Ordinalᵀ 𝓤) (υ : ⟨ τ ⟩ → Ordinalᵀ 𝓤)
                  → is-trichotomous [ τ ]
                  → ((x : ⟨ τ ⟩) → is-trichotomous [ υ x ])
                  → is-trichotomous [ ∑ τ υ ]
∑-is-trichotomous τ υ = sum.trichotomy-preservation _ _

\end{code}

Added by Martin Escardo 2nd September 2026.

The top of the index is needed only for the sum to have a top, and the
sum over an index without one is still an ordinal.

\begin{code}

∑ₒ : (α : Ordinal 𝓤) → (⟨ α ⟩ → Ordinalᵀ 𝓤) → Ordinal 𝓤
∑ₒ {𝓤} (X , _<_ , o) υ = (Σ x ꞉ X , ⟨ υ x ⟩) ,
                         Sum.order ,
                         Sum.well-order o (λ x → tis-well-ordered (υ x))
 where
  _≺_ : {x : X} → ⟨ υ x ⟩ → ⟨ υ x ⟩ → 𝓤 ̇
  y ≺ z = y ≺⟨ υ _ ⟩ z

  module Sum = sum-top fe _<_ _≺_ (λ x → top (υ x)) (λ x → top-is-top (υ x))

∑-is-∑ₒ : (τ : Ordinalᵀ 𝓤) (υ : ⟨ τ ⟩ → Ordinalᵀ 𝓤)
        → [ ∑ τ υ ] ＝ ∑ₒ [ τ ] υ
∑-is-∑ₒ τ υ = refl

\end{code}

End of addition.

Some restriction is needed to get extensionality of the lexicographic
order on sums. Two such restrictions are trichotomy and having
top. Without a restriction, the lexicographic order on the sum of an
ordinal-indexed family of ordinals need not be extensional, and asking
that it always be gives excluded middle, by Shulman's example in
Ordinals.ShulmanTaboo.

\begin{code}

Extensionality-of-Ordinal-Indexed-Sums : (𝓤 : Universe) → 𝓤 ⁺ ̇
Extensionality-of-Ordinal-Indexed-Sums 𝓤 =
   (τ : Ordinal 𝓤) (υ : ⟨ τ ⟩ → Ordinal 𝓤)
 → is-extensional (sum.order
                    (underlying-order τ)
                    (λ {x} → underlying-order (υ x)))

module _ (pe : propext 𝓤₀) where

 open import Ordinals.OrdinalOfTruthValues fe 𝓤₀ pe
 open import Ordinals.ShulmanTaboo fe pe

 extensionality-of-ordinal-indexed-sums-gives-EM
  : Extensionality-of-Ordinal-Indexed-Sums 𝓤₁ → EM 𝓤₀
 extensionality-of-ordinal-indexed-sums-gives-EM h = shulmans-taboo e
  where
   υ : ⟨ Ωₒ ⟩ → Ordinal 𝓤₁
   υ p = prop-ordinal (¬ (p ＝ ⊥)) (negations-are-props (fe 𝓤₁ 𝓤₀))

   _⊏_ : X → X → 𝓤₁ ̇
   _⊏_ = sum.order (underlying-order Ωₒ) (λ {p} → underlying-order (υ p))

   lex-gives-≺ : (z w : X) → z ⊏ w → z ≺ w
   lex-gives-≺ z w (inl l)       = l
   lex-gives-≺ z w (inr (r , l)) = 𝟘-elim l

   e : is-extensional _≺_
   e x y f g = h Ωₒ υ x y
                (λ z l → inl (f z (lex-gives-≺ z x l)))
                (λ z l → inl (g z (lex-gives-≺ z y l)))

\end{code}

Addition and multiplication can be reduced to ∑, given the ordinal 𝟚ᵒ
defined above:

\begin{code}

_+ᵒ_ : Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤
τ +ᵒ υ = ∑ 𝟚ᵒ (cases (λ _ → τ) (λ _ → υ))

+ᵒ-is-trichotomous : (τ υ : Ordinalᵀ 𝓤)
                   → is-trichotomous [ τ ]
                   → is-trichotomous [ υ ]
                   → is-trichotomous [ τ +ᵒ υ ]
+ᵒ-is-trichotomous τ υ t u = ∑-is-trichotomous 𝟚ᵒ (cases (λ _ → τ) (λ _ → υ))
                              𝟚ₒ-is-trichotomous
                              (dep-cases (λ _ → t) (λ _ → u))

_×ᵒ_ : Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤 → Ordinalᵀ 𝓤
τ ×ᵒ υ = ∑ τ  (λ (_ : ⟨ τ ⟩) → υ)

×ᵒ-is-trichotomous : (τ υ : Ordinalᵀ 𝓤)
                   → is-trichotomous [ τ ]
                   → is-trichotomous [ υ ]
                   → is-trichotomous [ τ ×ᵒ υ ]
×ᵒ-is-trichotomous τ υ t u = ∑-is-trichotomous τ (λ _ → υ) t (λ _ → u)

\end{code}

Extension of a family X → Ordᵀ along an embedding j : X → A to get a
family A → Ordᵀ. (This can also be done for Ord-valued families.)
This uses the module InjectiveTypes.Blackboard to calculate Y / j.

Sum of a countable family with an added non-isolated top element. We
first extend the family to ℕ∞ and then take the ordinal-indexed sum of
ordinals defined above.

\begin{code}

open topped-ordinals-injectivity fe

∑¹ : (ℕ → Ordᵀ) → Ordᵀ
∑¹ τ = ∑ ℕ∞ᵒ (τ ↗ embedding-ℕ-to-ℕ∞ fe₀)

\end{code}

And now with an isolated top element:

\begin{code}

∑₁ : (ℕ → Ordᵀ) → Ordᵀ
∑₁ τ = ∑ (succₒ ω) (τ ↗ (over , over-embedding))

\end{code}

The sum with an isolated top element preserves trichotomy, because the
fibers of the map over are decidable. There is no such statement for
the sum with a non-isolated top element, because the fibers of the map
ℕ → ℕ∞ used there are decidable only under LPO.

\begin{code}

∑₁-is-trichotomous : (τ : ℕ → Ordᵀ)
                   → ((n : ℕ) → is-trichotomous [ τ n ])
                   → is-trichotomous [ ∑₁ τ ]
∑₁-is-trichotomous τ t = ∑-is-trichotomous
                          (succₒ ω)
                          (τ ↗ (over , over-embedding))
                          (succₒ-is-trichotomous ω ω-is-trichotomous)
                          (↗-is-trichotomous τ
                            (over , over-embedding)
                            over-fibers-are-decidable
                            t)

\end{code}

Added 4th May 2022.

\begin{code}

module Omega {𝓤} (pe : propext 𝓤) where

 open import Ordinals.OrdinalOfTruthValues fe 𝓤 pe
 open import Ordinals.Notions
 open import UF.SubtypeClassifier

 Ωᵒ : Ordinalᵀ (𝓤 ⁺)
 Ωᵒ = Ωₒ , ⊤ , h
  where
   h : is-top (underlying-order Ωₒ) ⊤
   h y (p , _) = ⊥-is-not-⊤ (p ⁻¹)

\end{code}
