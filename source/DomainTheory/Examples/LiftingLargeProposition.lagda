Tom de Jong, 3 June 2024.

We consider the lifting of a proposition P as a locally small algebraic dcpo
which does not have a small basis unless the proposition P can be resized.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Examples.LiftingLargeProposition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (𝓥 𝓤 : Universe)
        (P : 𝓤 ̇  )
        (P-is-prop : is-prop P)
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.Sets
open import UF.Size hiding (is-locally-small)
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

private
 P-is-set : is-set P
 P-is-set = props-are-sets (P-is-prop)

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥
open import DomainTheory.Basics.SupComplete pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥
open import DomainTheory.Lifting.LiftingSet pt fe 𝓥 pe
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓥 hiding (κ)

open import Lifting.Construction 𝓥
open import Lifting.Miscelanea 𝓥
open import Lifting.Miscelanea-PropExt-FunExt 𝓥 pe fe
open import Lifting.UnivalentPrecategory 𝓥 P hiding (_⊑_)

open import OrderedTypes.Poset
open PosetAxioms fe

\end{code}

The lifting of a set with respect to the propositions in a universe 𝓥 always
produces a 𝓥-directed complete poset.

Here we consider the 𝓥-lifting of a proposition P in universe 𝓤 and show that if it has a small basis


The ordinals in a given universe 𝓤 form a dcpo whose carrier lives in the
successor universe 𝓤 ⁺. The ordinal relation lives in 𝓤, and so the dcpo of
ordinals is large, but locally small. It has suprema for all families of
ordinals indexed by types in 𝓤.

\begin{code}

𝓛P : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⁺ ⊔ 𝓤}
𝓛P = 𝓛-DCPO⊥ {𝓤} {P} (props-are-sets P-is-prop)

private
 _⊑_ : ⟪ 𝓛P ⟫ → ⟪ 𝓛P ⟫ → 𝓥 ̇
 (Q , _) ⊑ (R , _) = Q → R

 ⊑-is-prop-valued : (Q R : ⟪ 𝓛P ⟫) → is-prop (Q ⊑ R)
 ⊑-is-prop-valued Q (R , _ , i) = Π-is-prop fe (λ _ → i)

 ⊑-to-𝓛-⊑ : (Q R : ⟪ 𝓛P ⟫) → (Q ⊑ R → Q ⊑⟪ 𝓛P ⟫ R)
 ⊑-to-𝓛-⊑ (Q , _ , i) (R , _ , j) l h =
  to-subtype-＝
   (λ _ → ×-is-prop (Π-is-prop fe (λ _ → P-is-prop))
   (being-prop-is-prop fe))
   (pe i j l (λ r → h))

 𝓛-⊑-to-⊑ : (Q R : ⟪ 𝓛P ⟫) → (Q ⊑⟪ 𝓛P ⟫ R → Q ⊑ R)
 𝓛-⊑-to-⊑ Q R l = def-pr Q R (⊑'-to-⊑ l)

𝓛P-is-locally-small : is-locally-small (𝓛P ⁻)
𝓛P-is-locally-small =
 record
  { _⊑ₛ_ = _⊑_ ;
    ⊑ₛ-≃-⊑ = λ {Q} {R} → logically-equivalent-props-are-equivalent
              (⊑-is-prop-valued Q R)
              (prop-valuedness (𝓛P ⁻) Q R)
              (⊑-to-𝓛-⊑ Q R)
              (𝓛-⊑-to-⊑ Q R)
  }

private
 module _
   (ℚ@(Q , Q-implies-P , Q-is-prop) : ⟪ 𝓛P ⟫)
  where

  family : Q → ⟪ 𝓛P ⟫
  family q = 𝟙 , (λ _ → Q-implies-P q) , 𝟙-is-prop

  family-members-are-compact : (q : Q) → is-compact (𝓛P ⁻) (family q)
  family-members-are-compact q I α δ l = ∥∥-functor ⦅2⦆ ⦅1⦆
   where
    ⦅1⦆ : ∃ i ꞉ I , is-defined (α i)
    ⦅1⦆ = ＝-to-is-defined (l ⋆) ⋆
    ⦅2⦆ : (Σ i ꞉ I , is-defined (α i))
        → Σ i ꞉ I , family q ⊑⟪ 𝓛P ⟫ α i
    ⦅2⦆ (i , d) = i , ＝-to-⊑ (𝓛P ⁻) (family q   ＝⟨ l ⋆ ⟩
                                      ∐ (𝓛P ⁻) δ ＝⟨ e ⁻¹ ⟩
                                      α i        ∎)
     where
      e = family-defined-somewhere-sup-＝ P-is-set δ i d

  upperbound-of-family : is-upperbound _⊑_ ℚ family
  upperbound-of-family q _ = q

  lowerbound-of-upperbounds-of-family : is-lowerbound-of-upperbounds _⊑_ ℚ family
  lowerbound-of-upperbounds-of-family R R-is-ub q = R-is-ub q ⋆

  family-is-sup : is-sup _⊑_ ℚ family
  family-is-sup = upperbound-of-family , lowerbound-of-upperbounds-of-family

  family-is-sup' : is-sup (underlying-order (𝓛P ⁻)) ℚ family
  family-is-sup' = (λ q → ⊑-to-𝓛-⊑ (family q) ℚ (upperbound-of-family q)) ,
                   (λ ℝ ℝ-is-ub → ⊑-to-𝓛-⊑ ℚ ℝ (lowerbound-of-upperbounds-of-family ℝ (λ q → 𝓛-⊑-to-⊑ (family q) ℝ (ℝ-is-ub q))))

  ∐ˢˢ-＝ : ∐ˢˢ 𝓛P family Q-is-prop ＝ ℚ
  ∐ˢˢ-＝ = sups-are-unique (underlying-order (𝓛P ⁻)) (pr₁ (axioms-of-dcpo (𝓛P ⁻))) family (∐ˢˢ-is-sup 𝓛P family Q-is-prop) family-is-sup'

𝓛P-is-algebraic' : structurally-algebraic (𝓛P ⁻)
𝓛P-is-algebraic' =
 record
  { index-of-compact-family = λ (Q , _) → 𝟙 + Q
  ; compact-family = λ Q → add-⊥ 𝓛P (family Q)
  ; compact-family-is-directed =
     λ ℚ@(Q , _ , Q-is-prop) → add-⊥-is-directed 𝓛P
                                (subsingleton-indexed-is-semidirected (𝓛P ⁻)
                                  (family ℚ) Q-is-prop)
  ; compact-family-is-compact = κ
  ; compact-family-∐-＝ = λ ℚ@(Q , _ , Q-is-prop) → (∐ˢᵈ-in-terms-of-∐ 𝓛P _) ⁻¹ ∙ ((∐ˢˢ-in-terms-of-∐ˢᵈ 𝓛P Q-is-prop) ⁻¹ ∙ ∐ˢˢ-＝ ℚ)
  }
   where
    κ : (ℚ@(Q , Q-implies-P , Q-is-prop) : ⟪ 𝓛P ⟫) (i : 𝟙 + Q)
      → is-compact (𝓛P ⁻) (add-⊥ 𝓛P (family ℚ) i)
    κ ℚ (inl _) = ⊥-is-compact 𝓛P
    κ ℚ (inr q) = family-members-are-compact ℚ q

\end{code}

\begin{code}

𝓛P-is-sup-complete : is-sup-complete (𝓛P ⁻)
𝓛P-is-sup-complete = lifting-of-prop-is-sup-complete P-is-prop

greatest-element-resizes : (⊤ : ⟪ 𝓛P ⟫)
                         → is-greatest _⊑_ ⊤
                         → P is 𝓥 small
greatest-element-resizes (Q , Q-implies-P , Q-is-prop) grt =
 Q ,
 logically-equivalent-props-are-equivalent
  Q-is-prop
  P-is-prop
  Q-implies-P
  (λ p → grt (𝟙 , (λ _ → p) , 𝟙-is-prop) ⋆)

𝓛P-has-unspecified-small-basis-resizes : has-unspecified-small-basis (𝓛P ⁻)
                                       → P is 𝓥 small
𝓛P-has-unspecified-small-basis-resizes scb =
 greatest-element-resizes ⊤ ⊤-is-greatest
  where
   grt : Σ ⊤ ꞉ ⟪ 𝓛P ⟫ , ((Q : ⟪ 𝓛P ⟫) → Q ⊑⟪ 𝓛P ⟫ ⊤)
   grt = greatest-element-if-sup-complete-with-small-basis
          (𝓛P ⁻) 𝓛P-is-sup-complete scb
   ⊤ : ⟪ 𝓛P ⟫
   ⊤ = pr₁ grt
   ⊤-is-greatest : (Q : ⟪ 𝓛P ⟫) → Q ⊑ ⊤
   ⊤-is-greatest Q = 𝓛-⊑-to-⊑ Q ⊤ (pr₂ grt Q)

𝓛P-has-unspecified-small-compact-basis-resizes :
   has-unspecified-small-compact-basis (𝓛P ⁻)
 → P is 𝓥 small
𝓛P-has-unspecified-small-compact-basis-resizes h =
 𝓛P-has-unspecified-small-basis-resizes
  (∥∥-functor (λ (B , β , scb) → B , β , compact-basis-is-basis _ β scb) h)

\end{code}

\begin{code}

resizing-gives-small-compact-basis : P is 𝓥 small
                                   → has-specified-small-compact-basis (𝓛P ⁻)
resizing-gives-small-compact-basis (P₀ , e) =
 small-compact-basis-from-≃ᵈᶜᵖᵒ pe
  (𝓛-DCPO P₀-is-set) (𝓛P ⁻)
  (𝓛̇-≃ᵈᶜᵖᵒ P₀-is-set P-is-set e)
  scb
  where
   P₀-is-set : is-set P₀
   P₀-is-set = props-are-sets (equiv-to-prop e P-is-prop)
   scb : has-specified-small-compact-basis (𝓛-DCPO P₀-is-set)
   scb = 𝓛-has-specified-small-compact-basis P₀-is-set

\end{code}