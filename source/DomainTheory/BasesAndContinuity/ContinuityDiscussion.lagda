Tom de Jong, early January 2022.

Inspired by the paper "Continuous categories and exponentiable toposes" by Peter
Johnstone and André Joyal, we discuss the notions

(1) structural continuity of a dcpo;
(2) continuity of a dcpo;
(3) pseudocontinuity of a dcpo.

(1) and (2) are defined in Continuity.lagda and (3) is defined and examined here.
The notions (1)-(3) have the following shapes:

(1)   Π (x : D) →   Σ I : 𝓥 ̇ , Σ α : I → D , α is-directed × ... × ...
(2) ∥ Π (x : D) →   Σ I : 𝓥 ̇ , Σ α : I → D , α is-directed × ... × ... ∥
(3)   Π (x : D) → ∥ Σ I : 𝓥 ̇ , Σ α : I → D , α is-directed × ... × ... ∥

So (2) and (3) are propositions, but (1) isn't. We illustrate (1)-(3) by
discussion them in terms of left adjoints. In these discussions, the
Ind-completion, as defined in IndCompletion.lagda plays an important role.

We show that (1) for a dcpo D is equivalent to asserting that the map
∐ : Ind(D) → D (which takes a directed family to its supremum) has a specified
left adjoint.

It follows directly that (2) is equivalent to asking that ∐-map has an
*unspecified* left adjoint.

Because Ind is a preorder and not a poset, the type expressing that ∐-map has a
specified left adjoint is not a proposition, as the supposed left adjoint can
map elements of D to bicofinal (but nonequal) directed families.

We could take the poset reflection Ind(D)/≈ of Ind(D) and ask that the map
∐-map/ : Ind(D)/≈ → D induced by ∐ : Ind(D) → D has a left adjoint to obtain a
type that is a proposition. We show that this amounts precisely to
pseudocontinuity.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.ContinuityDiscussion
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Hedberg
open import UF.ImageAndSurjection pt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥
open import DomainTheory.BasesAndContinuity.IndCompletion pt fe 𝓥

\end{code}

Because we'll want to apply some standard equivalences later on, we first show
that our record-based definition of structural continuity is equivalent to one
using Σ-types.

\begin{code}

structurally-continuous-Σ : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
structurally-continuous-Σ 𝓓 =
   (x : ⟨ 𝓓 ⟩)
 → Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , (is-way-upperbound 𝓓 x α)
                                 × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ＝ x)


structurally-continuous-to-Σ : (𝓓 : DCPO {𝓤} {𝓣})
                              → structurally-continuous 𝓓
                              → structurally-continuous-Σ 𝓓
structurally-continuous-to-Σ 𝓓 C x =
   index-of-approximating-family x
 , approximating-family x
 , approximating-family-is-way-below x
 , approximating-family-is-directed x
 , approximating-family-∐-＝ x
 where
  open structurally-continuous C

structurally-continuous-from-Σ : (𝓓 : DCPO {𝓤} {𝓣})
                                → structurally-continuous-Σ 𝓓
                                → structurally-continuous 𝓓
structurally-continuous-from-Σ 𝓓 C' =
 record
  { index-of-approximating-family     = λ x → pr₁ (C' x)
  ; approximating-family              = λ x → pr₁ (pr₂ (C' x))
  ; approximating-family-is-directed  = λ x → pr₁ (pr₂ (pr₂ (pr₂ (C' x))))
  ; approximating-family-is-way-below = λ x → pr₁ (pr₂ (pr₂ (C' x)))
  ; approximating-family-∐-＝          = λ x → pr₂ (pr₂ (pr₂ (pr₂ (C' x))))
 }

structurally-continuous-≃ : (𝓓 : DCPO {𝓤} {𝓣})
                          → structurally-continuous 𝓓
                          ≃ structurally-continuous-Σ 𝓓
structurally-continuous-≃ 𝓓 = qinveq (structurally-continuous-to-Σ 𝓓)
                                    ((structurally-continuous-from-Σ 𝓓) ,
                                     ((λ x → refl) , (λ x → refl)))

\end{code}

In "Continuous categories and exponentiable toposes", Peter Johnstone and André
Joyal show in Lemma 2.1 that a dcpo D is continuous if and only if the map
∐ : Ind(D) → D that takes a directed family in the Ind-completion of D to its
supremum has a (specified) left adjoint.

We show that the type expressing that the ∐-map has a left adjoint is equivalent
to the type expressing structural continuity of D.

The proof below is fairly short, but only because we already characterized when
∐-map has a left adjoint in IndCompletion.lagda.

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 structurally-continuous-if-specified-left-adjoint :
    ∐-map-has-specified-left-adjoint
  → structurally-continuous 𝓓
 structurally-continuous-if-specified-left-adjoint (L , L-left-adjoint) =
  record
   { index-of-approximating-family     = λ x → pr₁ (L x)
   ; approximating-family              = λ x → pr₁ (pr₂ (L x))
   ; approximating-family-is-directed  = λ x → pr₂ (pr₂ (L x))
   ; approximating-family-is-way-below = λ x → pr₂ (L-is-approximating x)
   ; approximating-family-∐-＝          = λ x → pr₁ (L-is-approximating x)
  }
   where
    L-is-approximating : is-approximating L
    L-is-approximating = ⌜ left-adjoint-to-∐-map-characterization L ⌝⁻¹ L-left-adjoint

 specified-left-adjoint-if-structurally-continuous :
    structurally-continuous 𝓓
  → ∐-map-has-specified-left-adjoint
 specified-left-adjoint-if-structurally-continuous C = L , L-is-left-adjoint
  where
   open structurally-continuous C
   L : ⟨ 𝓓 ⟩ → Ind
   L x = index-of-approximating-family x
       , approximating-family x
       , approximating-family-is-directed x
   L-is-left-adjoint : left-adjoint-to-∐-map L
   L-is-left-adjoint x σ@(I , α , δ) = ⦅1⦆ , ⦅2⦆
    where
     ⦅1⦆ : L x ≲ (I , α , δ) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
     ⦅1⦆ Lx-cofinal-in-α = transport (λ - → - ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
                           (approximating-family-∐-＝ x)
                           (≲-to-⊑-of-∐ (approximating-family-is-directed x)
                                        δ Lx-cofinal-in-α)
     ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ → L x ≲ (I , α , δ)
     ⦅2⦆ x-below-∐α j = approximating-family-is-way-below x j I α δ x-below-∐α

 specified-left-adjoint-structurally-continuous-≃ :
  ∐-map-has-specified-left-adjoint ≃ structurally-continuous 𝓓
 specified-left-adjoint-structurally-continuous-≃ = qinveq f (g , σ , τ)
  where
   f = structurally-continuous-if-specified-left-adjoint
   g = specified-left-adjoint-if-structurally-continuous
   σ : g ∘ f ∼ id
   σ (L , L-left-adjoint) =
    to-subtype-＝ being-left-adjoint-to-∐-map-is-prop refl
   τ : f ∘ g ∼ id
   τ C = f (g C)         ＝⟨refl⟩
         ϕ (ψ (f (g C))) ＝⟨ h    ⟩
         ϕ (ψ C)         ＝⟨refl⟩
         C               ∎
    where
     ϕ : structurally-continuous-Σ 𝓓 → structurally-continuous 𝓓
     ϕ = structurally-continuous-from-Σ 𝓓
     ψ : structurally-continuous 𝓓 → structurally-continuous-Σ 𝓓
     ψ = structurally-continuous-to-Σ 𝓓
     h = ap ϕ (dfunext fe
          (λ x → to-Σ-＝ (refl , (to-Σ-＝ (refl ,
                  (to-×-＝ refl  (to-Σ-＝ (refl , (sethood 𝓓 _ _)))))))))

\end{code}

It follows immediately that a dcpo is continuous if and only if ∐-map has an
unspecified left adjoint.

\begin{code}


module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 ∐-map-has-unspecified-left-adjoint : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ∐-map-has-unspecified-left-adjoint = ∥ ∐-map-has-specified-left-adjoint ∥

 is-continuous-dcpo-iff-∐-map-has-unspecified-left-adjoint :
   ∐-map-has-unspecified-left-adjoint ≃ is-continuous-dcpo 𝓓
 is-continuous-dcpo-iff-∐-map-has-unspecified-left-adjoint =
  ∥∥-cong pt (specified-left-adjoint-structurally-continuous-≃ 𝓓)

\end{code}

Finally, we consider pseudocontinuity. It is similar to structural continuity,
but instead of asking that for every x : D, we have a specified directed family
approximating x, we merely ask there exists an unspecified directed family
approximating x.

On first sight, pseudocontinuity is arguably how one would expect us to define
contuinity of a dcpo while ensuring the notion is property as opposed to
structure. It is however weaker than continuity (as defined in
Continuity.lagda) and structural continuity. More importantly, with
pseudocontinuity we would need some instances of the axiom of choice when
proving the interpolation properties for the way-below relation, at least when
trying to mimic the proof in Continuity.lagda.

\begin{code}

is-pseudocontinuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-pseudocontinuous-dcpo 𝓓 =
   (x : ⟨ 𝓓 ⟩)
 → ∥ Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , (is-way-upperbound 𝓓 x α)
                                   × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ＝ x) ∥

being-pseudocontinuous-dcpo-is-prop : (𝓓 : DCPO {𝓤} {𝓣})
                                    → is-prop (is-pseudocontinuous-dcpo 𝓓)
being-pseudocontinuous-dcpo-is-prop 𝓓 = Π-is-prop fe (λ x → ∥∥-is-prop)

continuous-dcpo-hierarchy₁ : (𝓓 : DCPO {𝓤} {𝓣})
                           → structurally-continuous 𝓓
                           → is-continuous-dcpo 𝓓
continuous-dcpo-hierarchy₁ 𝓓 = ∣_∣

continuous-dcpo-hierarchy₂ : (𝓓 : DCPO {𝓤} {𝓣})
                           → is-continuous-dcpo 𝓓
                           → is-pseudocontinuous-dcpo 𝓓
continuous-dcpo-hierarchy₂ 𝓓 c x =
 ∥∥-functor (λ C → structurally-continuous-to-Σ 𝓓 C x) c

\end{code}

Of course, one way to obtain a propositional-valued definition of continuity is
to ensure that we're asking for left adjoints between posets. That is, we take
the poset reflection Ind/≈ of Ind and ask that ∐-map/ : Ind/≈ → D has a left
adjoint.

We show that this is exactly the same as pseudocontinuity. This also illustrates
the discussion above on the need for the axiom of choice, as it boils down to
choosing representatives of equivalence classes.

\begin{code}

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open import Quotient.Type
 open import Quotient.Large pt fe pe
 open general-set-quotients-exist large-set-quotients

 open Ind-completion 𝓓
 open Ind-completion-poset-reflection pe 𝓓

 ⊑-∐-map/-lemma : {x : ⟨ 𝓓 ⟩} {σ : Ind}
               → (x ⊑⟨ 𝓓 ⟩ ∐-map σ) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ (η σ))
 ⊑-∐-map/-lemma {x} {σ} = transport (λ - → x ⊑⟨ 𝓓 ⟩ -) ((∐-map/-triangle σ) ⁻¹)
                       , transport (λ - → x ⊑⟨ 𝓓 ⟩ -) (∐-map/-triangle σ)

 specified-left-adjoint-if-pseudocontinuous : is-pseudocontinuous-dcpo 𝓓
                                            → ∐-map/-has-specified-left-adjoint
 specified-left-adjoint-if-pseudocontinuous pc = L , L-is-ladj
  where
   module construction (x : ⟨ 𝓓 ⟩) where
    str-cont : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    str-cont = (Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → ⟨ 𝓓 ⟩)
                          , is-way-upperbound 𝓓 x α
                          × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ＝ x))
    κ : str-cont → Ind
    κ (I , α , _ , (δ , _)) = I , α , δ
    κ-gives-approximating-family : (σ : str-cont) → κ σ approximates x
    κ-gives-approximating-family (I , α , α-wb-x , (δ , ∐α-is-x)) =
     ∐α-is-x , α-wb-x

    ladj : (σ : str-cont) (τ : Ind) → (κ σ ≲ τ) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map τ)
    ladj σ τ = left-adjunct-to-if-approximates
                (κ σ) x (κ-gives-approximating-family σ) τ

    κ/ : str-cont → Ind/≈
    κ/ = η ∘ κ
    κ/-wconstant : wconstant κ/
    κ/-wconstant σ@(I , α , α-way-below-x , (δ , x-sup-of-α))
                 τ@(J , β , β-way-below-x , (ε , x-sup-of-β)) =
     ≤-is-antisymmetric (κ/ σ) (κ/ τ)
      (η-preserves-order (λ i → α-way-below-x i J β ε (＝-to-⊒ 𝓓 x-sup-of-β)))
      (η-preserves-order (λ j → β-way-below-x j I α δ (＝-to-⊒ 𝓓 x-sup-of-α)))

    ω : Σ ϕ ꞉ (∥ str-cont ∥ → Ind/≈) , κ/ ∼ ϕ ∘ ∣_∣
    ω = wconstant-map-to-set-factors-through-truncation-of-domain
         Ind/≈-is-set κ/ κ/-wconstant

   L : ⟨ 𝓓 ⟩ → Ind/≈
   L x = pr₁ ω (pc x)
    where
     open construction x

   L-is-ladj : left-adjoint-to-∐-map/ L
   L-is-ladj x = ∥∥-rec (Π-is-prop fe adj-condition-is-prop) lemma (pc x)
    where
     open construction x
     adj-condition-is-prop : (τ' : Ind/≈)
                           → is-prop ((L x ≤ τ') ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ τ'))
     adj-condition-is-prop τ' =
      (×-is-prop (Π-is-prop fe (λ _ → prop-valuedness 𝓓 x (∐-map/ τ')))
                 (Π-is-prop fe (λ _ → ≤-is-prop-valued (L x) τ')))
     lemma : (σ : str-cont) (τ' : Ind/≈) → ((L x ≤ τ') ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ τ'))
     lemma σ = /-induction ≋ adj-condition-is-prop L-is-ladj'
      where
       L-is-ladj' : (τ : Ind)
                  → (L x ≤ η τ) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ (η τ))
       L-is-ladj' τ = ↔-trans ⦅1⦆ ⦅2⦆
        where
         ⦅2⦆ : (κ σ ≲ τ) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ (η τ))
         ⦅2⦆ = ↔-trans (ladj σ τ) (⊑-∐-map/-lemma)
         ⦅1⦆ : (L x ≤ η τ) ↔ (κ σ ≲ τ)
         ⦅1⦆ = ↔-trans s (↔-sym η-↔-order)
          where
           s : (L x ≤ η τ) ↔ (η (κ σ) ≤ η τ)
           s = transport (_≤ η τ) e , transport (_≤ η τ) (e ⁻¹)
            where
             e : L x ＝ η (κ σ)
             e = L x          ＝⟨ refl                                 ⟩
                 pr₁ ω (pc x) ＝⟨ ap (pr₁ ω) (∥∥-is-prop (pc x) ∣ σ ∣) ⟩
                 pr₁ ω ∣ σ ∣  ＝⟨ (pr₂ ω σ) ⁻¹                         ⟩
                 η (κ σ)      ∎

 pseudocontinuous-if-specified-left-adjoint : ∐-map/-has-specified-left-adjoint
                                            → is-pseudocontinuous-dcpo 𝓓
 pseudocontinuous-if-specified-left-adjoint (L , L-is-left-adjoint) x =
  ∥∥-functor lemma (η-is-surjection (L x))
   where
    lemma : (Σ σ ꞉ Ind , η σ ＝ L x)
          → Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , is-way-upperbound 𝓓 x α
                                          × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ＝ x)
    lemma (σ@(I , α , δ) , e) = I , α , pr₂ approx , (δ , pr₁ approx)
     where
      ladj : (τ : Ind) → (σ ≲ τ) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map τ)
      ladj τ = ↔-trans (↔-trans η-↔-order ladj') (↔-sym ⊑-∐-map/-lemma)
       where
        ladj' : (η σ ≤ η τ) ↔ x ⊑⟨ 𝓓 ⟩ ∐-map/ (η τ)
        ladj' = transport (λ - → (- ≤ η τ) ↔ x ⊑⟨ 𝓓 ⟩ ∐-map/ (η τ)) (e ⁻¹)
                 (L-is-left-adjoint x (η τ))
      approx : (∐ 𝓓 δ ＝ x) × is-way-upperbound 𝓓 x α
      approx = approximates-if-left-adjunct-to σ x ladj

 specified-left-adjoint-pseudo-continuous-≃ : ∐-map/-has-specified-left-adjoint
                                            ≃ is-pseudocontinuous-dcpo 𝓓
 specified-left-adjoint-pseudo-continuous-≃ =
  logically-equivalent-props-are-equivalent
    ∐-map/-having-left-adjoint-is-prop
    (being-pseudocontinuous-dcpo-is-prop 𝓓)
    pseudocontinuous-if-specified-left-adjoint
    specified-left-adjoint-if-pseudocontinuous

\end{code}
