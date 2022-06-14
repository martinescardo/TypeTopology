Tom de Jong, early January 2022.

Inspired by the paper "Continuous categories and exponentiable toposes" by Peter
Johnstone and André Joyal, we discuss the notions

(1) structural continuity of a dcpo;
(2) continuity of a dcpo;
(3) pseudocontinuity of a dcpo.

(1) and (2) are defined in DcpoContinuous.lagda and (3) is defined and examined here.
The notions (1)-(3) have the following shapes:

(1)   Π (x : D) →   Σ I : 𝓥 ̇  , Σ α : I → D , α is-directed × ... × ...
(2) ∥ Π (x : D) →   Σ I : 𝓥 ̇  , Σ α : I → D , α is-directed × ... × ... ∥
(3)   Π (x : D) → ∥ Σ I : 𝓥 ̇  , Σ α : I → D , α is-directed × ... × ... ∥

So (2) and (3) are propositions, but (1) isn't. We illustrate (1)-(3) by
discussion them in terms of left adjoints. In these discussions, the
Ind-completion, as defined in DcpoIndCompletion.lagda plays an important role.

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

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

module DomainTheory.BasesAndContinuity.ContinuityDiscussion
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-ImageAndSurjection
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open ImageAndSurjection pt
open PropositionalTruncation pt

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
 → Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , (is-way-upperbound 𝓓 x α)
                                 × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x)


structurally-continuous-to-Σ : (𝓓 : DCPO {𝓤} {𝓣})
                              → structurally-continuous 𝓓
                              → structurally-continuous-Σ 𝓓
structurally-continuous-to-Σ 𝓓 C x =
   index-of-approximating-family x
 , approximating-family x
 , approximating-family-is-way-below x
 , approximating-family-is-directed x
 , approximating-family-∐-≡ x
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
  ; approximating-family-∐-≡          = λ x → pr₂ (pr₂ (pr₂ (pr₂ (C' x))))
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
∐-map has a left adjoint in DcpoIndCompletion.lagda.

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
   ; approximating-family-is-way-below = λ x → pr₂ (crit x)
   ; approximating-family-∐-≡          = λ x → pr₁ (crit x)
   }
   where
    crit : left-adjoint-to-∐-map-criterion L
    crit = ⌜ left-adjoint-to-∐-map-characterization L ⌝⁻¹ L-left-adjoint

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
                           (approximating-family-∐-≡ x)
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
    to-subtype-≡ being-left-adjoint-to-∐-map-is-prop refl
   τ : f ∘ g ∼ id
   τ C = f (g C)         ≡⟨ refl ⟩
         ϕ (ψ (f (g C))) ≡⟨ h    ⟩
         ϕ (ψ C)         ≡⟨ refl ⟩
         C               ∎
    where
     ϕ : structurally-continuous-Σ 𝓓 → structurally-continuous 𝓓
     ϕ = structurally-continuous-from-Σ 𝓓
     ψ : structurally-continuous 𝓓 → structurally-continuous-Σ 𝓓
     ψ = structurally-continuous-to-Σ 𝓓
     h = ap ϕ (dfunext fe
          (λ x → to-Σ-≡ (refl , (to-Σ-≡ (refl ,
                  (to-×-≡ refl  (to-Σ-≡ (refl , (sethood 𝓓 _ _)))))))))

\end{code}

One may observe that ∐-map-has-specified-left-adjoint does not require the
specified left adjoint to be functorial/monotone, as would normally be required
for an adjoint/Galois connection. But this actually follows from the "hom-set"
condition, as we show now.

The proof works because the approximating families are given by the left
adjoint, by definition of structurally-continuous-if-specified-left-adjoint.

\begin{code}

 left-adjoint-to-∐-map-is-monotone : (L : ⟨ 𝓓 ⟩ → Ind)
                                   → left-adjoint-to-∐-map L
                                   → (x y : ⟨ 𝓓 ⟩)
                                   → x ⊑⟨ 𝓓 ⟩ y
                                   → L x ≲ L y
 left-adjoint-to-∐-map-is-monotone L L-left-adjoint x y x-below-y = γ
  where
   C = structurally-continuous-if-specified-left-adjoint (L , L-left-adjoint)
   open structurally-continuous C
   I : 𝓥 ̇
   I = index-of-approximating-family x
   J : 𝓥 ̇
   J = index-of-approximating-family y
   xi-way-below-y : (i : I) → approximating-family x i ≪⟨ 𝓓 ⟩ y
   xi-way-below-y i = ≪-⊑-to-≪ 𝓓 (approximating-family-is-way-below x i)
                                 x-below-y
   γ : (i : I) → ∃ j ꞉ J , approximating-family x i ⊑⟨ 𝓓 ⟩
                           approximating-family y j
   γ i = xi-way-below-y i (index-of-approximating-family y)
                          (approximating-family y)
                          (approximating-family-is-directed y)
                          (approximating-family-∐-⊒ y)

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

Finall, we consider pseudocontinuity. It is similar to structural continuity,
but instead of asking that for every x : D, we have a specified directed family
approximating x, we merely ask there exists an unspecified directed family
approximating x.

On first sight, pseudocontinuity is arguably how one would expect us to define
contuinity of a dcpo while ensuring the notion is property as opposed to
structure. It is however weaker than continuity (as defined in
DcpoContinuous.lagda) and structural continuity. More importantly, with
pseudocontinuity we would need some instances of the axiom of choice when
proving the interpolation properties for the way-below relation, at least when
trying to mimick the proof in DcpoContinuous.lagda.

\begin{code}

is-pseudocontinuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-pseudocontinuous-dcpo 𝓓 =
   (x : ⟨ 𝓓 ⟩)
 → ∥ Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , (is-way-upperbound 𝓓 x α)
                                   × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x) ∥

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

 open Ind-completion 𝓓
 open Ind-completion-poset-reflection pe 𝓓

 specified-left-adjoint-if-pseudocontinuous : is-pseudocontinuous-dcpo 𝓓
                                            → ∐-map/-has-specified-left-adjoint
 specified-left-adjoint-if-pseudocontinuous pc = L , ladj
  where
   module construction (x : ⟨ 𝓓 ⟩) where
    dom : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    dom = (Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , is-way-upperbound 𝓓 x α
                                         × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x))
    κ : dom → Ind/≈
    κ = η ∘ (λ (I , α , _ , (δ , _)) → I , α , δ)
    κ-wconstant : wconstant κ
    κ-wconstant σ@(I , α , α-way-below-x , (δ , x-sup-of-α))
                τ@(J , β , β-way-below-x , (ε , x-sup-of-β)) =
     ≤-is-antisymmetric (κ σ) (κ τ)
      (η-preserves-order (I , α , δ) (J , β , ε)
        (λ i → α-way-below-x i J β ε (≡-to-⊒ 𝓓 x-sup-of-β)))
      (η-preserves-order (J , β , ε) (I , α , δ)
        (λ j → β-way-below-x j I α δ (≡-to-⊒ 𝓓 x-sup-of-α)))

    ω : Σ ϕ ꞉ (∥ dom ∥ → Ind/≈) , κ ∼ ϕ ∘ ∣_∣
    ω = wconstant-map-to-set-factors-through-truncation-of-domain
         Ind/≈-is-set κ κ-wconstant
   L : ⟨ 𝓓 ⟩ → Ind/≈
   L x = pr₁ ω (pc x)
    where
     open construction x

   ladj : left-adjoint-to-∐-map/ L
   ladj x α' = ∥∥-rec adj-condition-is-prop r (η-is-surjection α')
    where
     open construction x
     adj-condition-is-prop : is-prop ((L x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ α'))
     adj-condition-is-prop =
      (×-is-prop (Π-is-prop fe (λ _ → prop-valuedness 𝓓 x (∐-map/ α')))
                 (Π-is-prop fe (λ _ → ≤-is-prop-valued (L x) α')))
     r : (Σ α ꞉ Ind , η α ≡ α')
       → (L x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ α')
     r (α , refl) = ∥∥-rec adj-condition-is-prop ρ (pc x)
      where
       ρ : dom → (L x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ α')
       ρ τ@(J , β , β-way-below-x , ε , x-sup-of-β) = ⇔-trans claim₁ claim₂
        where
         claim₁ : (L x ≤ η α) ⇔ (η (J , β , ε) ≤ η α)
         claim₁ = lemma₁ eq₁
          where
           eq₁ = L x          ≡⟨ refl                                 ⟩
                 pr₁ ω (pc x)  ≡⟨ ap (pr₁ ω) (∥∥-is-prop (pc x) ∣ τ ∣) ⟩
                 pr₁ ω ∣ τ ∣   ≡⟨ (pr₂ ω τ) ⁻¹                         ⟩
                 η (J , β , ε) ∎
           lemma₁ : {σ τ : Ind/≈} → σ ≡ τ → σ ≤ η α ⇔ τ ≤ η α
           lemma₁ refl = ⇔-refl
         claim₂ : (η (J , β , ε) ≤ η α) ⇔ x ⊑⟨ 𝓓 ⟩ ∐-map/ (η α)
         claim₂ = ⇔-trans ((η-reflects-order  (J , β , ε) α) ,
                           (η-preserves-order (J , β , ε) α))
                          (⇔-trans claim₂' (lemma₂ (eq₂ ⁻¹)))
          where
           eq₂ : ∐-map/ (η α) ≡ ∐-map α
           eq₂ = ∐-map/-triangle α
           lemma₂ : {d e : ⟨ 𝓓 ⟩} → d ≡ e
                  → x ⊑⟨ 𝓓 ⟩ d ⇔ x ⊑⟨ 𝓓 ⟩ e
           lemma₂ refl = ⇔-refl
           claim₂' : ((J , β , ε) ≲ α) ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map α)
           claim₂' = ⌜ left-adjoint-to-∐-map-characterization-local
                        x (J , β , ε) ⌝
                     (x-sup-of-β , β-way-below-x) α

 pseudocontinuous-if-specified-left-adjoint : ∐-map/-has-specified-left-adjoint
                                            → is-pseudocontinuous-dcpo 𝓓
 pseudocontinuous-if-specified-left-adjoint (L , L-is-left-adjoint) x =
  ∥∥-rec ∥∥-is-prop r (η-is-surjection (L x))
   where
    r : (Σ σ ꞉ Ind , η σ ≡ L x)
      → ∥ Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , is-way-upperbound 𝓓 x α
                                        × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x) ∥
    r (σ@(I , α , δ) , p) = ∣ I , α , pr₂ claim , (δ , pr₁ claim) ∣
     where
      claim : (∐ 𝓓 δ ≡ x) × is-way-upperbound 𝓓 x α
      claim = ⌜ left-adjoint-to-∐-map-characterization-local x σ ⌝⁻¹
               ladj-local
       where
        ladj-local : left-adjoint-to-∐-map-local x (I , α , δ)
        ladj-local τ = ⦅⇒⦆ , ⦅⇐⦆
         where
          comm-eq : ∐-map/ (η τ) ≡ ∐-map τ
          comm-eq = ∐-map/-triangle τ
          ⦅⇒⦆ : σ ≲ τ → x ⊑⟨ 𝓓 ⟩ ∐-map τ
          ⦅⇒⦆ σ-cofinal-in-τ = x           ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
                              ∐-map/ (η τ) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
                              ∐-map      τ ∎⟨ 𝓓 ⟩
           where
            ⦅2⦆ = ≡-to-⊑ 𝓓 comm-eq
            ⦅1⦆ = lr-implication (L-is-left-adjoint x (η τ))
                  (≤-is-transitive (L x) (η σ) (η τ)
                    (transport (λ - → - ≤ η σ) p (≤-is-reflexive (η σ)))
                    ησ-less-than-ητ)
             where
              ησ-less-than-ητ : η σ ≤ η τ
              ησ-less-than-ητ = η-preserves-order σ τ σ-cofinal-in-τ
          ⦅⇐⦆ : x ⊑⟨ 𝓓 ⟩ ∐-map τ → σ ≲ τ
          ⦅⇐⦆ x-below-∐τ = η-reflects-order σ τ lem
           where
            lem : η σ ≤ η τ
            lem = transport⁻¹ (λ - → - ≤ η τ) p lem'
             where
              lem' : L x ≤ η τ
              lem' = rl-implication (L-is-left-adjoint x (η τ))
                      (x            ⊑⟨ 𝓓 ⟩[ x-below-∐τ       ]
                       ∐-map τ      ⊑⟨ 𝓓 ⟩[ ≡-to-⊒ 𝓓 comm-eq ]
                       ∐-map/ (η τ) ∎⟨ 𝓓 ⟩)

 specified-left-adjoint-pseudo-continuous-≃ : ∐-map/-has-specified-left-adjoint
                                            ≃ is-pseudocontinuous-dcpo 𝓓
 specified-left-adjoint-pseudo-continuous-≃ =
  logically-equivalent-props-are-equivalent
    ∐-map/-having-left-adjoint-is-prop
    (being-pseudocontinuous-dcpo-is-prop 𝓓)
    pseudocontinuous-if-specified-left-adjoint
    specified-left-adjoint-if-pseudocontinuous

\end{code}
