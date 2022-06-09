Tom de Jong, early January 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

module DcpoContinuousDiscussion
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥
open import DcpoContinuous pt fe 𝓥
open import DcpoIndCompletion pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

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

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 Johnstone-Joyal₁ : ∐-map-has-specified-left-adjoint
                  → structurally-continuous 𝓓
 Johnstone-Joyal₁ (L , L-left-adjoint) =
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

 Johnstone-Joyal₂ : structurally-continuous 𝓓
                  → ∐-map-has-specified-left-adjoint
 Johnstone-Joyal₂ C = L , L-is-left-adjoint
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

 Johnstone-Joyal-≃ : ∐-map-has-specified-left-adjoint
                   ≃ structurally-continuous 𝓓
 Johnstone-Joyal-≃ = qinveq f (g , σ , τ)
  where
   f = Johnstone-Joyal₁
   g = Johnstone-Joyal₂
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

 -- TODO: Comment further on this.
 -- In turns out that monotonicity of L need not be required, as it follows from
 -- the "hom-set" condition.

 left-adjoint-to-∐-map-is-monotone : (L : ⟨ 𝓓 ⟩ → Ind)
                                   → left-adjoint-to-∐-map L
                                   → (x y  : ⟨ 𝓓 ⟩)
                                   → x ⊑⟨ 𝓓 ⟩ y
                                   → L x ≲ L y
 left-adjoint-to-∐-map-is-monotone L L-left-adjoint x y x-below-y i = goal
  where
   C = Johnstone-Joyal₁ (L , L-left-adjoint)
   open structurally-continuous C
   goal = ≪-⊑-to-≪ 𝓓 (approximating-family-is-way-below x i) x-below-y
           (index-of-approximating-family y)
           (approximating-family y) (approximating-family-is-directed y)
           (approximating-family-∐-⊒ y)

\end{code}

Continuity and pseudocontinuity (for comparison)

\begin{code}

-- A truncated version of Johnstone-Joyal-≃

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 ∐-map-has-unspecified-left-adjoint : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ∐-map-has-unspecified-left-adjoint = ∥ ∐-map-has-specified-left-adjoint ∥

 is-continuous-dcpo-iff-∐-map-has-unspecified-left-adjoint :
   ∐-map-has-unspecified-left-adjoint ≃ is-continuous-dcpo 𝓓
 is-continuous-dcpo-iff-∐-map-has-unspecified-left-adjoint =
  ∥∥-cong pt (Johnstone-Joyal-≃ 𝓓)

\end{code}

\begin{code}

is-pseudocontinuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-pseudocontinuous-dcpo 𝓓 =
   (x : ⟨ 𝓓 ⟩)
 → ∥ Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , (is-way-upperbound 𝓓 x α)
                                   × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x) ∥

being-psuedocontinuous-dcpo-is-prop : (𝓓 : DCPO {𝓤} {𝓣})
                                   → is-prop (is-pseudocontinuous-dcpo 𝓓)
being-psuedocontinuous-dcpo-is-prop 𝓓 = Π-is-prop fe (λ x → ∥∥-is-prop)

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

Quotienting Ind and pseudocontinuity

TODO: Write some more

\begin{code}

open import UF-ImageAndSurjection

open ImageAndSurjection pt

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 open import PosetReflection pt fe pe
 open poset-reflection Ind _≲_ ≲-is-prop-valued ≲-is-reflexive ≲-is-transitive

 Ind' : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 Ind' = poset-reflection-carrier

 Ind'-is-set : is-set Ind'
 Ind'-is-set = poset-reflection-is-set

 ∐-map'-specification :
   Σ f̃ ꞉ (Ind' → ⟨ 𝓓 ⟩) , ((σ' τ' : Ind') → σ' ≤ τ'
                                          → f̃ σ' ⊑⟨ 𝓓 ⟩ f̃ τ')
                        × (f̃ ∘ η ∼ ∐-map)
 ∐-map'-specification =
  center (universal-property (underlying-order 𝓓) (sethood 𝓓) (prop-valuedness 𝓓)
                             (reflexivity 𝓓) (transitivity 𝓓) (antisymmetry 𝓓)
                             ∐-map ∐-map-is-monotone)

 ∐-map' : Ind' → ⟨ 𝓓 ⟩
 ∐-map' = pr₁ ∐-map'-specification

 left-adjoint-to-∐-map' : (⟨ 𝓓 ⟩ → Ind')
                        → 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 left-adjoint-to-∐-map' L' =
  (x : ⟨ 𝓓 ⟩) (α' : Ind') → (L' x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map' α')

 being-left-adjoint-to-∐-map'-is-prop : (L' : ⟨ 𝓓 ⟩ → Ind')
                                      → is-prop (left-adjoint-to-∐-map' L')
 being-left-adjoint-to-∐-map'-is-prop L' =
  Π₂-is-prop fe (λ x α' → ×-is-prop
                           (Π-is-prop fe (λ _ → prop-valuedness 𝓓 x (∐-map' α')))
                           (Π-is-prop fe (λ _ → ≤-is-prop-valued (L' x) α')))

 ∐-map'-has-specified-left-adjoint : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 ∐-map'-has-specified-left-adjoint = Σ left-adjoint-to-∐-map'

 ∐-map'-having-left-adjoint-is-prop : is-prop ∐-map'-has-specified-left-adjoint
 ∐-map'-having-left-adjoint-is-prop
  (L , L-is-left-adjoint) (L' , L'-is-left-adjoint) =
   to-subtype-≡ being-left-adjoint-to-∐-map'-is-prop
                (dfunext fe (λ x → ≤-is-antisymmetric (L x) (L' x)
                  (rl-implication (L-is-left-adjoint x (L' x))
                                  (lr-implication (L'-is-left-adjoint x (L' x))
                                    (≤-is-reflexive (L' x))))
                  (rl-implication (L'-is-left-adjoint x (L x))
                                  (lr-implication (L-is-left-adjoint x (L x))
                                    (≤-is-reflexive (L x))))))

 pseudo₁ : is-pseudocontinuous-dcpo 𝓓
         → ∐-map'-has-specified-left-adjoint
 pseudo₁ pc = L' , ladj
  where
   module construction (x : ⟨ 𝓓 ⟩) where
    dom : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    dom = (Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , is-way-upperbound 𝓓 x α
                                         × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x))
    κ : dom → Ind'
    κ = η ∘ (λ (I , α , _ , (δ , _)) → I , α , δ)
    κ-wconstant : wconstant κ
    κ-wconstant σ@(I , α , α-way-below-x , (δ , x-sup-of-α))
                τ@(J , β , β-way-below-x , (ε , x-sup-of-β)) =
     ≤-is-antisymmetric (κ σ) (κ τ)
      (η-preserves-order (I , α , δ) (J , β , ε)
        (λ i → α-way-below-x i J β ε (≡-to-⊒ 𝓓 x-sup-of-β)))
      (η-preserves-order (J , β , ε) (I , α , δ)
        (λ j → β-way-below-x j I α δ (≡-to-⊒ 𝓓 x-sup-of-α)))

    ω : Σ ϕ ꞉ (∥ dom ∥ → Ind') , κ ∼ ϕ ∘ ∣_∣
    ω = wconstant-map-to-set-factors-through-truncation-of-domain
         Ind'-is-set κ κ-wconstant
   L' : ⟨ 𝓓 ⟩ → Ind'
   L' x = pr₁ ω (pc x)
    where
     open construction x

   ladj : left-adjoint-to-∐-map' L'
   ladj x α' = ∥∥-rec goal-is-prop r (η-is-surjection α')
    where
     open construction x
     goal-is-prop : is-prop ((L' x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map' α'))
     goal-is-prop = (×-is-prop
                     (Π-is-prop fe (λ _ → prop-valuedness 𝓓 x (∐-map' α')))
                     (Π-is-prop fe (λ _ → ≤-is-prop-valued (L' x) α')))
     r : (Σ α ꞉ Ind , η α ≡ α')
       → (L' x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map' α')
     r (α , refl) = ∥∥-rec goal-is-prop ρ (pc x)
      where
       ρ : dom → (L' x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map' α')
       ρ τ@(J , β , β-way-below-x , ε , x-sup-of-β) = ⇔-trans claim₁ claim₂
        where
         claim₁ : (L' x ≤ η α) ⇔ (η (J , β , ε) ≤ η α)
         claim₁ = lemma₁ eq₁
          where
           eq₁ = L' x          ≡⟨ refl                                 ⟩
                 pr₁ ω (pc x)  ≡⟨ ap (pr₁ ω) (∥∥-is-prop (pc x) ∣ τ ∣) ⟩
                 pr₁ ω ∣ τ ∣   ≡⟨ (pr₂ ω τ) ⁻¹                         ⟩
                 η (J , β , ε) ∎
           lemma₁ : {σ τ : Ind'} → σ ≡ τ → σ ≤ η α ⇔ τ ≤ η α
           lemma₁ refl = ⇔-refl
         claim₂ : (η (J , β , ε) ≤ η α) ⇔ x ⊑⟨ 𝓓 ⟩ ∐-map' (η α)
         claim₂ = ⇔-trans ((η-reflects-order  (J , β , ε) α) ,
                           (η-preserves-order (J , β , ε) α))
                          (⇔-trans claim₂' (lemma₂ (eq₂ ⁻¹)))
          where
           eq₂ : ∐-map' (η α) ≡ ∐-map α
           eq₂ = pr₂ (pr₂ ∐-map'-specification) α
           lemma₂ : {d e : ⟨ 𝓓 ⟩} → d ≡ e
                  → x ⊑⟨ 𝓓 ⟩ d ⇔ x ⊑⟨ 𝓓 ⟩ e
           lemma₂ refl = ⇔-refl
           claim₂' : ((J , β , ε) ≲ α) ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map α)
           claim₂' = ⌜ left-adjoint-to-∐-map-characterization-local
                        x (J , β , ε) ⌝
                     (x-sup-of-β , β-way-below-x) α

 pseudo₂ : ∐-map'-has-specified-left-adjoint
         → is-pseudocontinuous-dcpo 𝓓
 pseudo₂ (L' , L'-is-left-adjoint) x =
  ∥∥-rec ∥∥-is-prop r (η-is-surjection (L' x))
   where
    r : (Σ σ ꞉ Ind , η σ ≡ L' x)
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
          comm-eq : ∐-map' (η τ) ≡ ∐-map τ
          comm-eq = pr₂ (pr₂ ∐-map'-specification) τ
          ⦅⇒⦆ : σ ≲ τ → x ⊑⟨ 𝓓 ⟩ ∐-map τ
          ⦅⇒⦆ σ-cofinal-in-τ = x           ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
                              ∐-map' (η τ) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
                              ∐-map      τ ∎⟨ 𝓓 ⟩
           where
            ⦅2⦆ = ≡-to-⊑ 𝓓 comm-eq
            ⦅1⦆ = lr-implication (L'-is-left-adjoint x (η τ))
                  (≤-is-transitive (L' x) (η σ) (η τ)
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
              lem' : L' x ≤ η τ
              lem' = rl-implication (L'-is-left-adjoint x (η τ))
                      (x            ⊑⟨ 𝓓 ⟩[ x-below-∐τ       ]
                       ∐-map τ      ⊑⟨ 𝓓 ⟩[ ≡-to-⊒ 𝓓 comm-eq ]
                       ∐-map' (η τ) ∎⟨ 𝓓 ⟩)

\end{code}
