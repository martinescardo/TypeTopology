Tom de Jong, early January 2022.

In category theory, the Ind-completion freely adds filtered colimits. For a
poset, the Ind-completion can be described as the preorder of directed families
into the poset, ordered by cofinality.

We construct the Ind-completion for a 𝓥-dcpo 𝓓 and show it is a preorder. We
define and characterize what it means for the map Ind → 𝓓 that takes suprema to
have a left adjoint. We also consider the poset reflection Ind/≈ of Ind and
define what it means for the induced map Ind/≈ → 𝓓 to have a left adjoint.

This development is used in exploring possible notions of continuous dcpo in
ContinuityDiscussion.lagda. In particular, the observation that the
Ind-completion is a preorder and not a poset is seen to be important there.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.IndCompletion
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

module Ind-completion
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 Ind : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Ind = Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , is-Directed 𝓓 α

 index-of-underlying-family : Ind → 𝓥 ̇
 index-of-underlying-family = pr₁

 underlying-family : (α : Ind) → index-of-underlying-family α → ⟨ 𝓓 ⟩
 underlying-family α = pr₁ (pr₂ α)

 _≲_ : Ind → Ind → 𝓥 ⊔ 𝓣 ̇
 (I , α , _) ≲ (J , β , _) = (i : I) → ∃ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j

 ≲-is-prop-valued : (α β : Ind) → is-prop (α ≲ β)
 ≲-is-prop-valued α β = Π-is-prop fe (λ i → ∥∥-is-prop)

 ≲-is-reflexive : (α : Ind) → α ≲ α
 ≲-is-reflexive (I , α , δ) i = ∣ i , reflexivity 𝓓 (α i) ∣

 ≲-is-transitive : (σ τ ρ : Ind) → σ ≲ τ → τ ≲ ρ → σ ≲ ρ
 ≲-is-transitive (I , α , δ) (J , β , ε) (K , γ , ϕ)
  α-cofinal-in-β β-cofinal-in-γ i = ∥∥-rec ∥∥-is-prop r (α-cofinal-in-β i)
   where
    r : (Σ j ꞉ J , α i ⊑⟨ 𝓓 ⟩ β j)
      → (∃ k ꞉ K , α i ⊑⟨ 𝓓 ⟩ γ k)
    r (j , u) = ∥∥-functor (λ (k , v) → k , (α i ⊑⟨ 𝓓 ⟩[ u ]
                                             β j ⊑⟨ 𝓓 ⟩[ v ]
                                             γ k ∎⟨ 𝓓 ⟩))
                           (β-cofinal-in-γ j)

\end{code}

We now construct directed suprema of 𝓥-small families in Ind.

\begin{code}

 Ind-∐ : {I : 𝓥 ̇ } (𝓐 : I → Ind)
       → is-directed _≲_ 𝓐
       → Ind
 Ind-∐ {I} 𝓐 (I-inhabited , 𝓐-semidirected) =
  Σ J , β , K-is-inhabited , β-is-semidirected
   where
    J : I → 𝓥 ̇
    J i = pr₁ (𝓐 i)
    α : (i : I) → J i → ⟨ 𝓓 ⟩
    α i = pr₁ (pr₂ (𝓐 i))
    δ : (i : I) → is-Directed 𝓓 (α i)
    δ i = pr₂ (pr₂ (𝓐 i))
    K : 𝓥 ̇
    K = Σ J
    β : K → ⟨ 𝓓 ⟩
    β (i , j) = α i j
    K-is-inhabited : ∥ K ∥
    K-is-inhabited =
     ∥∥-rec ∥∥-is-prop h I-inhabited
      where
       h : I → ∥ K ∥
       h i = ∥∥-functor (λ j → (i , j)) (inhabited-if-Directed 𝓓 (α i) (δ i))
    β-is-semidirected : is-semidirected (underlying-order 𝓓) β
    β-is-semidirected (i₁ , j₁) (i₂ , j₂) =
     ∥∥-rec ∥∥-is-prop f (𝓐-semidirected i₁ i₂)
      where
       f : (Σ i ꞉ I , (𝓐 i₁ ≲ 𝓐 i) × (𝓐 i₂ ≲ 𝓐 i))
         → ∃ k ꞉ K , (β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β k) × (β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β k)
       f (i , u₁ , u₂) = ∥∥-rec ∥∥-is-prop g (u₁ j₁)
        where
         g : (Σ jⁱ₁ ꞉ J i , β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β (i , jⁱ₁))
           → ∃ k ꞉ K , (β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β k) × (β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β k)
         g (jⁱ₁ , v₁) = ∥∥-rec ∥∥-is-prop h (u₂ j₂)
          where
           h : (Σ jⁱ₂ ꞉ J i , β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β (i , jⁱ₂))
             → ∃ k ꞉ K , (β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β k) × (β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β k)
           h (jⁱ₂ , v₂) = ∥∥-functor r
                           (semidirected-if-Directed 𝓓 (α i) (δ i) jⁱ₁ jⁱ₂)
            where
             r : (Σ j ꞉ J i , (α i jⁱ₁ ⊑⟨ 𝓓 ⟩ α i j) × (α i jⁱ₂ ⊑⟨ 𝓓 ⟩ α i j))
               → Σ k ꞉ K , (β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β k) × (β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β k)
             r (j , w₁ , w₂) = (i , j) ,
                               ( (β (i₁ , j₁)  ⊑⟨ 𝓓 ⟩[ v₁ ]
                                  β (i  , jⁱ₁) ⊑⟨ 𝓓 ⟩[ w₁ ]
                                  β (i  , j)   ∎⟨ 𝓓 ⟩)
                               , (β (i₂ , j₂)  ⊑⟨ 𝓓 ⟩[ v₂ ]
                                  β (i  , jⁱ₂) ⊑⟨ 𝓓 ⟩[ w₂ ]
                                  β (i  , j)   ∎⟨ 𝓓 ⟩))

 Ind-∐-is-directed : {I : 𝓥 ̇ } (𝓐 : I → Ind) (δ : is-directed _≲_ 𝓐)
                   → is-Directed 𝓓 (underlying-family (Ind-∐ 𝓐 δ))
 Ind-∐-is-directed 𝓐 δ = pr₂ (pr₂ (Ind-∐ 𝓐 δ))

 Ind-∐-is-upperbound : {I : 𝓥 ̇ } (𝓐 : I → Ind) (δ : is-directed _≲_ 𝓐)
                     → is-upperbound _≲_ (Ind-∐ 𝓐 δ) 𝓐
 Ind-∐-is-upperbound 𝓐 δ i j =
  ∣ (i , j) , reflexivity 𝓓 (pr₁ (pr₂ (𝓐 i)) j) ∣

 Ind-∐-is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } (𝓐 : I → Ind)
                                      (δ : is-directed _≲_ 𝓐)
                                    → is-lowerbound-of-upperbounds _≲_
                                       (Ind-∐ 𝓐 δ) 𝓐
 Ind-∐-is-lowerbound-of-upperbounds {A} 𝓐 _ _ ub (i , j) = ub i j

\end{code}

Taking suprema in our 𝓥-dcpo 𝓓 of directed families indexed into 𝓓 defines a
monotone map from Ind to 𝓓.

\begin{code}

 ∐-map : Ind → ⟨ 𝓓 ⟩
 ∐-map (I , α , δ) = ∐ 𝓓 δ

 ≲-to-⊑-of-∐ : {I J : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} {β : J → ⟨ 𝓓 ⟩}
               (δ : is-Directed 𝓓 α) (ε : is-Directed 𝓓 β)
             → (I , α , δ) ≲ (J , β , ε)
             → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
 ≲-to-⊑-of-∐ {I} {J} {α} {β} δ ε α-cofinal-in-β =
  ∐-⊑-if-cofinal 𝓓 α-cofinal-in-β δ ε

 ∐-map-is-monotone : (α β : Ind) → α ≲ β → ∐-map α ⊑⟨ 𝓓 ⟩ ∐-map β
 ∐-map-is-monotone (I , α , δ) (J , β , ε) = ≲-to-⊑-of-∐ δ ε

\end{code}

Since we can view every element of 𝓓 as a constant directed family into 𝓓, we
also have a map in the other direction which comes in useful at times.

\begin{code}

 ⌞_⌟ : ⟨ 𝓓 ⟩ → (𝟙{𝓥} → ⟨ 𝓓 ⟩)
 ⌞_⌟ x = λ _ → x

 ⌞⌟-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 ⌞ x ⌟
 ⌞⌟-is-directed x = ∣ ⋆ ∣ , σ
  where
   σ : is-semidirected (underlying-order 𝓓) (λ _ → x)
   σ i j = ∣ ⋆ , reflexivity 𝓓 x , reflexivity 𝓓 x ∣

 ι : ⟨ 𝓓 ⟩ → Ind
 ι x = 𝟙 , ⌞ x ⌟ , ⌞⌟-is-directed x

\end{code}

In our discussions on the notion of continuous dcpo we will be interested in
∐-map having a left adjoint, see ContinuityDiscussion.lagda.

We define what that means here and note that it is helpful to consider an
auxilliary relation between Ind(D) and D that we call "being left adjunct to",
because a map L : D → Ind(D) is a left adjoint to ∐-map precisely when L(x) is
left adjunct to x for every x : D.

\begin{code}

 _is-left-adjunct-to_ : Ind → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 α is-left-adjunct-to x = (β : Ind) → (α ≲ β) ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map β)

 being-left-adjunct-to-is-prop : (σ : Ind) (x : ⟨ 𝓓 ⟩)
                               → is-prop (σ is-left-adjunct-to x)
 being-left-adjunct-to-is-prop σ x =
  Π-is-prop fe (λ τ → ↔-is-prop fe fe (≲-is-prop-valued σ τ)
                                      (prop-valuedness 𝓓 x (∐-map τ)))

 left-adjoint-to-∐-map : (⟨ 𝓓 ⟩ → Ind) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 left-adjoint-to-∐-map L = (x : ⟨ 𝓓 ⟩) → L x is-left-adjunct-to x

 being-left-adjoint-to-∐-map-is-prop : (L : ⟨ 𝓓 ⟩ → Ind)
                                     → is-prop (left-adjoint-to-∐-map L)
 being-left-adjoint-to-∐-map-is-prop L =
  Π-is-prop fe (λ x → being-left-adjunct-to-is-prop (L x) x)

 ∐-map-has-specified-left-adjoint : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ∐-map-has-specified-left-adjoint = Σ left-adjoint-to-∐-map

\end{code}

We can equivalently describe the adjoint-condition in terms of directed suprema
and the way-below relation.

\begin{code}

 _approximates_ : Ind → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 (I , α , δ) approximates x = (∐ 𝓓 δ ＝ x) × ((i : I) → α i ≪⟨ 𝓓 ⟩ x)

 approximates-is-prop : (σ : Ind) (x : ⟨ 𝓓 ⟩) → is-prop (σ approximates x)
 approximates-is-prop σ x =
  ×-is-prop (sethood 𝓓) (Π-is-prop fe (λ i → ≪-is-prop-valued 𝓓))

 is-approximating : (⟨ 𝓓 ⟩ → Ind) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-approximating L = (x : ⟨ 𝓓 ⟩) → (L x) approximates x

 left-adjunct-to-if-approximates : (σ : Ind) (x : ⟨ 𝓓 ⟩)
                                 → σ approximates x → σ is-left-adjunct-to x
 left-adjunct-to-if-approximates σ@(I , α , δ) x (x-sup-of-α , α-way-below-x)
                                 τ@(J , β , ε) = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇒⦆ : σ ≲ τ → x ⊑⟨ 𝓓 ⟩ ∐-map τ
   ⦅⇒⦆ α-cofinal-in-β = transport (λ - → - ⊑⟨ 𝓓 ⟩ ∐-map τ) x-sup-of-α
                        (≲-to-⊑-of-∐ δ ε α-cofinal-in-β)
   ⦅⇐⦆ : x ⊑⟨ 𝓓 ⟩ ∐-map τ → σ ≲ τ
   ⦅⇐⦆ x-below-∐β i = α-way-below-x i J β ε x-below-∐β

 approximates-if-left-adjunct-to : (σ : Ind) (x : ⟨ 𝓓 ⟩)
                                 → σ is-left-adjunct-to x
                                 → σ approximates x
 approximates-if-left-adjunct-to σ@(I , α , δ) x ladj =
  x-is-sup-of-α , α-way-below-x
   where
    α-way-below-x : (i : I) → α i ≪⟨ 𝓓 ⟩ x
    α-way-below-x i J β ε x-below-∐β = h i
     where
      h : (I , α , δ) ≲ (J , β , ε)
      h = rl-implication (ladj (J , β , ε)) x-below-∐β
    x-is-sup-of-α : ∐ 𝓓 δ ＝ x
    x-is-sup-of-α = antisymmetry 𝓓 (∐ 𝓓 δ) x ⦅1⦆ ⦅2⦆
     where
      ⦅1⦆ : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ x
      ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 δ x
            (λ i → ≪-to-⊑ 𝓓 (α-way-below-x i))
      ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
      ⦅2⦆ = lr-implication (ladj σ) (≲-is-reflexive σ)

 approximate-left-adjunct-to-≃ : (σ : Ind) (x : ⟨ 𝓓 ⟩)
                               → σ approximates x ≃ σ is-left-adjunct-to x
 approximate-left-adjunct-to-≃ σ x = logically-equivalent-props-are-equivalent
                                      (approximates-is-prop σ x)
                                      (being-left-adjunct-to-is-prop σ x)
                                      (left-adjunct-to-if-approximates σ x)
                                      (approximates-if-left-adjunct-to σ x)

 left-adjoint-to-∐-map-characterization : (L : ⟨ 𝓓 ⟩ → Ind)
                                        → is-approximating L
                                        ≃ left-adjoint-to-∐-map L
 left-adjoint-to-∐-map-characterization L =
  Π-cong fe fe (λ x → approximate-left-adjunct-to-≃ (L x) x)

\end{code}

One may observe that the type (left-to-adjoint-to-∐-map L) does not require L to
be functorial/monotone, as would normally be required for an adjoint/Galois
connection. But this actually follows from the "hom-set" condition, as we show
now.

\begin{code}

 left-adjoint-to-∐-map-is-monotone : (L : ⟨ 𝓓 ⟩ → Ind)
                                   → left-adjoint-to-∐-map L
                                   → (x y : ⟨ 𝓓 ⟩)
                                   → x ⊑⟨ 𝓓 ⟩ y
                                   → L x ≲ L y
 left-adjoint-to-∐-map-is-monotone L L-left-adjoint x y x-below-y = γ
  where
   γ : L x ≲ L y
   γ = rl-implication (L-left-adjoint x (L y)) x-below-∐-Ly
    where
     x-below-∐-Ly = x           ⊑⟨ 𝓓 ⟩[ x-below-y             ]
                    y           ⊑⟨ 𝓓 ⟩[ ＝-to-⊒ 𝓓 (pr₁ approx) ]
                    ∐-map (L y) ∎⟨ 𝓓 ⟩
      where
       approx : L y approximates y
       approx = approximates-if-left-adjunct-to (L y) y (L-left-adjoint y)

\end{code}

Because Ind is a preorder and not a poset, the type expressing that ∐-map has a
specified left adjoint is not a proposition, as the supposed left adjoint can
map elements of 𝓓 to bicofinal (but nonequal) directed families.

We could take the poset reflection Ind/≈ of Ind and ask that the map Ind/≈ → 𝓓
induced by the supremum-map Ind → 𝓓 has a left adjoint to obtain a type that is
a proposition. We describe that process here.

This is *not* the same as asking that ∐-map : Ind → 𝓓 has an unspecified left
adjoint, as we explain in ContinuityDiscussion.lagda.

\begin{code}

module Ind-completion-poset-reflection
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 open import OrderedTypes.PosetReflection pt fe pe
 open poset-reflection Ind _≲_ ≲-is-prop-valued ≲-is-reflexive ≲-is-transitive public

 Ind/≈ : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 Ind/≈ = poset-reflection-carrier

 Ind/≈-is-set : is-set Ind/≈
 Ind/≈-is-set = poset-reflection-is-set

 ∐-map/-specification :
   ∃! f̃ ꞉ (Ind/≈ → ⟨ 𝓓 ⟩) , ((σ' τ' : Ind/≈) → σ' ≤ τ' → f̃ σ' ⊑⟨ 𝓓 ⟩ f̃ τ')
                          × (f̃ ∘ η ∼ ∐-map)
 ∐-map/-specification =
  universal-property (underlying-order 𝓓) (sethood 𝓓) (prop-valuedness 𝓓)
                     (reflexivity 𝓓) (transitivity 𝓓) (antisymmetry 𝓓)
                     ∐-map ∐-map-is-monotone

 ∐-map/ : Ind/≈ → ⟨ 𝓓 ⟩
 ∐-map/ = ∃!-witness ∐-map/-specification

 ∐-map/-triangle : (α : Ind) → ∐-map/ (η α) ＝ ∐-map α
 ∐-map/-triangle = pr₂ (∃!-is-witness ∐-map/-specification)

 left-adjoint-to-∐-map/ : (⟨ 𝓓 ⟩ → Ind/≈)
                        → 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 left-adjoint-to-∐-map/ L' =
  (x : ⟨ 𝓓 ⟩) (α' : Ind/≈) → (L' x ≤ α') ↔ (x ⊑⟨ 𝓓 ⟩ ∐-map/ α')

 being-left-adjoint-to-∐-map/-is-prop : (L' : ⟨ 𝓓 ⟩ → Ind/≈)
                                      → is-prop (left-adjoint-to-∐-map/ L')
 being-left-adjoint-to-∐-map/-is-prop L' =
  Π₂-is-prop fe (λ x α' → ×-is-prop
                           (Π-is-prop fe (λ _ → prop-valuedness 𝓓 x (∐-map/ α')))
                           (Π-is-prop fe (λ _ → ≤-is-prop-valued (L' x) α')))

 ∐-map/-has-specified-left-adjoint : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 ∐-map/-has-specified-left-adjoint = Σ left-adjoint-to-∐-map/

 ∐-map/-having-left-adjoint-is-prop : is-prop ∐-map/-has-specified-left-adjoint
 ∐-map/-having-left-adjoint-is-prop
  (L , L-is-left-adjoint) (L' , L'-is-left-adjoint) =
   to-subtype-＝ being-left-adjoint-to-∐-map/-is-prop
                (dfunext fe (λ x → ≤-is-antisymmetric (L x) (L' x)
                  (rl-implication (L-is-left-adjoint x (L' x))
                                  (lr-implication (L'-is-left-adjoint x (L' x))
                                    (≤-is-reflexive (L' x))))
                  (rl-implication (L'-is-left-adjoint x (L x))
                                  (lr-implication (L-is-left-adjoint x (L x))
                                    (≤-is-reflexive (L x))))))

\end{code}
