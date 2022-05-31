Tom de Jong, early January 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

module DcpoContinuous
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
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

\end{code}

First some material on 𝓥-Ind...TODO: Write more comments.

\begin{code}

module Ind-completion
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 Ind : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Ind = Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , is-Directed 𝓓 α

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

 Ind-∐ : {I : 𝓥 ̇  } (𝓐 : I → Ind)
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
       f (i , u₁ , u₂) = ∥∥-rec ∥∥-is-prop g c₁
        where
         c₁ : ∃ jⁱ₁ ꞉ J i , β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β (i , jⁱ₁)
         c₁ = u₁ j₁
         g : (Σ jⁱ₁ ꞉ J i , β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β (i , jⁱ₁))
           → ∃ k ꞉ K , (β (i₁ , j₁) ⊑⟨ 𝓓 ⟩ β k) × (β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β k)
         g (jⁱ₁ , v₁) = ∥∥-rec ∥∥-is-prop h c₂
          where
           c₂ : ∃ jⁱ₂ ꞉ J i , β (i₂ , j₂) ⊑⟨ 𝓓 ⟩ β (i , jⁱ₂)
           c₂ = u₂ j₂
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

 Ind-∐-is-upperbound : {I : 𝓥 ̇  } (𝓐 : I → Ind) (δ : is-directed _≲_ 𝓐)
                     → is-upperbound _≲_ (Ind-∐ 𝓐 δ) 𝓐
 Ind-∐-is-upperbound 𝓐 δ i j =
  ∣ (i , j) , reflexivity 𝓓 (pr₁ (pr₂ (𝓐 i)) j) ∣

 Ind-∐-is-lowerbound-of-upperbounds : {I : 𝓥 ̇  } (𝓐 : I → Ind)
                                      (δ : is-directed _≲_ 𝓐)
                                    → is-lowerbound-of-upperbounds _≲_
                                       (Ind-∐ 𝓐 δ) 𝓐
 Ind-∐-is-lowerbound-of-upperbounds {A} 𝓐 _ _ ub (i , j) = ub i j

 ∐-map : Ind → ⟨ 𝓓 ⟩
 ∐-map (I , α , δ) = ∐ 𝓓 δ

 left-adjoint-to-∐-map-local : ⟨ 𝓓 ⟩ → Ind → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 left-adjoint-to-∐-map-local x α = (β : Ind) → (α ≲ β) ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map β)

 left-adjoint-to-∐-map-local-is-prop : (x : ⟨ 𝓓 ⟩) (σ : Ind)
                                     → is-prop (left-adjoint-to-∐-map-local x σ)
 left-adjoint-to-∐-map-local-is-prop x σ =
  Π-is-prop fe (λ τ → ⇔-is-prop fe fe (≲-is-prop-valued σ τ)
                                      (prop-valuedness 𝓓 x (∐-map τ)))

 left-adjoint-to-∐-map : (⟨ 𝓓 ⟩ → Ind) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 left-adjoint-to-∐-map L = (x : ⟨ 𝓓 ⟩) → left-adjoint-to-∐-map-local x (L x)
  -- (x : ⟨ 𝓓 ⟩) (α : Ind) → (L x ≲ α) ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map α)

 being-left-adjoint-to-∐-map-is-prop : (L : ⟨ 𝓓 ⟩ → Ind)
                                     → is-prop (left-adjoint-to-∐-map L)
 being-left-adjoint-to-∐-map-is-prop L =
  Π-is-prop fe (λ x → left-adjoint-to-∐-map-local-is-prop x (L x))

 ∐-map-has-specified-left-adjoint : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ∐-map-has-specified-left-adjoint = Σ left-adjoint-to-∐-map

 left-adjoint-to-∐-map-local-criterion : ⟨ 𝓓 ⟩ → Ind → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 left-adjoint-to-∐-map-local-criterion x (I , α , δ) =
  (∐ 𝓓 δ ≡ x) × ((i : I) → α i ≪⟨ 𝓓 ⟩ x)

 left-adjoint-to-∐-map-local-criterion-is-prop :
    (x : ⟨ 𝓓 ⟩) (σ : Ind)
  → is-prop (left-adjoint-to-∐-map-local-criterion x σ)
 left-adjoint-to-∐-map-local-criterion-is-prop x σ =
  ×-is-prop (sethood 𝓓) (Π-is-prop fe (λ i → ≪-is-prop-valued 𝓓))

 left-adjoint-to-∐-map-criterion : (⟨ 𝓓 ⟩ → Ind)
                                 → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 left-adjoint-to-∐-map-criterion L =
  (x : ⟨ 𝓓 ⟩) → left-adjoint-to-∐-map-local-criterion x (L x)

 ≲-to-⊑-of-∐ : {I J : 𝓥 ̇  } {α : I → ⟨ 𝓓 ⟩} {β : J → ⟨ 𝓓 ⟩}
               (δ : is-Directed 𝓓 α) (ε : is-Directed 𝓓 β)
             → (I , α , δ) ≲ (J , β , ε)
             → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
 ≲-to-⊑-of-∐ {I} {J} {α} {β} δ ε α-cofinal-in-β =
  ∐-⊑-if-cofinal 𝓓 α-cofinal-in-β δ ε

 ∐-map-is-monotone : (α β : Ind) → α ≲ β → ∐-map α ⊑⟨ 𝓓 ⟩ ∐-map β
 ∐-map-is-monotone (I , α , δ) (J , β , ε) = ≲-to-⊑-of-∐ δ ε

 ⌞_⌟ : ⟨ 𝓓 ⟩ → (𝟙{𝓥} → ⟨ 𝓓 ⟩)
 ⌞_⌟ x = λ _ → x

 ⌞⌟-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 ⌞ x ⌟
 ⌞⌟-is-directed x = ∣ ⋆ ∣ , σ
  where
   σ : is-semidirected (underlying-order 𝓓) (λ _ → x)
   σ i j = ∣ ⋆ , reflexivity 𝓓 x , reflexivity 𝓓 x ∣

 ι : ⟨ 𝓓 ⟩ → Ind
 ι x = 𝟙 , ⌞ x ⌟ , ⌞⌟-is-directed x

 left-adjoint-to-∐-map-characterization-local :
    (x : ⟨ 𝓓 ⟩) (σ : Ind)
  → left-adjoint-to-∐-map-local-criterion x σ
  ≃ left-adjoint-to-∐-map-local x σ
 left-adjoint-to-∐-map-characterization-local x σ@(I , α , δ) =
  logically-equivalent-props-are-equivalent
   (left-adjoint-to-∐-map-local-criterion-is-prop x σ)
   (left-adjoint-to-∐-map-local-is-prop x σ)
   ⦅⇒⦆ ⦅⇐⦆
   where
    ⦅⇒⦆ : left-adjoint-to-∐-map-local-criterion x σ
        → left-adjoint-to-∐-map-local x σ
    ⦅⇒⦆ (x-sup-of-α , α-way-below-x) τ@(J , β , ε) = lr , rl
     where
      lr : σ ≲ τ → x ⊑⟨ 𝓓 ⟩ ∐-map τ
      lr α-cofinal-in-β = transport (λ - → - ⊑⟨ 𝓓 ⟩ ∐-map τ) x-sup-of-α
                           (≲-to-⊑-of-∐ δ ε α-cofinal-in-β)
      rl : x ⊑⟨ 𝓓 ⟩ ∐-map τ → σ ≲ τ
      rl x-below-∐β i = α-way-below-x i J β ε x-below-∐β
    ⦅⇐⦆ : left-adjoint-to-∐-map-local x σ
        → left-adjoint-to-∐-map-local-criterion x σ
    ⦅⇐⦆ ladj = ⦅1⦆ , ⦅2⦆
     where
      ⦅2⦆ : (i : I) → α i ≪⟨ 𝓓 ⟩ x
      ⦅2⦆ i J β ε x-below-∐β = h i
       where
        h : (I , α , δ) ≲ (J , β , ε)
        h = rl-implication (ladj (J , β , ε)) x-below-∐β
      ⦅1⦆ : ∐ 𝓓 δ ≡ x
      ⦅1⦆ = antisymmetry 𝓓 (∐ 𝓓 δ) x u v
       where
        v : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
        v = lr-implication (ladj (I , α , δ)) (≲-is-reflexive (I , α , δ))
        u : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ x
        u = ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩[ ⦅a⦆ ]
            ∐ 𝓓 ε ⊑⟨ 𝓓 ⟩[ ⦅b⦆ ]
            x     ∎⟨ 𝓓 ⟩
         where
          ε : is-Directed 𝓓 ⌞ x ⌟
          ε = ⌞⌟-is-directed x
          ⦅a⦆ = ≲-to-⊑-of-∐ δ ε
                (rl-implication (ladj (ι x)) (∐-is-upperbound 𝓓 ε ⋆))
          ⦅b⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 ε x (λ _ → reflexivity 𝓓 x)

 left-adjoint-to-∐-map-characterization : (L : ⟨ 𝓓 ⟩ → Ind)
                                        → left-adjoint-to-∐-map-criterion L
                                        ≃ left-adjoint-to-∐-map L
 left-adjoint-to-∐-map-characterization L =
  Π-cong fe fe ⟨ 𝓓 ⟩
   (λ x → left-adjoint-to-∐-map-local-criterion x (L x))
   (λ x → left-adjoint-to-∐-map-local x (L x))
   (λ x → left-adjoint-to-∐-map-characterization-local x (L x))

\end{code}

\begin{code}

is-way-upperbound : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇  } (x : ⟨ 𝓓 ⟩) (α : I → ⟨ 𝓓 ⟩)
                  → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-way-upperbound 𝓓 {I} x α = (i : I) → α i ≪⟨ 𝓓 ⟩ x

\end{code}

We use record syntax to have descriptively named projections available without
having to add them as boilerplate.

\begin{code}

record structurally-continuous (𝓓 : DCPO {𝓤} {𝓣}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
 field
  index-of-approximating-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
  approximating-family : (x : ⟨ 𝓓 ⟩)
                       → (index-of-approximating-family x) → ⟨ 𝓓 ⟩
  approximating-family-is-directed : (x : ⟨ 𝓓 ⟩)
                                   → is-Directed 𝓓 (approximating-family x)
  approximating-family-is-way-below : (x : ⟨ 𝓓 ⟩)
                                    → is-way-upperbound 𝓓 x
                                       (approximating-family x)
  approximating-family-∐-≡ : (x : ⟨ 𝓓 ⟩)
                           → ∐ 𝓓 (approximating-family-is-directed x) ≡ x

structurally-continuous' : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
structurally-continuous' 𝓓 =
   (x : ⟨ 𝓓 ⟩)
 → Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → ⟨ 𝓓 ⟩) , (is-way-upperbound 𝓓 x α)
                                 × (Σ δ ꞉ is-Directed 𝓓 α , ∐ 𝓓 δ ≡ x)

structurally-continuous-prime : (𝓓 : DCPO {𝓤} {𝓣})
                              → structurally-continuous 𝓓
                              → structurally-continuous' 𝓓
structurally-continuous-prime 𝓓 C x =
   index-of-approximating-family x
 , approximating-family x
 , approximating-family-is-way-below x
 , approximating-family-is-directed x
 , approximating-family-∐-≡ x
 where
  open structurally-continuous C

structurally-continuous-unprime : (𝓓 : DCPO {𝓤} {𝓣})
                                → structurally-continuous' 𝓓
                                → structurally-continuous 𝓓
structurally-continuous-unprime 𝓓 C' = record {
  index-of-approximating-family     = λ x → pr₁ (C' x);
  approximating-family              = λ x → pr₁ (pr₂ (C' x));
  approximating-family-is-directed  = λ x → pr₁ (pr₂ (pr₂ (pr₂ (C' x))));
  approximating-family-is-way-below = λ x → pr₁ (pr₂ (pr₂ (C' x)));
  approximating-family-∐-≡          = λ x → pr₂ (pr₂ (pr₂ (pr₂ (C' x))))
 }

structurally-continuous-≃ : (𝓓 : DCPO {𝓤} {𝓣})
                          → structurally-continuous 𝓓
                          ≃ structurally-continuous' 𝓓
structurally-continuous-≃ 𝓓 = qinveq (structurally-continuous-prime 𝓓)
                                    ((structurally-continuous-unprime 𝓓) ,
                                     ((λ x → refl) , (λ x → refl)))

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (C : structurally-continuous 𝓓)
       where

 open structurally-continuous C

 approximating-family-∐-⊑ : (x : ⟨ 𝓓 ⟩)
                          → ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ x
 approximating-family-∐-⊑ x = ≡-to-⊑ 𝓓 (approximating-family-∐-≡ x)

 approximating-family-∐-⊒ : (x : ⟨ 𝓓 ⟩)
                          → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (approximating-family-is-directed x)
 approximating-family-∐-⊒ x = ≡-to-⊒ 𝓓 (approximating-family-∐-≡ x)

\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 Johnstone-Joyal₁ : ∐-map-has-specified-left-adjoint
                  → structurally-continuous 𝓓
 Johnstone-Joyal₁ (L , L-left-adjoint) = record {
   index-of-approximating-family     = λ x → pr₁ (L x);
   approximating-family              = λ x → pr₁ (pr₂ (L x));
   approximating-family-is-directed  = λ x → pr₂ (pr₂ (L x));
   approximating-family-is-way-below = λ x → pr₂ (crit x);
   approximating-family-∐-≡          = λ x → pr₁ (crit x)
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
     ϕ : structurally-continuous' 𝓓 → structurally-continuous 𝓓
     ϕ = structurally-continuous-unprime 𝓓
     ψ : structurally-continuous 𝓓 → structurally-continuous' 𝓓
     ψ = structurally-continuous-prime 𝓓
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
           (approximating-family-∐-⊒ 𝓓 C y)

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (C : structurally-continuous 𝓓)
       where

 open structurally-continuous C

 structurally-continuous-⊑-criterion :
    {x y : ⟨ 𝓓 ⟩}
  → ((i : index-of-approximating-family x) → approximating-family x i ⊑⟨ 𝓓 ⟩ y)
  → x ⊑⟨ 𝓓 ⟩ y
 structurally-continuous-⊑-criterion {x} {y} l =
  transport (λ - → - ⊑⟨ 𝓓 ⟩ y) (approximating-family-∐-≡ x) γ
   where
    γ : ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ y
    γ = ∐-is-lowerbound-of-upperbounds 𝓓 (approximating-family-is-directed x) y l

 str-≪-nullary-interpolation : (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
 str-≪-nullary-interpolation x =
  ∥∥-functor γ (inhabited-if-Directed 𝓓 (approximating-family x)
                                        (approximating-family-is-directed x))
   where
    γ : index-of-approximating-family x → Σ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
    γ i = (approximating-family x i , approximating-family-is-way-below x i)

 str-≪-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                           → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
 str-≪-unary-interpolation {x} {y} x-way-below-y = goal
  where
   Iʸ : 𝓥 ̇
   Iʸ = index-of-approximating-family y
   αʸ : Iʸ → ⟨ 𝓓 ⟩
   αʸ = approximating-family y
   δʸ : is-Directed 𝓓 αʸ
   δʸ = approximating-family-is-directed y
   J : (i : Iʸ) → 𝓥 ̇
   J i = index-of-approximating-family (αʸ i)
   β : (i : Iʸ) → J i → ⟨ 𝓓 ⟩
   β i = approximating-family (αʸ i)
   δ : (i : Iʸ) → is-Directed 𝓓 (β i)
   δ i = approximating-family-is-directed (αʸ i)

   open Ind-completion 𝓓
   𝓑 : Iʸ → Ind
   𝓑 i = J i , β i , δ i
   𝓘 : Ind
   𝓘 = Ind-∐ 𝓑 (inhabited-if-Directed 𝓓 αʸ δʸ , σ)
    where
     σ : is-semidirected _≲_ 𝓑
     σ i₁ i₂ = ∥∥-functor r (semidirected-if-Directed 𝓓 αʸ δʸ i₁ i₂)
      where
       r : (Σ i ꞉ Iʸ , (αʸ i₁ ⊑⟨ 𝓓 ⟩ αʸ i) × (αʸ i₂ ⊑⟨ 𝓓 ⟩ αʸ i))
         → Σ i ꞉ Iʸ , (𝓑 i₁ ≲ 𝓑 i) × (𝓑 i₂ ≲ 𝓑 i)
       r (i , u , v) = i , l₁ , l₂
        where
         w = approximating-family-∐-⊒ 𝓓 C (αʸ i)
         l₁ : 𝓑 i₁ ≲ 𝓑 i
         l₁ j = approximating-family-is-way-below (αʸ i₁) j (J i) (β i) (δ i)
                 (αʸ i₁     ⊑⟨ 𝓓 ⟩[ u ]
                  αʸ i      ⊑⟨ 𝓓 ⟩[ w ]
                  ∐ 𝓓 (δ i) ∎⟨ 𝓓 ⟩)
         l₂ : 𝓑 i₂ ≲ 𝓑 i
         l₂ j = approximating-family-is-way-below (αʸ i₂) j (J i) (β i) (δ i)
                 (αʸ i₂     ⊑⟨ 𝓓 ⟩[ v ]
                  αʸ i      ⊑⟨ 𝓓 ⟩[ w ]
                  ∐ 𝓓 (δ i) ∎⟨ 𝓓 ⟩)

   K : 𝓥 ̇
   K = pr₁ 𝓘
   γ : K → ⟨ 𝓓 ⟩
   γ = pr₁ (pr₂ 𝓘)
   γ-is-directed : is-Directed 𝓓 γ
   γ-is-directed = pr₂ (pr₂ 𝓘)

   y-below-∐-of-γ : y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
   y-below-∐-of-γ = structurally-continuous-⊑-criterion u
    where
     u : (i : Iʸ) → αʸ i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
     u i = structurally-continuous-⊑-criterion v
      where
       v : (j : J i) → β i j ⊑⟨ 𝓓 ⟩ ∐ 𝓓 γ-is-directed
       v j = ∐-is-upperbound 𝓓 γ-is-directed (i , j)

   x-below-γ : ∃ k ꞉ K , x ⊑⟨ 𝓓 ⟩ γ k
   x-below-γ = x-way-below-y K γ γ-is-directed y-below-∐-of-γ

   goal : ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
   goal = ∥∥-functor r lemma
    where
     r : (Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                               × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                               × (αʸ i ≪⟨ 𝓓 ⟩ y))
       → Σ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
     r (i , j , u , v , w) = (αʸ i , ⊑-≪-to-≪ 𝓓 u v , w)
     lemma : ∥ Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                                    × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                                    × (αʸ i ≪⟨ 𝓓 ⟩ y) ∥
     lemma = ∥∥-functor s x-below-γ
      where
       s : (Σ k ꞉ K , x ⊑⟨ 𝓓 ⟩ γ k)
         → Σ i ꞉ Iʸ , Σ j ꞉ J i , (x ⊑⟨ 𝓓 ⟩ β i j)
                                × (β i j ≪⟨ 𝓓 ⟩ αʸ i)
                                × (αʸ i ≪⟨ 𝓓 ⟩ y)
       s ((i , j) , l) = (i , j , l ,
                          approximating-family-is-way-below (αʸ i) j ,
                          approximating-family-is-way-below y i)

-- TODO: Comment on use of do-notation

 str-≪-binary-interpolation : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                            → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d)
                                          × (y ≪⟨ 𝓓 ⟩ d)
                                          × (d ≪⟨ 𝓓 ⟩ z)
 str-≪-binary-interpolation {x} {y} {z} x-way-below-z y-way-below-z = do
  let δ = approximating-family-is-directed z
  let l = approximating-family-∐-⊒ 𝓓 C z
  (d₁ , x-way-below-d₁ , d₁-way-below-z) ← str-≪-unary-interpolation
                                            x-way-below-z
  (d₂ , y-way-below-d₂ , d₂-way-below-z) ← str-≪-unary-interpolation
                                            y-way-below-z

  (i₁ , d₁-below-zⁱ₁)                    ← d₁-way-below-z _ _ δ l
  (i₂ , d₂-below-zⁱ₂)                    ← d₂-way-below-z _ _ δ l

  (i , zⁱ₁-below-zⁱ , zⁱ₂-below-zⁱ)      ← semidirected-if-Directed 𝓓 _ δ i₁ i₂
  let α = approximating-family z
  let d₁-below-αⁱ = d₁   ⊑⟨ 𝓓 ⟩[ d₁-below-zⁱ₁ ]
                    α i₁ ⊑⟨ 𝓓 ⟩[ zⁱ₁-below-zⁱ ]
                    α i  ∎⟨ 𝓓 ⟩
  let d₂-below-αⁱ = d₂   ⊑⟨ 𝓓 ⟩[ d₂-below-zⁱ₂ ]
                    α i₂ ⊑⟨ 𝓓 ⟩[ zⁱ₂-below-zⁱ ]
                    α i  ∎⟨ 𝓓 ⟩
  ∣ approximating-family z i , ≪-⊑-to-≪ 𝓓 x-way-below-d₁ d₁-below-αⁱ
                             , ≪-⊑-to-≪ 𝓓 y-way-below-d₂ d₂-below-αⁱ
                             , approximating-family-is-way-below z i ∣


\end{code}

Continuity and pseudocontinuity (for comparison)

\begin{code}

is-continuous-dcpo : DCPO {𝓤} {𝓣} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-continuous-dcpo 𝓓 = ∥ structurally-continuous 𝓓 ∥

being-continuous-dcpo-is-prop : (𝓓 : DCPO {𝓤} {𝓣})
                              → is-prop (is-continuous-dcpo 𝓓)
being-continuous-dcpo-is-prop 𝓓 = ∥∥-is-prop

-- is-continuous-dcpo' : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
-- is-continuous-dcpo' 𝓓 = ∥ structurally-continuous' 𝓓 ∥

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
 ∥∥-functor (λ C → structurally-continuous-prime 𝓓 C x) c

\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (c : is-continuous-dcpo 𝓓)
       where

 ≪-nullary-interpolation : (x : ⟨ 𝓓 ⟩) → ∃ y ꞉ ⟨ 𝓓 ⟩ , y ≪⟨ 𝓓 ⟩ x
 ≪-nullary-interpolation x =
  ∥∥-rec ∥∥-is-prop (λ C → str-≪-nullary-interpolation 𝓓 C x) c

 ≪-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                       → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d) × (d ≪⟨ 𝓓 ⟩ y)
 ≪-unary-interpolation x-way-below-y =
  ∥∥-rec ∥∥-is-prop (λ C → str-≪-unary-interpolation 𝓓 C x-way-below-y) c

 ≪-binary-interpolation : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                        → ∃ d ꞉ ⟨ 𝓓 ⟩ , (x ≪⟨ 𝓓 ⟩ d)
                                      × (y ≪⟨ 𝓓 ⟩ d)
                                      × (d ≪⟨ 𝓓 ⟩ z)
 ≪-binary-interpolation {x} {y} {z} u v =
  ∥∥-rec ∥∥-is-prop (λ C → str-≪-binary-interpolation 𝓓 C u v) c

\end{code}

Quotienting Ind and pseudocontinuity

TODO: Write some more

\begin{code}

open import UF-ImageAndSurjection

open ImageAndSurjection pt

record poset-reflection (F : Universe → Universe → Universe)
                        (X : 𝓤 ̇  ) (_≲_ : X → X → 𝓣 ̇  )
                        (≲-is-prop-valued : (x y : X) → is-prop (x ≲ y))
                        (≲-is-reflexive : (x : X) → x ≲ x)
                        (≲-is-transitive : (x y z : X) → x ≲ y → y ≲ z → x ≲ z)
                        : 𝓤ω where
 field
  X̃ : F 𝓤 𝓣 ̇   -- X̃ can live in any type universe, possibly depending on 𝓤 and 𝓣
  X̃-is-set : is-set X̃ -- This follows from the properties of ≤, so it's
                      -- actually redundant, but convenient to assume it.
  η : X → X̃
  η-is-surjective : is-surjection η
  _≤_ : X̃ → X̃ → 𝓣 ̇
  ≤-is-prop-valued : (x' y' : X̃) → is-prop (x' ≤ y')
  ≤-is-reflexive : (x' : X̃) → x' ≤ x'
  ≤-is-transitive : (x' y' z' : X̃) → x' ≤ y' → y' ≤ z' → x' ≤ z'
  ≤-is-antisymmetric : (x' y' : X̃) → x' ≤ y' → y' ≤ x' → x' ≡ y'
  η-preserves-order : (x y : X) → x ≲ y → η x ≤ η y
  η-reflects-order  : (x y : X) → η x ≤ η y → x ≲ y
  -- Important: the universal property should apply to *any* poset,
  -- possibly with different universe parameters than the preorder (X , ≲)
  -- and the poset (X̃ , ≤).
  universal-property : {Q : 𝓤' ̇  } (_⊑_ : Q → Q → 𝓣' ̇  )
                     → ((q : Q) → q ⊑ q)
                     → ((p q r : Q) → p ⊑ q → q ⊑ r → p ⊑ r)
                     → ((p q : Q) → p ⊑ q → q ⊑ p → p ≡ q)
                     → (f : X → Q)
                     → ((x y : X) → x ≲ y → f x ⊑ f y)
                     → ∃! f̃ ꞉ (X̃ → Q) , ((x' y' : X̃) → x' ≤ y' → f̃ x' ⊑ f̃ y')
                                      × (f̃ ∘ η ≡ f)

module _
        (F : Universe → Universe → Universe)
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 module _
         (pr : poset-reflection F Ind _≲_ ≲-is-prop-valued ≲-is-reflexive ≲-is-transitive)
        where

  open poset-reflection pr

  Ind' : F (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣) ̇
  Ind' = X̃

  Ind'-is-set : is-set Ind'
  Ind'-is-set = X̃-is-set

  ∐-map'-specification :
    Σ f̃ ꞉ (Ind' → ⟨ 𝓓 ⟩) , ((σ' τ' : Ind') → σ' ≤ τ'
                                           → f̃ σ' ⊑⟨ 𝓓 ⟩ f̃ τ')
                         × (f̃ ∘ η ≡ ∐-map)
  ∐-map'-specification =
   center (universal-property (underlying-order 𝓓)
                              (reflexivity 𝓓) (transitivity 𝓓) (antisymmetry 𝓓)
                              ∐-map ∐-map-is-monotone)

  ∐-map' : Ind' → ⟨ 𝓓 ⟩
  ∐-map' = pr₁ ∐-map'-specification

  left-adjoint-to-∐-map' : (⟨ 𝓓 ⟩ → Ind')
                         → (𝓥 ⊔ 𝓤 ⊔ 𝓣 ⊔ F (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)) ̇
  left-adjoint-to-∐-map' L' =
   (x : ⟨ 𝓓 ⟩) (α' : Ind') → (L' x ≤ α') ⇔ (x ⊑⟨ 𝓓 ⟩ ∐-map' α')

  being-left-adjoint-to-∐-map'-is-prop : (L' : ⟨ 𝓓 ⟩ → Ind')
                                       → is-prop (left-adjoint-to-∐-map' L')
  being-left-adjoint-to-∐-map'-is-prop L' =
   Π₂-is-prop fe (λ x α' → ×-is-prop
                            (Π-is-prop fe (λ _ → prop-valuedness 𝓓 x (∐-map' α')))
                            (Π-is-prop fe (λ _ → ≤-is-prop-valued (L' x) α')))

  ∐-map'-has-specified-left-adjoint : (𝓥 ⊔ 𝓤 ⊔ 𝓣 ⊔ F (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)) ̇
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
    ladj x α' = ∥∥-rec goal-is-prop
                       r
                       (η-is-surjective α')
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
            eq₂ = happly (pr₂ (pr₂ ∐-map'-specification)) α
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
   ∥∥-rec ∥∥-is-prop r (η-is-surjective (L' x))
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
           comm-eq = happly (pr₂ (pr₂ ∐-map'-specification)) τ
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
             lem = back-transport (λ - → - ≤ η τ) p lem'
              where
               lem' : L' x ≤ η τ
               lem' = rl-implication (L'-is-left-adjoint x (η τ))
                       (x            ⊑⟨ 𝓓 ⟩[ x-below-∐τ       ]
                        ∐-map τ      ⊑⟨ 𝓓 ⟩[ ≡-to-⊒ 𝓓 comm-eq ]
                        ∐-map' (η τ) ∎⟨ 𝓓 ⟩)




{-
module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 open Ind-completion 𝓓

 _≈_ : Ind → Ind → 𝓥 ⊔ 𝓣 ̇
 α ≈ β = α ≲ β × β ≲ α

 ≈-is-prop-valued : (α β : Ind) → is-prop (α ≈ β)
 ≈-is-prop-valued α β = ×-is-prop (≲-is-prop-valued α β) (≲-is-prop-valued β α)

 ≈-is-reflexive : (α : Ind) → α ≈ α
 ≈-is-reflexive α = (≲-is-reflexive α) , (≲-is-reflexive α)

 ≈-is-symmetric : (α β : Ind) → α ≈ β → β ≈ α
 ≈-is-symmetric α β (u , v) = (v , u)

 ≈-is-transitive : (α β γ : Ind) → α ≈ β → β ≈ γ → α ≈ γ
 ≈-is-transitive α β γ (p , q) (u , v) =
  (≲-is-transitive α β γ p u) , (≲-is-transitive γ β α v q)

 open import UF-Quotient pt fe pe

 open quotient Ind _≈_
       ≈-is-prop-valued ≈-is-reflexive ≈-is-symmetric ≈-is-transitive

 Ind' = X/≈ -- the quotient

 _≲'_ : Ind' → Ind' → {!!} ̇
 _≲'_ x = {!!}

 -- TODO: Continue...
 -- Implement poset reflection abstractly? Perhaps just assume it (abstractly) here
-}

\end{code}

Local smallness...

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 ≪-is-small-valued-str : structurally-continuous 𝓓
                       → is-locally-small 𝓓
                       → (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
 ≪-is-small-valued-str C ls x y = (∃ i ꞉ I , x ⊑ₛ α i) , ψ
  where
   open is-locally-small ls
   open structurally-continuous C
   I : 𝓥 ̇
   I = index-of-approximating-family y
   α : I → ⟨ 𝓓 ⟩
   α = approximating-family y
   ψ : (∃ i ꞉ I , x ⊑ₛ α i) ≃ (x ≪⟨ 𝓓 ⟩ y)
   ψ = logically-equivalent-props-are-equivalent ∥∥-is-prop (≪-is-prop-valued 𝓓)
        ⦅⇒⦆ ⦅⇐⦆
    where
     ⦅⇐⦆ : x ≪⟨ 𝓓 ⟩ y → ∃ i ꞉ I , x ⊑ₛ α i
     ⦅⇐⦆ x-way-below-y = ∥∥-functor r (x-way-below-y I α
                                      (approximating-family-is-directed y)
                                      (approximating-family-∐-⊒ 𝓓 C y))
      where
       r : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i) → Σ i ꞉ I , x ⊑ₛ α i
       r (i , x-below-αᵢ) = (i , ⊑-to-⊑ₛ x-below-αᵢ)
     ⦅⇒⦆ : (∃ i ꞉ I , x ⊑ₛ α i) → x ≪⟨ 𝓓 ⟩ y
     ⦅⇒⦆ h J β ε y-below-∐β = ∥∥-rec ∥∥-is-prop r h
      where
       r : (Σ i ꞉ I , x ⊑ₛ α i) → ∃ j ꞉ J , x ⊑⟨ 𝓓 ⟩ β j
       r (i , x-belowₛ-αᵢ) = ⊑-≪-to-≪ 𝓓 x-below-αᵢ
                                         (approximating-family-is-way-below y i)
                                         J β ε y-below-∐β
        where
         x-below-αᵢ : x ⊑⟨ 𝓓 ⟩ α i
         x-below-αᵢ = ⊑ₛ-to-⊑ x-belowₛ-αᵢ

 ≪-is-small-valued-str' : structurally-continuous 𝓓
                        → is-locally-small 𝓓
                        → Σ _≪ₛ_ ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇  )
                        , ((x y : ⟨ 𝓓 ⟩) → (x ≪ₛ y) ≃ (x ≪⟨ 𝓓 ⟩ y))
 ≪-is-small-valued-str' C ls =
  ⌜ small-binary-relation-equivalence ⌝ (≪-is-small-valued-str C ls)

 ≪-is-small-valued-str-converse : structurally-continuous 𝓓
                                → ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
                                → is-locally-small 𝓓
 ≪-is-small-valued-str-converse C ≪-is-small-valued =
  ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
   where
    _≪ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
    x ≪ₛ y = pr₁ (≪-is-small-valued x y)
    φ : (x y : ⟨ 𝓓 ⟩) → x ≪ₛ y ≃ x ≪⟨ 𝓓 ⟩ y
    φ x y = pr₂ (≪-is-small-valued x y)
    γ : (x y : ⟨ 𝓓 ⟩) → is-small (x ⊑⟨ 𝓓 ⟩ y)
    γ x y = (∀ (i : I) → α i ≪ₛ y) , ψ
     where
      open structurally-continuous C
      I : 𝓥 ̇
      I = index-of-approximating-family x
      α : I → ⟨ 𝓓 ⟩
      α = approximating-family x
      ψ : (∀ (i : I) → α i ≪ₛ y) ≃ x ⊑⟨ 𝓓 ⟩ y
      ψ = logically-equivalent-props-are-equivalent
           (Π-is-prop fe (λ i → equiv-to-prop (φ (α i) y) (≪-is-prop-valued 𝓓)))
           (prop-valuedness 𝓓 x y)
           ⦅⇒⦆ ⦅⇐⦆
       where
        ⦅⇐⦆ : x ⊑⟨ 𝓓 ⟩ y → (∀ (i : I) → α i ≪ₛ y)
        ⦅⇐⦆ x-below-y i =
         ⌜ φ (α i) y ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (approximating-family-is-way-below x i)
                                      x-below-y)
        ⦅⇒⦆ : (∀ (i : I) → α i ≪ₛ y) → x ⊑⟨ 𝓓 ⟩ y
        ⦅⇒⦆ α-way-below-y = x     ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
                            ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
                            y     ∎⟨ 𝓓 ⟩
         where
          δ : is-Directed 𝓓 α
          δ = approximating-family-is-directed x
          ⦅1⦆ = approximating-family-∐-⊒ 𝓓 C x
          ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 δ y
                (λ i → ≪-to-⊑ 𝓓 (⌜ φ (α i) y ⌝ (α-way-below-y i)))


 module _
         (pe : Prop-Ext)
        where

  open import UF-Size hiding (is-small ; is-locally-small)

  ≪-is-small-valued : is-continuous-dcpo 𝓓
                    → is-locally-small 𝓓
                    → (x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y)
  ≪-is-small-valued c ls x y = ∥∥-rec p (λ C → ≪-is-small-valued-str C ls x y) c
   where
    p : is-prop (is-small (x ≪⟨ 𝓓 ⟩ y))
    p = prop-being-small-is-prop (λ _ → pe) (λ _ _ → fe)
         (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓) 𝓥

  ≪-is-small-valued' : is-continuous-dcpo 𝓓
                     → is-locally-small 𝓓
                     → Σ _≪ₛ_ ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇  )
                     , ((x y : ⟨ 𝓓 ⟩) → (x ≪ₛ y) ≃ (x ≪⟨ 𝓓 ⟩ y))
  ≪-is-small-valued' c ls =
   ⌜ small-binary-relation-equivalence ⌝ (≪-is-small-valued c ls)

  ≪-is-small-valued-converse : is-continuous-dcpo 𝓓
                             → ((x y : ⟨ 𝓓 ⟩) → is-small (x ≪⟨ 𝓓 ⟩ y))
                             → is-locally-small 𝓓
  ≪-is-small-valued-converse c ws =
   ∥∥-rec (being-locally-small-is-prop 𝓓 (λ _ → pe))
    (λ C → ≪-is-small-valued-str-converse C ws) c

\end{code}

TODO: Write comment

\begin{code}

record structurally-algebraic (𝓓 : DCPO {𝓤} {𝓣}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
 field
  index-of-compact-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
  compact-family : (x : ⟨ 𝓓 ⟩) → (index-of-compact-family x) → ⟨ 𝓓 ⟩
  compact-family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (compact-family x)
  compact-family-is-compact : (x : ⟨ 𝓓 ⟩) (i : index-of-compact-family x)
                            → is-compact 𝓓 (compact-family x i)
  compact-family-∐-≡ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (compact-family-is-directed x) ≡ x

is-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-algebraic-dcpo 𝓓 = ∥ structurally-algebraic 𝓓 ∥

structurally-continuous-if-structurally-algebraic :
   (𝓓 : DCPO {𝓤} {𝓣})
 → structurally-algebraic 𝓓 → structurally-continuous 𝓓
structurally-continuous-if-structurally-algebraic 𝓓 sa = record {
  index-of-approximating-family     = index-of-compact-family;
  approximating-family              = compact-family;
  approximating-family-is-directed  = compact-family-is-directed;
  approximating-family-is-way-below = γ;
  approximating-family-∐-≡          = compact-family-∐-≡
 }
  where
   open structurally-algebraic sa
   γ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (compact-family x)
   γ x i = ≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i) l
    where
     l = compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
         ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
         x                                  ∎⟨ 𝓓 ⟩
      where
       ⦅1⦆ = ∐-is-upperbound 𝓓 (compact-family-is-directed x) i
       ⦅2⦆ = ≡-to-⊑ 𝓓 (compact-family-∐-≡ x)

is-continuous-dcpo-if-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                                     → is-algebraic-dcpo 𝓓
                                     → is-continuous-dcpo 𝓓
is-continuous-dcpo-if-algebraic-dcpo 𝓓 =
 ∥∥-functor (structurally-continuous-if-structurally-algebraic 𝓓)

\end{code}

TO DO

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 structural-continuity-of-dcpo-preserved-by-continuous-retract :
    structurally-continuous 𝓔
  → structurally-continuous 𝓓
 structural-continuity-of-dcpo-preserved-by-continuous-retract C =
  record
    { index-of-approximating-family =
       λ x → index-of-approximating-family (s x)
    ; approximating-family =
       λ x → r ∘ approximating-family (s x)
    ; approximating-family-is-directed = lemma₁
    ; approximating-family-is-way-below = lemma₂
    ; approximating-family-∐-≡ = lemma₃
    }
  where
   open structurally-continuous C
   α : (y : ⟨ 𝓔 ⟩) → index-of-approximating-family y → ⟨ 𝓔 ⟩
   α = approximating-family
   lemma₁ : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (r ∘ α (s x))
   lemma₁ x = image-is-directed' 𝓔 𝓓 𝕣
               (approximating-family-is-directed (s x))
   lemma₂ : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (r ∘ α (s x))
   lemma₂ x i J β δ x-below-∐β =
    ∥∥-functor h (approximating-family-is-way-below (s x) i J (s ∘ β) ε l)
     where
      h : (Σ j ꞉ J , α (s x) i ⊑⟨ 𝓔 ⟩ s (β j))
        → Σ j ꞉ J , r (α (s x) i) ⊑⟨ 𝓓 ⟩ β j
      h (j , u) = (j , v)
       where
        v = r (α (s x) i) ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
            r (s (β j))   ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
            β j           ∎⟨ 𝓓 ⟩
         where
          ⦅1⦆ = monotone-if-continuous 𝓔 𝓓 𝕣
                (α (s x) i) (s (β j)) u
          ⦅2⦆ = ≡-to-⊑ 𝓓 (s-section-of-r (β j))
      ε : is-Directed 𝓔 (s ∘ β)
      ε = image-is-directed' 𝓓 𝓔 𝕤 δ
      l = s x       ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
          s (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
          ∐ 𝓔 ε     ∎⟨ 𝓔 ⟩
       where
        ⦅1⦆ = monotone-if-continuous 𝓓 𝓔 𝕤
              x (∐ 𝓓 δ) x-below-∐β
        ⦅2⦆ = continuous-∐-⊑ 𝓓 𝓔 𝕤 δ
   lemma₃ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (lemma₁ x) ≡ x
   lemma₃ x = ∐ 𝓓 (lemma₁ x) ≡⟨ ⦅1⦆ ⟩
              r (∐ 𝓔 δ)      ≡⟨ ⦅2⦆ ⟩
              r (s x)        ≡⟨ ⦅3⦆ ⟩
              x              ∎
    where
     δ : is-Directed 𝓔 (α (s x))
     δ = approximating-family-is-directed (s x)
     ⦅1⦆ = (continuous-∐-≡ 𝓔 𝓓 𝕣 δ) ⁻¹
     ⦅2⦆ = ap r (approximating-family-∐-≡ (s x))
     ⦅3⦆ = s-section-of-r x

 continuity-of-dcpo-preserved-by-continuous-retract : is-continuous-dcpo 𝓔
                                                    → is-continuous-dcpo 𝓓
 continuity-of-dcpo-preserved-by-continuous-retract =
  ∥∥-functor structural-continuity-of-dcpo-preserved-by-continuous-retract

\end{code}
