Tom de Jong, early January 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

module DcpoContinuous
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

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

 is-semidirected' : {A : 𝓥 ̇  } (𝓐 : A → Ind)
                  → 𝓥 ⊔ 𝓣 ̇
 is-semidirected' {A} 𝓐 = (a₁ a₂ : A) → ∃ a ꞉ A , (𝓐 a₁ ≲ 𝓐 a) × (𝓐 a₂ ≲ 𝓐 a)

 Ind-∐ : {I : 𝓥 ̇  } (𝓐 : I → Ind)
       → ∥ I ∥
       → is-semidirected' 𝓐
       → Ind
 Ind-∐ {I} 𝓐 I-inhabited 𝓐-semidirected =
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

 Ind-∐-is-upperbound : {I : 𝓥 ̇  } (𝓐 : I → Ind)
                       (ρ : ∥ I ∥) (σ : is-semidirected' 𝓐)
                     → is-upperbound _≲_ (Ind-∐ 𝓐 ρ σ) 𝓐
 Ind-∐-is-upperbound 𝓐 ρ σ i j =
  ∣ (i , j) , (reflexivity 𝓓 (pr₁ (pr₂ (𝓐 i)) j)) ∣

 Ind-∐-is-lowerbound-of-upperbounds : {I : 𝓥 ̇  } (𝓐 : I → Ind)
                                      (ρ : ∥ I ∥) (σ : is-semidirected' 𝓐)
                                    → is-lowerbound-of-upperbounds _≲_
                                       (Ind-∐ 𝓐 ρ σ) 𝓐
 Ind-∐-is-lowerbound-of-upperbounds {A} 𝓐 ρ σ _ ub (i , j) = ub i j

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

-- TODO: Review this
{-
structural-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩)
                 → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
structural-basis 𝓓 {B} β =
  (x : ⟨ 𝓓 ⟩) → Σ I ꞉ 𝓥 ̇  ,
                Σ α ꞉ (I → B) , ((i : I) → β (α i) ≪⟨ 𝓓 ⟩ x)
                              × (Σ δ ꞉ is-Directed 𝓓 (β ∘ α) , ∐ 𝓓 δ ≡ x)
-}

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
 approximating-family-∐-⊒ x = ≡-to-⊑ 𝓓 ((approximating-family-∐-≡ x) ⁻¹)

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
   𝓘 = Ind-∐ 𝓑 (inhabited-if-Directed 𝓓 αʸ δʸ) σ
    where
     σ : is-semidirected' 𝓑
     σ i₁ i₂ = ∥∥-functor r (semidirected-if-Directed 𝓓 αʸ δʸ i₁ i₂)
      where
       r : (Σ i ꞉ Iʸ , (αʸ i₁ ⊑⟨ 𝓓 ⟩ αʸ i) × (αʸ i₂ ⊑⟨ 𝓓 ⟩ αʸ i))
         → Σ i ꞉ Iʸ , (𝓑 i₁ ≲ 𝓑 i) × (𝓑 i₂ ≲ 𝓑 i)
       r (i , u , v) = i , l₁ , l₂
        where
         w = approximating-family-∐-⊒ (αʸ i)
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
  (d₁ , x-way-below-d₁ , d₁-way-below-z) ← str-≪-unary-interpolation
                                            x-way-below-z
  (d₂ , y-way-below-d₂ , d₂-way-below-z) ← str-≪-unary-interpolation
                                            y-way-below-z

  (i₁ , d₁-below-zⁱ₁)                    ← d₁-way-below-z _ _
                                            (approximating-family-is-directed z)
                                            (approximating-family-∐-⊒ z)
  (i₂ , d₂-below-zⁱ₂)                    ← d₂-way-below-z _ _
                                            (approximating-family-is-directed z)
                                            (approximating-family-∐-⊒ z)

  (i , zⁱ₁-below-zⁱ , zⁱ₂-below-zⁱ)      ← semidirected-if-Directed 𝓓 _
                                            (approximating-family-is-directed z)
                                            i₁ i₂
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
