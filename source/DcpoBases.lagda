Tom de Jong, early January 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-FunExt
open import UF-PropTrunc

open import UF-Subsingletons

module DcpoBases
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF-Base hiding (_≈_)
open import UF-Equiv
open import UF-EquivalenceExamples


open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥
open import DcpoContinuous pt fe 𝓥
open import DcpoMiscelanea pt fe 𝓥
open import DcpoWayBelow pt fe 𝓥

open import UF-Size hiding (is-small ; is-locally-small)


-- TODO: Move elsewhere
module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {I : 𝓦 ̇  } {J : 𝓦' ̇  }
        (ρ : I ≃ J)
        (α : I → ⟨ 𝓓 ⟩)
       where

 reindexed-family : J → ⟨ 𝓓 ⟩
 reindexed-family = α ∘ ⌜ ρ ⌝⁻¹

 reindexed-family-is-directed : is-Directed 𝓓 α
                              → is-Directed 𝓓 reindexed-family
 reindexed-family-is-directed δ = J-inh , β-semidirected
  where
   J-inh : ∥ J ∥
   J-inh = ∥∥-functor ⌜ ρ ⌝ (inhabited-if-Directed 𝓓 α δ)
   β : J → ⟨ 𝓓 ⟩
   β = reindexed-family
   β-semidirected : is-semidirected (underlying-order 𝓓) β
   β-semidirected j₁ j₂ =
    ∥∥-functor r (semidirected-if-Directed 𝓓 α δ (⌜ ρ ⌝⁻¹ j₁) (⌜ ρ ⌝⁻¹ j₂))
     where
      r : (Σ i ꞉ I , (β j₁ ⊑⟨ 𝓓 ⟩ α i) × (β j₂ ⊑⟨ 𝓓 ⟩ α i))
        → (Σ j ꞉ J , (β j₁ ⊑⟨ 𝓓 ⟩ β j) × (β j₂ ⊑⟨ 𝓓 ⟩ β j))
      r (i , l₁ , l₂) = (⌜ ρ ⌝ i
                        , (β j₁                    ⊑⟨ 𝓓 ⟩[ l₁ ]
                           α i                     ⊑⟨ 𝓓 ⟩[ k ]
                           (α ∘ ⌜ ρ ⌝⁻¹ ∘ ⌜ ρ ⌝) i ∎⟨ 𝓓 ⟩)
                        , (β j₂                    ⊑⟨ 𝓓 ⟩[ l₂ ]
                           α i                     ⊑⟨ 𝓓 ⟩[ k ]
                           (α ∘ ⌜ ρ ⌝⁻¹ ∘ ⌜ ρ ⌝) i ∎⟨ 𝓓 ⟩))
       where
        k = ≡-to-⊑ 𝓓
             (ap α ((inverses-are-retractions ⌜ ρ ⌝ (⌜⌝-is-equiv ρ) i) ⁻¹))

 reindexed-family-sup : (x : ⟨ 𝓓 ⟩)
                      → is-sup (underlying-order 𝓓) x α
                      → is-sup (underlying-order 𝓓) x (reindexed-family)
 reindexed-family-sup x x-is-sup = ub , lb-of-ubs
  where
   β : J → ⟨ 𝓓 ⟩
   β = reindexed-family
   ub : is-upperbound (underlying-order 𝓓) x β
   ub i = sup-is-upperbound (underlying-order 𝓓) x-is-sup (⌜ ρ ⌝⁻¹ i)
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x β
   lb-of-ubs y y-is-ub = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                          x-is-sup y lemma
    where
     lemma : is-upperbound (underlying-order 𝓓) y α
     lemma i = α i         ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               β (⌜ ρ ⌝ i) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               y           ∎⟨ 𝓓 ⟩
      where
       ⦅1⦆ = ≡-to-⊑ 𝓓
             (ap α (inverses-are-retractions ⌜ ρ ⌝ (⌜⌝-is-equiv ρ) i) ⁻¹)
       ⦅2⦆ = y-is-ub (⌜ ρ ⌝ i)


module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↡ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ↡ᴮ x = Σ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x

 ι : (x : ⟨ 𝓓 ⟩) → ↡ᴮ x → ⟨ 𝓓 ⟩
 ι x = β ∘ pr₁

 record is-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ≪ᴮ-is-small : (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x))
   ↡ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (ι x)
   ↡ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (ι x)

  _≪ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ≪ᴮₛ x = pr₁ (≪ᴮ-is-small x b)

  ≪ᴮₛ-≃-≪ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
  ≪ᴮₛ-≃-≪ᴮ {b} {x} = pr₂ (≪ᴮ-is-small x b)

  ↡ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↡ᴮₛ x = Σ b ꞉ B , (b ≪ᴮₛ x)

  ιₛ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ x → ⟨ 𝓓 ⟩
  ιₛ x = β ∘ pr₁

  ↡ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (ιₛ x)
  ↡ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ≪ᴮₛ-≃-≪ᴮ)) (ι x) (↡ᴮ-is-directed x)

  ↡ᴮₛ-∐-≡ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ≡ x
  ↡ᴮₛ-∐-≡ x = antisymmetry 𝓓 (∐ 𝓓 (↡ᴮₛ-is-directed x)) x ⦅1⦆ ⦅2⦆
   where
    ⦅1⦆ : ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
    ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (↡ᴮₛ-is-directed x) x
          (λ (b , u) → sup-is-upperbound (underlying-order 𝓓) (↡ᴮ-is-sup x)
                        (b , (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ u)))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↡ᴮ-is-sup x)
          (∐ 𝓓 (↡ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↡ᴮₛ-is-directed x)
                        (b , (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ v)))

  ↡ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↡ᴮₛ-∐-⊑ x = ≡-to-⊑ 𝓓 (↡ᴮₛ-∐-≡ x)

  ↡ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
  ↡ᴮₛ-∐-⊒ x = ≡-to-⊑ 𝓓 ((↡ᴮₛ-∐-≡ x) ⁻¹)

  ↡ᴮₛ-way-below : (x : ⟨ 𝓓 ⟩) (b : ↡ᴮₛ x) → ιₛ x b ≪⟨ 𝓓 ⟩ x
  ↡ᴮₛ-way-below x (b , u) = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ u



 module _
         (sb : is-small-basis)
        where

  open is-small-basis sb

  structurally-continuous-if-equiped-with-small-basis : structurally-continuous 𝓓
  structurally-continuous-if-equiped-with-small-basis = record {
    index-of-approximating-family     = ↡ᴮₛ ;
    approximating-family              = ιₛ ;
    approximating-family-is-directed  = ↡ᴮₛ-is-directed ;
    approximating-family-is-way-below = ↡ᴮₛ-way-below ;
    approximating-family-∐-≡          = ↡ᴮₛ-∐-≡
   }

  ⊑-in-terms-of-≪ᴮ : {x y : ⟨ 𝓓 ⟩}
                   → (x ⊑⟨ 𝓓 ⟩ y) ≃ (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
  ⊑-in-terms-of-≪ᴮ {x} {y} =
   logically-equivalent-props-are-equivalent
    (prop-valuedness 𝓓 x y)
    (Π₂-is-prop fe (λ b u → ≪-is-prop-valued 𝓓)) ⦅⇒⦆ ⦅⇐⦆
     where
      ⦅⇒⦆ : x ⊑⟨ 𝓓 ⟩ y → (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y)
      ⦅⇒⦆ x-below-y b b-way-below-x = ≪-⊑-to-≪ 𝓓 b-way-below-x x-below-y
      ⦅⇐⦆ : (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y) → x ⊑⟨ 𝓓 ⟩ y
      ⦅⇐⦆ h = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
              (↡ᴮ-is-sup x) y
              (λ (b , b-way-below-x) → ≪-to-⊑ 𝓓 (h b b-way-below-x))

  locally-small-if-small-basis : is-locally-small 𝓓
  locally-small-if-small-basis =
   ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
    where
     γ : is-locally-small' 𝓓
     γ x y = (∀ (b : B) → b ≪ᴮₛ x → b ≪ᴮₛ y) , e
      where
       e = (∀ (b : B) → b ≪ᴮₛ x → b ≪ᴮₛ y)             ≃⟨ I   ⟩
           (∀ (b : B) → b ≪ᴮₛ x → β b ≪⟨ 𝓓 ⟩ y)       ≃⟨ II  ⟩
           (∀ (b : B) → β b ≪⟨ 𝓓 ⟩ x → β b ≪⟨ 𝓓 ⟩ y) ≃⟨ III ⟩
           x ⊑⟨ 𝓓 ⟩ y                                ■
        where
         I   = Π-cong fe fe B _ _ (λ b →
                →cong fe fe (≃-refl (b ≪ᴮₛ x)) ≪ᴮₛ-≃-≪ᴮ)
         II  = Π-cong fe fe B _ _ (λ b →
                →cong fe fe ≪ᴮₛ-≃-≪ᴮ (≃-refl (β b ≪⟨ 𝓓 ⟩ y)))
         III = ≃-sym (⊑-in-terms-of-≪ᴮ)


  small-basis-nullary-interpolation : (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x
  small-basis-nullary-interpolation x =
   ∥∥-functor id (inhabited-if-Directed 𝓓 (ι x) (↡ᴮ-is-directed x))

  small-basis-nullary-interpolationₛ : (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , b ≪ᴮₛ x
  small-basis-nullary-interpolationₛ x =
   ∥∥-functor (λ (b , u) → b , (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ u))
             (small-basis-nullary-interpolation x)

  small-basis-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                                  → ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
  small-basis-unary-interpolation {x} {y} x-way-below-y = goal
   where
    I : 𝓥 ̇
    I = Σ b ꞉ B , Σ c ꞉ B , (b ≪ᴮₛ β c) × (c ≪ᴮₛ y)
    π : I → ⟨ 𝓓 ⟩
    π (b , _ , _ , _) = β b
    I-inhabited : ∥ I ∥
    I-inhabited = ∥∥-rec ∥∥-is-prop h (small-basis-nullary-interpolationₛ y)
     where
      h : (Σ c ꞉ B , c ≪ᴮₛ y) → ∥ I ∥
      h (c , c-way-below-y) =
       ∥∥-functor k (small-basis-nullary-interpolationₛ (β c))
        where
         k : (Σ b ꞉ B , b ≪ᴮₛ β c) → I
         k (b , b-way-below-c) = (b , c , b-way-below-c , c-way-below-y)
    δ : is-Directed 𝓓 π
    δ = I-inhabited , σ
     where
      σ : is-semidirected (underlying-order 𝓓) π
      σ (b₁ , c₁ , b₁-way-below-c₁ , c₁-way-below-y)
        (b₂ , c₂ , b₂-way-below-c₂ , c₂-way-below-y) =
       ∥∥-rec ∥∥-is-prop h (semidirected-if-Directed 𝓓 (ιₛ y) (↡ᴮₛ-is-directed y)
                             (c₁ , c₁-way-below-y)
                             (c₂ , c₂-way-below-y))
        where
         h : (Σ j ꞉ ↡ᴮₛ y , (β c₁ ⊑⟨ 𝓓 ⟩ β (pr₁ j)) × (β c₂ ⊑⟨ 𝓓 ⟩ β (pr₁ j)))
           → ∃ i ꞉ I , (β b₁ ⊑⟨ 𝓓 ⟩ π i) × (β b₂ ⊑⟨ 𝓓 ⟩ π i)
         h ((c , c-way-below-y) , c₁-below-c , c₂-below-c) =
          ∥∥-functor k
           (semidirected-if-Directed 𝓓 (ιₛ (β c)) (↡ᴮₛ-is-directed (β c))
             (b₁ , ⌜ φ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ φ ⌝ b₁-way-below-c₁) c₁-below-c))
             (b₂ , ⌜ φ ⌝⁻¹ (≪-⊑-to-≪ 𝓓 (⌜ φ ⌝ b₂-way-below-c₂) c₂-below-c)))
           where
            φ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
            φ = ≪ᴮₛ-≃-≪ᴮ
            k : Σ j ꞉ ↡ᴮₛ (β c) , (β b₁ ⊑⟨ 𝓓 ⟩ β (pr₁ j))
                                × (β b₂ ⊑⟨ 𝓓 ⟩ β (pr₁ j))
              → Σ i ꞉ I , (β b₁ ⊑⟨ 𝓓 ⟩ π i) × (β b₂ ⊑⟨ 𝓓 ⟩ π i)
            k ((b , b-way-below-c) , b₁-below-b , b₂-below-b) =
             ((b , c , b-way-below-c , c-way-below-y) , (b₁-below-b , b₂-below-b))
    y-below-sup-of-π : y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
    y-below-sup-of-π = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                        (↡ᴮ-is-sup y) (∐ 𝓓 δ)
                        (λ (c , c-way-below-y) →
                          sup-is-lowerbound-of-upperbounds (underlying-order 𝓓)
                           (↡ᴮ-is-sup (β c)) (∐ 𝓓 δ)
                            (λ (b , b-way-below-c) →
                              ∐-is-upperbound 𝓓 δ
                               (b , c , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ b-way-below-c
                                      , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹ c-way-below-y)))

    claim : ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ π i
    claim = x-way-below-y I π δ y-below-sup-of-π

    goal : ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
    goal = ∥∥-functor γ claim
     where
      γ : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ π i)
        → Σ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
      γ ((b , c , b-way-below-c , c-way-below-y) , x-below-b) =
       (c , (⊑-≪-to-≪ 𝓓 x-below-b (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-c))
          , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-way-below-y)

  -- TODO: Explain use of do-notation
  small-basis-binary-interpolation : {x y z : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
                                   → ∃ b ꞉ B , (x   ≪⟨ 𝓓 ⟩ β b)
                                             × (y   ≪⟨ 𝓓 ⟩ β b)
                                             × (β b ≪⟨ 𝓓 ⟩ z  )
  small-basis-binary-interpolation {x} {y} {z} x-way-below-z y-way-below-z = do
   let δ = ↡ᴮₛ-is-directed z
   let l = ↡ᴮₛ-∐-⊒ z
   (b₁ , x-way-below-b₁ , b₁-way-below-z) ← small-basis-unary-interpolation
                                             x-way-below-z
   (b₂ , y-way-below-b₂ , b₂-way-below-z) ← small-basis-unary-interpolation
                                             y-way-below-z

   ((c₁ , c₁-way-below-z) , b₁-below-c₁)  ← b₁-way-below-z (↡ᴮₛ z) (ιₛ z) δ l
   ((c₂ , c₂-way-below-z) , b₂-below-c₂)  ← b₂-way-below-z (↡ᴮₛ z) (ιₛ z) δ l

   ((c  , c-way-below-z ) , c₁-below-c
                          , c₂-below-c)   ← semidirected-if-Directed 𝓓 (ιₛ z) δ
                                             (c₁ , c₁-way-below-z)
                                             (c₂ , c₂-way-below-z)
   let b₁-below-c = β b₁ ⊑⟨ 𝓓 ⟩[ b₁-below-c₁ ]
                    β c₁ ⊑⟨ 𝓓 ⟩[ c₁-below-c ]
                    β c  ∎⟨ 𝓓 ⟩
   let b₂-below-c = β b₂ ⊑⟨ 𝓓 ⟩[ b₂-below-c₂ ]
                    β c₂ ⊑⟨ 𝓓 ⟩[ c₂-below-c ]
                    β c  ∎⟨ 𝓓 ⟩
   ∣ c , ≪-⊑-to-≪ 𝓓 x-way-below-b₁ b₁-below-c
       , (≪-⊑-to-≪ 𝓓 y-way-below-b₂ b₂-below-c)
       , ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ c-way-below-z ∣




 is-small-basis-Σ : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-small-basis-Σ = (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x))
                                × is-Directed 𝓓 (ι x)
                                × is-sup (underlying-order 𝓓) x (ι x)

 being-small-basis-Σ-is-prop : is-prop is-small-basis-Σ
 being-small-basis-Σ-is-prop =
  Π-is-prop fe (λ x →
   ×₃-is-prop (Π-is-prop fe
               (λ b → prop-has-size-is-prop (λ _ → pe) (λ _ _ → fe)
                       (β b ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓) 𝓥))
              (being-directed-is-prop (underlying-order 𝓓) (ι x))
              (is-sup-is-prop (underlying-order 𝓓) (axioms-of-dcpo 𝓓) x (ι x)))

 is-small-basis-≃ : is-small-basis ≃ is-small-basis-Σ
 is-small-basis-≃ = qinveq f (g , ρ , σ)
  where
   f : is-small-basis → is-small-basis-Σ
   f sb x = (≪ᴮ-is-small x , ↡ᴮ-is-directed x , ↡ᴮ-is-sup x)
    where
     open is-small-basis sb
   g : is-small-basis-Σ → is-small-basis
   g sb = record {
     ≪ᴮ-is-small = λ x → pr₁ (sb x);
     ↡ᴮ-is-directed = λ x → pr₁ (pr₂ (sb x));
     ↡ᴮ-is-sup  = λ x → pr₂ (pr₂ (sb x))
    }
   ρ : g ∘ f ∼ id
   ρ _ = refl
   σ : f ∘ g ∼ id
   σ _ = refl

 being-small-basis-is-prop : is-prop is-small-basis
 being-small-basis-is-prop = equiv-to-prop is-small-basis-≃
                              being-small-basis-Σ-is-prop




module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 has-specified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-basis = Σ B ꞉ 𝓥 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-basis 𝓓 β

 has-unspecified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-basis = ∥ has-specified-small-basis ∥

 structurally-continuous-if-specified-small-basis : has-specified-small-basis
                                                  → structurally-continuous 𝓓
 structurally-continuous-if-specified-small-basis (B , β , sb) =
  structurally-continuous-if-equiped-with-small-basis 𝓓 β sb

 is-continuous-dcpo-if-unspecified-small-basis : has-unspecified-small-basis
                                               → is-continuous-dcpo 𝓓
 is-continuous-dcpo-if-unspecified-small-basis =
  ∥∥-functor structurally-continuous-if-specified-small-basis



\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↓ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓣 ̇
 ↓ᴮ x = Σ b ꞉ B , β b ⊑⟨ 𝓓 ⟩ x

 ↓ι : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x → ⟨ 𝓓 ⟩
 ↓ι x = β ∘ pr₁

 record is-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   basis-is-compact : (b : B) → is-compact 𝓓 (β b)
   ⊑ᴮ-is-small : (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ⊑⟨ 𝓓 ⟩ x))
   ↓ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ι x)
   ↓ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↓ι x)

  _⊑ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ⊑ᴮₛ x = pr₁ (⊑ᴮ-is-small x b)

  ⊑ᴮₛ-≃-⊑ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ⊑ᴮₛ x) ≃ (β b ⊑⟨ 𝓓 ⟩ x)
  ⊑ᴮₛ-≃-⊑ᴮ {b} {x} = pr₂ (⊑ᴮ-is-small x b)

  ↓ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↓ᴮₛ x = Σ b ꞉ B , (b ⊑ᴮₛ x)

  ↓ιₛ : (x : ⟨ 𝓓 ⟩) → ↓ᴮₛ x → ⟨ 𝓓 ⟩
  ↓ιₛ x = β ∘ pr₁

  ↓ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ιₛ x)
  ↓ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ⊑ᴮₛ-≃-⊑ᴮ)) (↓ι x) (↓ᴮ-is-directed x)

  ↓ᴮₛ-∐-≡ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↓ᴮₛ-is-directed x) ≡ x
  ↓ᴮₛ-∐-≡ x = antisymmetry 𝓓 (∐ 𝓓 (↓ᴮₛ-is-directed x)) x ⦅1⦆ ⦅2⦆
   where
    ⦅1⦆ : ∐ 𝓓 (↓ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
    ⦅1⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 (↓ᴮₛ-is-directed x) x
          (λ (b , u) → sup-is-upperbound (underlying-order 𝓓) (↓ᴮ-is-sup x)
                        (b , (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u)))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↓ᴮ-is-sup x)
          (∐ 𝓓 (↓ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↓ᴮₛ-is-directed x)
                        (b , (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝⁻¹ v)))

  ↓ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↓ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↓ᴮₛ-∐-⊑ x = ≡-to-⊑ 𝓓 (↓ᴮₛ-∐-≡ x)

  ↓ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↓ᴮₛ-is-directed x)
  ↓ᴮₛ-∐-⊒ x = ≡-to-⊑ 𝓓 ((↓ᴮₛ-∐-≡ x) ⁻¹)

  ↓ᴮₛ-way-below : (x : ⟨ 𝓓 ⟩) (b : ↓ᴮₛ x) → ↓ιₛ x b ⊑⟨ 𝓓 ⟩ x
  ↓ᴮₛ-way-below x (b , u) = ⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ u

 compact-basis-is-basis : is-small-compact-basis
                        → is-small-basis 𝓓 β
 compact-basis-is-basis scb = record {
   ≪ᴮ-is-small    = λ x b → ( b ⊑ᴮₛ x
                            , ((b ⊑ᴮₛ x)      ≃⟨ ⊑ᴮₛ-≃-⊑ᴮ ⟩
                               (β b ⊑⟨ 𝓓 ⟩ x) ≃⟨ lemma b  ⟩
                               (β b ≪⟨ 𝓓 ⟩ x) ■));
   ↡ᴮ-is-directed = λ x → reindexed-family-is-directed 𝓓
                           (↓ᴮ-≃-↡ᴮ x) (↓ι x) (↓ᴮ-is-directed x);
   ↡ᴮ-is-sup      = λ x → reindexed-family-sup 𝓓 (↓ᴮ-≃-↡ᴮ x) (↓ι x)
                           x (↓ᴮ-is-sup x)
  }
   where
    open is-small-compact-basis scb
    lemma : (b : B) {x : ⟨ 𝓓 ⟩} → (β b ⊑⟨ 𝓓 ⟩ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
    lemma b = compact-⊑-≃-≪ 𝓓 (basis-is-compact b)
    ↓ᴮ-≃-↡ᴮ : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x ≃ ↡ᴮ 𝓓 β x
    ↓ᴮ-≃-↡ᴮ x = Σ-cong (λ b → lemma b)









{-
module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 record structural-basis {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇  where
  field
   index-of-approximating-family : ⟨ 𝓓 ⟩ → 𝓥 ̇
   approximating-family : (x : ⟨ 𝓓 ⟩)
                        → (index-of-approximating-family x) → B
   approximating-family-is-directed : (x : ⟨ 𝓓 ⟩)
                                    → is-Directed 𝓓 (β ∘ approximating-family x)
   approximating-family-is-way-below : (x : ⟨ 𝓓 ⟩)
                                     → is-way-upperbound 𝓓 x
                                        (β ∘ approximating-family x)
   approximating-family-∐-≡ : (x : ⟨ 𝓓 ⟩)
                            → ∐ 𝓓 (approximating-family-is-directed x) ≡ x

 {-
 structural-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩)
                  → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
 structural-basis 𝓓 {B} β =
   (x : ⟨ 𝓓 ⟩) → Σ I ꞉ 𝓥 ̇  ,
                 Σ α ꞉ (I → B) , ((i : I) → β (α i) ≪⟨ 𝓓 ⟩ x)
                               × (Σ δ ꞉ is-Directed 𝓓 (β ∘ α) , ∐ 𝓓 δ ≡ x)
 -}

 is-basis : {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
 is-basis β = ∥ structural-basis β ∥

 {-
 has-specified-structural-basis : (𝓓 : DCPO {𝓤} {𝓣})
                                → 𝓥 ⁺ ⊔ 𝓤 ⁺ ⊔ 𝓣 ̇
 has-specified-structural-basis {𝓤} {𝓣} 𝓓 =
   Σ B ꞉ 𝓤 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , structural-basis 𝓓 β
 -}

 structurally-continuous-if-specified-structural-basis :
   {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩)
   → structural-basis β
   → structurally-continuous 𝓓
 structurally-continuous-if-specified-structural-basis β str-basis =
  record
    { index-of-approximating-family = index-of-approximating-family
    ; approximating-family = λ x → β ∘ approximating-family x
    ; approximating-family-is-directed = approximating-family-is-directed
    ; approximating-family-is-way-below = approximating-family-is-way-below
    ; approximating-family-∐-≡ = approximating-family-∐-≡
    }
    where
     open structural-basis str-basis

 specified-structural-basis-if-structurally-continuous :
   structurally-continuous 𝓓 → structural-basis id
 specified-structural-basis-if-structurally-continuous C =
  record
    { index-of-approximating-family = index-of-approximating-family
    ; approximating-family = approximating-family
    ; approximating-family-is-directed = approximating-family-is-directed
    ; approximating-family-is-way-below = approximating-family-is-way-below
    ; approximating-family-∐-≡ = approximating-family-∐-≡
    }
    where
     open structurally-continuous C

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓓-is-locally-small : is-locally-small 𝓓)
       where

 has-specified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-basis = Σ B ꞉ 𝓥 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-basis 𝓓 β

 has-unspecified-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-basis = ∥ has-specified-small-basis ∥

 generates-dcpo-str : {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩)
                    → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
 generates-dcpo-str {𝓦} {B} β = (x : ⟨ 𝓓 ⟩) → Σ I ꞉ 𝓥 ̇  , Σ α ꞉ (I → B) ,
                                              Σ δ ꞉ is-Directed 𝓓 (β ∘ α) ,
                                                ∐ 𝓓 δ ≡ x

 generates-dcpo : {B : 𝓦 ̇  } (β : B → ⟨ 𝓓 ⟩)
                → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
 generates-dcpo β = ∥ generates-dcpo-str β ∥

 -- TODO: Think of a better name
 has-specified-small-generator : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-generator =
  Σ B ꞉ 𝓥 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , generates-dcpo β

 has-unspecified-small-generator : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-generator =
  ∥ Σ B ꞉ 𝓥 ̇  , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , generates-dcpo β ∥

 module _
         {B : 𝓥 ̇  }
         (β : B → ⟨ 𝓓 ⟩)
        where

  bases-generate : is-basis 𝓓 β → generates-dcpo β
  bases-generate = ∥∥-functor r
   where
    r : structural-basis 𝓓 β → generates-dcpo-str β
    r β-basis-str x = index-of-approximating-family x
                    , approximating-family x
                    , approximating-family-is-directed x
                    , (approximating-family-∐-≡ x)
     where
      open structural-basis β-basis-str

  generators-are-bases-in-continuous-dcpos : is-continuous-dcpo 𝓓
                                           → generates-dcpo β
                                           → is-basis 𝓓 β
  generators-are-bases-in-continuous-dcpos c = ∥∥-functor r
   where
    r : generates-dcpo-str β → structural-basis 𝓓 β
    r β-gen-str = record {
       index-of-approximating-family = λ x → pr₁ (β-gen-str x)
        where
         Iₓ : 𝓥 ̇
     ; approximating-family = λ x → pr₁ (pr₂ (β-gen-str x))
     ; approximating-family-is-directed = λ x → pr₁ (pr₂ (pr₂ (β-gen-str x)))
     ; approximating-family-is-way-below = λ x → {!!}
     ; approximating-family-∐-≡ = λ x → pr₂ (pr₂ (pr₂ (β-gen-str x)))
     }
-}

\end{code}
