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
        (fe : Fun-Ext)
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

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
       where

 ↡ᴮ : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ↡ᴮ x = Σ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x

 ↡ι : (x : ⟨ 𝓓 ⟩) → ↡ᴮ x → ⟨ 𝓓 ⟩
 ↡ι x = β ∘ pr₁

 record is-small-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇  where
  field
   ≪ᴮ-is-small : (x : ⟨ 𝓓 ⟩) → ((b : B) → is-small (β b ≪⟨ 𝓓 ⟩ x))
   ↡ᴮ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡ι x)
   ↡ᴮ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↡ι x)

  _≪ᴮₛ_ : (b : B) (x : ⟨ 𝓓 ⟩) → 𝓥 ̇
  b ≪ᴮₛ x = pr₁ (≪ᴮ-is-small x b)

  ≪ᴮₛ-≃-≪ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
  ≪ᴮₛ-≃-≪ᴮ {b} {x} = pr₂ (≪ᴮ-is-small x b)

  ≪ᴮₛ-is-prop-valued : {b : B} {x : ⟨ 𝓓 ⟩} → is-prop (b ≪ᴮₛ x)
  ≪ᴮₛ-is-prop-valued = equiv-to-prop ≪ᴮₛ-≃-≪ᴮ (≪-is-prop-valued 𝓓)

  ↡ᴮₛ : ⟨ 𝓓 ⟩ → 𝓥 ̇
  ↡ᴮₛ x = Σ b ꞉ B , (b ≪ᴮₛ x)

  ↡ιₛ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ x → ⟨ 𝓓 ⟩
  ↡ιₛ x = β ∘ pr₁

  ↡ᴮₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡ιₛ x)
  ↡ᴮₛ-is-directed x = reindexed-family-is-directed 𝓓
                       (Σ-cong (λ b → ≃-sym ≪ᴮₛ-≃-≪ᴮ)) (↡ι x) (↡ᴮ-is-directed x)

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
  ↡ᴮₛ-∐-⊒ x = ≡-to-⊒ 𝓓 (↡ᴮₛ-∐-≡ x)

  ↡ᴮₛ-way-below : (x : ⟨ 𝓓 ⟩) (b : ↡ᴮₛ x) → ↡ιₛ x b ≪⟨ 𝓓 ⟩ x
  ↡ᴮₛ-way-below x (b , u) = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ u



 module _
         (sb : is-small-basis)
        where

  open is-small-basis sb

  structurally-continuous-if-equiped-with-small-basis : structurally-continuous 𝓓
  structurally-continuous-if-equiped-with-small-basis = record {
    index-of-approximating-family     = ↡ᴮₛ ;
    approximating-family              = ↡ιₛ ;
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
   ∥∥-functor id (inhabited-if-Directed 𝓓 (↡ι x) (↡ᴮ-is-directed x))

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
       ∥∥-rec ∥∥-is-prop h (semidirected-if-Directed 𝓓 (↡ιₛ y) (↡ᴮₛ-is-directed y)
                             (c₁ , c₁-way-below-y)
                             (c₂ , c₂-way-below-y))
        where
         h : (Σ j ꞉ ↡ᴮₛ y , (β c₁ ⊑⟨ 𝓓 ⟩ β (pr₁ j)) × (β c₂ ⊑⟨ 𝓓 ⟩ β (pr₁ j)))
           → ∃ i ꞉ I , (β b₁ ⊑⟨ 𝓓 ⟩ π i) × (β b₂ ⊑⟨ 𝓓 ⟩ π i)
         h ((c , c-way-below-y) , c₁-below-c , c₂-below-c) =
          ∥∥-functor k
           (semidirected-if-Directed 𝓓 (↡ιₛ (β c)) (↡ᴮₛ-is-directed (β c))
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

   ((c₁ , c₁-way-below-z) , b₁-below-c₁)  ← b₁-way-below-z (↡ᴮₛ z) (↡ιₛ z) δ l
   ((c₂ , c₂-way-below-z) , b₂-below-c₂)  ← b₂-way-below-z (↡ᴮₛ z) (↡ιₛ z) δ l

   ((c  , c-way-below-z ) , c₁-below-c
                          , c₂-below-c)   ← semidirected-if-Directed 𝓓 (↡ιₛ z) δ
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
                                × is-Directed 𝓓 (↡ι x)
                                × is-sup (underlying-order 𝓓) x (↡ι x)

 being-small-basis-Σ-is-prop : Prop-Ext → is-prop is-small-basis-Σ
 being-small-basis-Σ-is-prop pe =
  Π-is-prop fe (λ x →
   ×₃-is-prop (Π-is-prop fe
               (λ b → prop-being-small-is-prop (λ _ → pe) (λ _ _ → fe)
                       (β b ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓) 𝓥))
              (being-directed-is-prop (underlying-order 𝓓) (↡ι x))
              (is-sup-is-prop (underlying-order 𝓓) (pr₁ (axioms-of-dcpo 𝓓))
                              x (↡ι x)))

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

 being-small-basis-is-prop : Prop-Ext → is-prop is-small-basis
 being-small-basis-is-prop pe = equiv-to-prop is-small-basis-≃
                                 (being-small-basis-Σ-is-prop pe)




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
  ↓ᴮₛ-∐-⊒ x = ≡-to-⊒ 𝓓 (↓ᴮₛ-∐-≡ x)

  ↓ᴮₛ-compact : (x : ⟨ 𝓓 ⟩) (b : ↓ᴮₛ x) → is-compact 𝓓 (↓ιₛ x b)
  ↓ᴮₛ-compact x (b , u) = basis-is-compact b

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

\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 structurally-algebraic-if-equiped-with-small-compact-basis :
    {B : 𝓥 ̇  } (β : B → ⟨ 𝓓 ⟩)
  → is-small-compact-basis 𝓓 β
  → structurally-algebraic 𝓓
 structurally-algebraic-if-equiped-with-small-compact-basis β scb = record {
   index-of-compact-family    = ↓ᴮₛ;
   compact-family             = ↓ιₛ;
   compact-family-is-directed = ↓ᴮₛ-is-directed;
   compact-family-is-compact  = ↓ᴮₛ-compact;
   compact-family-∐-≡         = ↓ᴮₛ-∐-≡
  }
   where
    open is-small-compact-basis scb

 has-specified-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-specified-small-compact-basis =
  Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-small-compact-basis 𝓓 β

 has-unspecified-small-compact-basis : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 has-unspecified-small-compact-basis = ∥ has-specified-small-compact-basis ∥

 structurally-algebraic-if-specified-small-compact-basis :
    has-specified-small-compact-basis
  → structurally-algebraic 𝓓
 structurally-algebraic-if-specified-small-compact-basis (B , β , sb) =
  structurally-algebraic-if-equiped-with-small-compact-basis β sb

 is-algebraic-dcpo-if-unspecified-small-compact-basis :
    has-unspecified-small-compact-basis
  → is-algebraic-dcpo 𝓓
 is-algebraic-dcpo-if-unspecified-small-compact-basis =
  ∥∥-functor structurally-algebraic-if-specified-small-compact-basis

\end{code}

TODO: Write comment

\begin{code}

small-and-compact-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇  } (β : B → ⟨ 𝓓 ⟩)
                        → is-small-basis 𝓓 β
                        → ((b : B) → is-compact 𝓓 (β b))
                        → is-small-compact-basis 𝓓 β
small-and-compact-basis 𝓓 {B} β β-is-small-basis κ = record {
   basis-is-compact = κ
  ; ⊑ᴮ-is-small     = I
  ; ↓ᴮ-is-directed  = II
  ; ↓ᴮ-is-sup       = III
 }
  where
   open is-small-basis β-is-small-basis
   module _
           (x : ⟨ 𝓓 ⟩)
          where
    ↡-and-↓-coincide : ↡ᴮ 𝓓 β x ≃ ↓ᴮ 𝓓 β x
    ↡-and-↓-coincide = Σ-cong (λ b → ≃-sym (compact-⊑-≃-≪ 𝓓 (κ b)))
    I : (b : B) → is-small (β b ⊑⟨ 𝓓 ⟩ x)
    I b = ⌜ local-smallness-equivalent-definitions 𝓓 ⌝
           (locally-small-if-small-basis 𝓓 β β-is-small-basis)
           (β b) x
    II : is-Directed 𝓓 (↓ι 𝓓 β x)
    II = reindexed-family-is-directed 𝓓 ↡-and-↓-coincide (↡ι 𝓓 β x)
          (↡ᴮ-is-directed x)
    III : is-sup (underlying-order 𝓓) x (↓ι 𝓓 β x)
    III = reindexed-family-sup 𝓓 ↡-and-↓-coincide (↡ι 𝓓 β x) x (↡ᴮ-is-sup x)


\end{code}

TODO: Move this somewhere and explain
       (ref. Abramsky-Jung, compendium, subset of basis...)

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (x : ⟨ 𝓓 ⟩)
        {I : 𝓥 ̇  }
        (σ : I → ↡ᴮ 𝓓 β x)
       where

 ↡ᴮ-sup-criterion : is-sup (underlying-order 𝓓) x (↡ι 𝓓 β x ∘ σ)
                  → is-sup (underlying-order 𝓓) x (↡ι 𝓓 β x)
 ↡ᴮ-sup-criterion x-is-sup = (ub , lb-of-ubs)
  where
   ub : is-upperbound (underlying-order 𝓓) x (↡ι 𝓓 β x)
   ub (b , b-way-below-x) = ≪-to-⊑ 𝓓 b-way-below-x
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x (↡ι 𝓓 β x)
   lb-of-ubs y y-is-ub =
    sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) x-is-sup y y-is-ub'
     where
      y-is-ub' : is-upperbound (underlying-order 𝓓) y (↡ι 𝓓 β x ∘ σ)
      y-is-ub' i = y-is-ub (σ i)

 ↡ᴮ-directedness-criterion : (δ : is-Directed 𝓓 (↡ι 𝓓 β x ∘ σ))
                           → (x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ)
                           → is-Directed 𝓓 (↡ι 𝓓 β x)
 ↡ᴮ-directedness-criterion δ@(inh , semidir) x-below-∐ = (inh' , semidir')
  where
   inh' : ∥ ↡ᴮ 𝓓 β x ∥
   inh' = ∥∥-functor σ inh
   semidir' : is-semidirected (underlying-order 𝓓) (↡ι 𝓓 β x)
   semidir' (b₁ , b₁-way-below-x) (b₂ , b₂-way-below-x) =
    ∥∥-rec₂ ∃-is-prop f (b₁-way-below-x I (↡ι 𝓓 β x ∘ σ) δ x-below-∐)
                       (b₂-way-below-x I (↡ι 𝓓 β x ∘ σ) δ x-below-∐)
     where
      f : (Σ i ꞉ I , β b₁ ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x (σ i))
        → (Σ i ꞉ I , β b₂ ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x (σ i))
        → (∃ b ꞉ ↡ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x b)
                          × (β b₂ ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x b))
      f (i₁ , u₁) (i₂ , u₂) = ∥∥-functor g (semidir i₁ i₂)
       where
        g : (Σ i ꞉ I , (↡ι 𝓓 β x (σ i₁) ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x (σ i))
                     × (↡ι 𝓓 β x (σ i₂) ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x (σ i)))
          → (Σ b ꞉ ↡ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x b)
                            × (β b₂ ⊑⟨ 𝓓 ⟩ ↡ι 𝓓 β x b))
        g (i , v₁ , v₂) = (σ i
                        , (β b₁            ⊑⟨ 𝓓 ⟩[ u₁ ]
                           ↡ι 𝓓 β x (σ i₁) ⊑⟨ 𝓓 ⟩[ v₁ ]
                           ↡ι 𝓓 β x (σ i)  ∎⟨ 𝓓 ⟩)
                        , (β b₂            ⊑⟨ 𝓓 ⟩[ u₂ ]
                           ↡ι 𝓓 β x (σ i₂) ⊑⟨ 𝓓 ⟩[ v₂ ]
                           ↡ι 𝓓 β x (σ i)  ∎⟨ 𝓓 ⟩))

\end{code}

TODO: Move to DcpoContinuous?

\begin{code}

record _continuous-retract-of_
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'}) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇  where
  field
   s : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   r : ⟨ 𝓔 ⟩ → ⟨ 𝓓 ⟩
   r-s-equation : r ∘ s ∼ id
   s-is-continuous : is-continuous 𝓓 𝓔 s
   r-is-continuous : is-continuous 𝓔 𝓓 r

  𝕤 : DCPO[ 𝓓 , 𝓔 ]
  𝕤 = s , s-is-continuous

  𝕣 : DCPO[ 𝓔 , 𝓓 ]
  𝕣 = r , r-is-continuous

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
          ⦅2⦆ = ≡-to-⊑ 𝓓 (r-s-equation (β j))
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
     ⦅3⦆ = r-s-equation x

 continuity-of-dcpo-preserved-by-continuous-retract : is-continuous-dcpo 𝓔
                                                    → is-continuous-dcpo 𝓓
 continuity-of-dcpo-preserved-by-continuous-retract =
  ∥∥-functor structural-continuity-of-dcpo-preserved-by-continuous-retract

\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

 continuous-retraction-≪-criterion : (y : ⟨ 𝓔 ⟩) (x : ⟨ 𝓓 ⟩)
                                   → y ≪⟨ 𝓔 ⟩ s x
                                   → r y ≪⟨ 𝓓 ⟩ x
 continuous-retraction-≪-criterion y x y-way-below-sx I α δ x-below-∐α =
  ∥∥-functor h (y-way-below-sx I (s ∘ α) ε l)
   where
    ε : is-Directed 𝓔 (s ∘ α)
    ε = image-is-directed' 𝓓 𝓔 𝕤 δ
    l : s x ⊑⟨ 𝓔 ⟩ ∐ 𝓔 ε
    l = s x       ⊑⟨ 𝓔 ⟩[ monotone-if-continuous 𝓓 𝓔 𝕤 x (∐ 𝓓 δ) x-below-∐α ]
        s (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ continuous-∐-⊑ 𝓓 𝓔 𝕤 δ ]
        ∐ 𝓔 ε     ∎⟨ 𝓔 ⟩
    h : (Σ i ꞉ I , y ⊑⟨ 𝓔 ⟩ s (α i))
      → (Σ i ꞉ I , r y ⊑⟨ 𝓓 ⟩ α i)
    h (i , u) = (i , v)
     where
      v = r y         ⊑⟨ 𝓓 ⟩[ monotone-if-continuous 𝓔 𝓓 𝕣 y (s (α i)) u ]
          r (s (α i)) ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (r-s-equation (α i)) ]
          α i         ∎⟨ 𝓓 ⟩

 local-smallness-preserved-by-continuous-retract : is-locally-small 𝓔
                                                 → is-locally-small 𝓓
 local-smallness-preserved-by-continuous-retract ls =
  ⌜ local-smallness-equivalent-definitions 𝓓 ⌝⁻¹ γ
   where
    open is-locally-small ls
    γ : is-locally-small' 𝓓
    γ x y = (s x ⊑ₛ s y , g)
     where
      g : (s x ⊑ₛ s y) ≃ (x ⊑⟨ 𝓓 ⟩ y)
      g = logically-equivalent-props-are-equivalent
           (equiv-to-prop ⊑ₛ-≃-⊑ -- (f (s x) (s y))
             (prop-valuedness 𝓔 (s x) (s y)))
           (prop-valuedness 𝓓 x y)
           ⦅⇒⦆ ⦅⇐⦆
       where
        ⦅⇒⦆ : (s x ⊑ₛ s y) → (x ⊑⟨ 𝓓 ⟩ y)
        ⦅⇒⦆ l = x      ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               r (s x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               r (s y) ⊑⟨ 𝓓 ⟩[ ⦅3⦆ ]
               y       ∎⟨ 𝓓 ⟩
         where
          ⦅1⦆ = ≡-to-⊒ 𝓓 (r-s-equation x)
          ⦅2⦆ = monotone-if-continuous 𝓔 𝓓 𝕣 (s x) (s y) (⊑ₛ-to-⊑ l)
          ⦅3⦆ = ≡-to-⊑ 𝓓 (r-s-equation y)
        ⦅⇐⦆ : (x ⊑⟨ 𝓓 ⟩ y) → (s x ⊑ₛ s y)
        ⦅⇐⦆ l = ⊑-to-⊑ₛ (monotone-if-continuous 𝓓 𝓔 𝕤 x y l)

 small-basis-from-continuous-retract : Prop-Ext → {B : 𝓥 ̇  } (β : B → ⟨ 𝓔 ⟩)
                                     → is-small-basis 𝓔 β
                                     → is-small-basis 𝓓 (r ∘ β)
 small-basis-from-continuous-retract pe {B} β sb =
  record
    { ≪ᴮ-is-small    = lemma₁
    ; ↡ᴮ-is-directed = lemma₂
    ; ↡ᴮ-is-sup      = lemma₃
    }
     where
      open is-small-basis sb

      lemma₁ : (x : ⟨ 𝓓 ⟩) (b : B) → is-small (r (β b) ≪⟨ 𝓓 ⟩ x)
      lemma₁ x b = ≪-is-small-valued 𝓓 pe 𝓓-cont 𝓓-loc-small (r (β b)) x
       where
        𝓓-loc-small : is-locally-small 𝓓
        𝓓-loc-small = (local-smallness-preserved-by-continuous-retract
                        (locally-small-if-small-basis 𝓔 β sb))
        𝓓-cont : is-continuous-dcpo 𝓓
        𝓓-cont = continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ
                  ∣ structurally-continuous-if-specified-small-basis
                     𝓔 (B , (β , sb)) ∣

      σ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ (s x) → ↡ᴮ 𝓓 (r ∘ β) x
      σ x (b , b-way-below-sx) =
       (b , continuous-retraction-≪-criterion (β b) x
             (⌜ ≪ᴮₛ-≃-≪ᴮ ⌝ b-way-below-sx))

      ε : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓔 (↡ιₛ (s x))
      ε x = ↡ᴮₛ-is-directed (s x)

      eq-lemma : (x : ⟨ 𝓓 ⟩) → r (∐ 𝓔 (ε x)) ≡ x
      eq-lemma x = r (∐ 𝓔 (ε x)) ≡⟨ ap r (↡ᴮₛ-∐-≡ (s x)) ⟩
                   r (s x)       ≡⟨ r-s-equation x       ⟩
                   x             ∎

      lemma₂ : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↡ι 𝓓 (r ∘ β) x)
      lemma₂ x = ↡ᴮ-directedness-criterion 𝓓 (r ∘ β) x (σ x) ε' h
       where
        ε' : is-Directed 𝓓 (r ∘ ↡ιₛ (s x))
        ε' = image-is-directed' 𝓔 𝓓 𝕣 (ε x)
        h : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε'
        h = transport (λ - → - ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε') (eq-lemma x) claim
         where
          claim : r (∐ 𝓔 (ε x)) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε'
          claim = continuous-∐-⊑ 𝓔 𝓓 𝕣 (ε x)

      lemma₃ : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↡ι 𝓓 (r ∘ β) x)
      lemma₃ x = ↡ᴮ-sup-criterion 𝓓 (r ∘ β) x (σ x) h
       where
        h : is-sup (underlying-order 𝓓) x (r ∘ ↡ιₛ (s x))
        h = transport (λ - → is-sup (underlying-order 𝓓) - (r ∘ ↡ιₛ (s x)))
             (eq-lemma x) claim
         where
          claim : is-sup (underlying-order 𝓓) (r (∐ 𝓔 (ε x))) (r ∘ ↡ιₛ (s x))
          claim = r-is-continuous (↡ᴮₛ (s x)) (↡ιₛ (s x)) (ε x)

\end{code}

TODO: Write some more...
Criterion for locally small exponentials

\begin{code}

open import DcpoExponential pt fe 𝓥

locally-small-exponential-criterion : Prop-Ext
                                    → (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                                    → has-unspecified-small-basis 𝓓
                                    → is-locally-small 𝓔
                                    → is-locally-small (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) -- TODO: Change ⟹?
locally-small-exponential-criterion pe 𝓓 𝓔 𝓓-sb ls =
 ∥∥-rec (being-locally-small-is-prop (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) (λ _ → pe)) lemma 𝓓-sb
  where
   open is-locally-small ls
   lemma : has-specified-small-basis 𝓓 → is-locally-small (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
   lemma (B , β , β-is-small-basis) =
    ⌜ local-smallness-equivalent-definitions (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ⌝⁻¹ γ
     where
      open is-small-basis β-is-small-basis
      γ : is-locally-small' (𝓓 ⟹ᵈᶜᵖᵒ 𝓔)
      γ 𝕗@(f , f-cont) 𝕘@(g , g-cont) = (order , claim)
       where
        order : 𝓥 ̇
        order = (b : B) → f (β b) ⊑ₛ g (β b)
        claim : order ≃ ((x : ⟨ 𝓓 ⟩) → f x ⊑⟨ 𝓔 ⟩ g x)
        claim = logically-equivalent-props-are-equivalent
                 (Π-is-prop fe (λ b → equiv-to-prop ⊑ₛ-≃-⊑
                                       (prop-valuedness 𝓔 (f (β b)) (g (β b)))))
                 (Π-is-prop fe (λ x → prop-valuedness 𝓔 (f x) (g x)))
                 ⦅⇒⦆ ⦅⇐⦆
         where
          ⦅⇐⦆ : ((x : ⟨ 𝓓 ⟩) → f x ⊑⟨ 𝓔 ⟩ g x) → order
          ⦅⇐⦆ f-below-g b = ⊑-to-⊑ₛ (f-below-g (β b))
          ⦅⇒⦆ : order → ((x : ⟨ 𝓓 ⟩) → f x ⊑⟨ 𝓔 ⟩ g x)
          ⦅⇒⦆ f-below-g x = transport (λ - → f - ⊑⟨ 𝓔 ⟩ g -)
                             (↡ᴮₛ-∐-≡ x) f-below-g'
           where
            f-below-g' = f (∐ 𝓓 (↡ᴮₛ-is-directed x)) ⊑⟨ 𝓔 ⟩[ ⦅1⦆ ]
                         ∐ 𝓔 εᶠ                      ⊑⟨ 𝓔 ⟩[ ⦅2⦆ ]
                         ∐ 𝓔 εᵍ                      ⊑⟨ 𝓔 ⟩[ ⦅3⦆ ]
                         g (∐ 𝓓 (↡ᴮₛ-is-directed x)) ∎⟨ 𝓔 ⟩
             where
              εᶠ : is-Directed 𝓔 (f ∘ ↡ιₛ x)
              εᶠ = image-is-directed' 𝓓 𝓔 𝕗 (↡ᴮₛ-is-directed x)
              εᵍ : is-Directed 𝓔 (g ∘ ↡ιₛ x)
              εᵍ = image-is-directed' 𝓓 𝓔 𝕘 (↡ᴮₛ-is-directed x)
              ⦅1⦆ = continuous-∐-⊑ 𝓓 𝓔 𝕗 (↡ᴮₛ-is-directed x)
              ⦅3⦆ = continuous-∐-⊒ 𝓓 𝓔 𝕘 (↡ᴮₛ-is-directed x)
              ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓔 εᶠ (∐ 𝓔 εᵍ) ub
               where
                ub : (i : ↡ᴮₛ x) → f (↡ιₛ x i) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 εᵍ
                ub (b , i) = f (β b) ⊑⟨ 𝓔 ⟩[ ⦅†⦆ ]
                             g (β b) ⊑⟨ 𝓔 ⟩[ ⦅‡⦆ ]
                             ∐ 𝓔 εᵍ  ∎⟨ 𝓔 ⟩
                 where
                  ⦅†⦆ = ⊑ₛ-to-⊑ (f-below-g b)
                  ⦅‡⦆ = ∐-is-upperbound 𝓔 εᵍ (b , i)

\end{code}

TODO: Put this somewhere else in this file

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇  }
        (β : B → ⟨ 𝓓 ⟩)
        (β-is-small-compact-basis : is-small-compact-basis 𝓓 β)
       where

 open is-small-compact-basis β-is-small-compact-basis

 small-compact-basis-contains-all-compact-elements : (x : ⟨ 𝓓 ⟩)
                                                   → is-compact 𝓓 x
                                                   → ∃ b ꞉ B , β b ≡ x
 small-compact-basis-contains-all-compact-elements x x-is-compact =
  ∥∥-functor γ (x-is-compact (↓ᴮₛ x) (↓ιₛ x) (↓ᴮₛ-is-directed x) (↓ᴮₛ-∐-⊒ x))
   where
    γ : (Σ (b , b-below-x) ꞉ ↓ᴮₛ x , x ⊑⟨ 𝓓 ⟩ β b)
      → (Σ b ꞉ B , β b ≡ x)
    γ ((b , b-below-x) , x-below-b) = (b , e)
     where
      e : β b ≡ x
      e = antisymmetry 𝓓 (β b) x (⌜ ⊑ᴮₛ-≃-⊑ᴮ ⌝ b-below-x) x-below-b

\end{code}
