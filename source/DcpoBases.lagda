Tom de Jong, early January 2022.

TODO: Describe contents.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

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

open import UF-Base
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

  ≪ᴮₛ-to-≪ᴮ : {b : B} {x : ⟨ 𝓓 ⟩} → (b ≪ᴮₛ x) → (β b ≪⟨ 𝓓 ⟩ x)
  ≪ᴮₛ-to-≪ᴮ = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝

  ≪ᴮ-to-≪ᴮₛ : {b : B} {x : ⟨ 𝓓 ⟩} → (β b ≪⟨ 𝓓 ⟩ x) → (b ≪ᴮₛ x)
  ≪ᴮ-to-≪ᴮₛ = ⌜ ≪ᴮₛ-≃-≪ᴮ ⌝⁻¹

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
                        (b , ≪ᴮₛ-to-≪ᴮ u))
    ⦅2⦆ : x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
    ⦅2⦆ = sup-is-lowerbound-of-upperbounds (underlying-order 𝓓) (↡ᴮ-is-sup x)
          (∐ 𝓓 (↡ᴮₛ-is-directed x))
          (λ (b , v) → ∐-is-upperbound 𝓓 (↡ᴮₛ-is-directed x)
                        (b , ≪ᴮ-to-≪ᴮₛ v))

  ↡ᴮₛ-∐-⊑ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (↡ᴮₛ-is-directed x) ⊑⟨ 𝓓 ⟩ x
  ↡ᴮₛ-∐-⊑ x = ≡-to-⊑ 𝓓 (↡ᴮₛ-∐-≡ x)

  ↡ᴮₛ-∐-⊒ : (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (↡ᴮₛ-is-directed x)
  ↡ᴮₛ-∐-⊒ x = ≡-to-⊒ 𝓓 (↡ᴮₛ-∐-≡ x)

  ↡ᴮₛ-is-way-below : (x : ⟨ 𝓓 ⟩) (b : ↡ᴮₛ x) → ↡ιₛ x b ≪⟨ 𝓓 ⟩ x
  ↡ᴮₛ-is-way-below x (b , u) = ≪ᴮₛ-to-≪ᴮ u



 module _
         (sb : is-small-basis)
        where

  open is-small-basis sb

  structurally-continuous-if-equiped-with-small-basis : structurally-continuous 𝓓
  structurally-continuous-if-equiped-with-small-basis =
   record
    { index-of-approximating-family     = ↡ᴮₛ
    ; approximating-family              = ↡ιₛ
    ; approximating-family-is-directed  = ↡ᴮₛ-is-directed
    ; approximating-family-is-way-below = ↡ᴮₛ-is-way-below
    ; approximating-family-∐-≡          = ↡ᴮₛ-∐-≡
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
   ∥∥-functor (λ (b , u) → b , ≪ᴮ-to-≪ᴮₛ u)
             (small-basis-nullary-interpolation x)

  small-basis-unary-interpolation : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y
                                  → ∃ b ꞉ B , (x ≪⟨ 𝓓 ⟩ β b) × (β b ≪⟨ 𝓓 ⟩ y)
  small-basis-unary-interpolation {x} {y} x-way-below-y =
   ∥∥-rec ∃-is-prop γ (≪-unary-interpolation-str 𝓓 C x-way-below-y)
    where
     C : structurally-continuous 𝓓
     C = structurally-continuous-if-equiped-with-small-basis
     open structurally-continuous C
     γ : (Σ d ꞉ ⟨ 𝓓 ⟩ , x ≪⟨ 𝓓 ⟩ d × d ≪⟨ 𝓓 ⟩ y)
       → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ (β b) × β b ≪⟨ 𝓓 ⟩ y
     γ (d , x-wb-d , d-wb-y) =
      ∥∥-functor σ (d-wb-y (↡ᴮₛ y) (↡ιₛ y) (↡ᴮₛ-is-directed y) (↡ᴮₛ-∐-⊒ y))
       where
        σ : (Σ b ꞉ ↡ᴮₛ y , d ⊑⟨ 𝓓 ⟩ ↡ιₛ y b)
          → Σ b ꞉ B , x ≪⟨ 𝓓 ⟩ (β b) × β b ≪⟨ 𝓓 ⟩ y
        σ ((b , b-wb-y) , d-below-b) =
         b , ≪-⊑-to-≪ 𝓓 x-wb-d d-below-b
           , ≪ᴮₛ-to-≪ᴮ b-wb-y

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
       , ≪-⊑-to-≪ 𝓓 y-way-below-b₂ b₂-below-c
       , ≪ᴮₛ-to-≪ᴮ c-way-below-z ∣



{-
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
 is-small-basis-≃ = qinveq f (g , (λ _ → refl) , (λ _ → refl))
  where
   f : is-small-basis → is-small-basis-Σ
   f sb x = (≪ᴮ-is-small x , ↡ᴮ-is-directed x , ↡ᴮ-is-sup x)
    where
     open is-small-basis sb
   g : is-small-basis-Σ → is-small-basis
   g sb =
    record
     { ≪ᴮ-is-small = λ x → pr₁ (sb x)
     ; ↡ᴮ-is-directed = λ x → pr₁ (pr₂ (sb x))
     ; ↡ᴮ-is-sup  = λ x → pr₂ (pr₂ (sb x))
     }

 being-small-basis-is-prop : Prop-Ext → is-prop is-small-basis
 being-small-basis-is-prop pe = equiv-to-prop is-small-basis-≃
                                 (being-small-basis-Σ-is-prop pe)
-}



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
 compact-basis-is-basis scb =
  record
   { ≪ᴮ-is-small    = λ x b → ( b ⊑ᴮₛ x
                            , ((b ⊑ᴮₛ x)      ≃⟨ ⊑ᴮₛ-≃-⊑ᴮ ⟩
                               (β b ⊑⟨ 𝓓 ⟩ x) ≃⟨ lemma b  ⟩
                               (β b ≪⟨ 𝓓 ⟩ x) ■))
   ; ↡ᴮ-is-directed = λ x → reindexed-family-is-directed 𝓓
                             (↓ᴮ-≃-↡ᴮ x) (↓ι x) (↓ᴮ-is-directed x)
   ; ↡ᴮ-is-sup      = λ x → reindexed-family-sup 𝓓 (↓ᴮ-≃-↡ᴮ x) (↓ι x)
                             x (↓ᴮ-is-sup x)
   }
   where
    open is-small-compact-basis scb
    lemma : (b : B) {x : ⟨ 𝓓 ⟩} → (β b ⊑⟨ 𝓓 ⟩ x) ≃ (β b ≪⟨ 𝓓 ⟩ x)
    lemma b = compact-⊑-≃-≪ 𝓓 (basis-is-compact b)
    ↓ᴮ-≃-↡ᴮ : (x : ⟨ 𝓓 ⟩) → ↓ᴮ x ≃ ↡ᴮ 𝓓 β x
    ↓ᴮ-≃-↡ᴮ x = Σ-cong (λ b → lemma b)

 locally-small-if-small-compact-basis : is-small-compact-basis
                                      → is-locally-small 𝓓
 locally-small-if-small-compact-basis scb =
  locally-small-if-small-basis 𝓓 β (compact-basis-is-basis scb)


\end{code}

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 structurally-algebraic-if-equiped-with-small-compact-basis :
    {B : 𝓥 ̇  } (β : B → ⟨ 𝓓 ⟩)
  → is-small-compact-basis 𝓓 β
  → structurally-algebraic 𝓓
 structurally-algebraic-if-equiped-with-small-compact-basis β scb =
  record
   { index-of-compact-family    = ↓ᴮₛ
   ; compact-family             = ↓ιₛ
   ; compact-family-is-directed = ↓ᴮₛ-is-directed
   ; compact-family-is-compact  = ↓ᴮₛ-compact
   ; compact-family-∐-≡         = ↓ᴮₛ-∐-≡
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
small-and-compact-basis 𝓓 {B} β β-is-small-basis κ =
 record
  { basis-is-compact = κ
  ; ⊑ᴮ-is-small      = I
  ; ↓ᴮ-is-directed   = II
  ; ↓ᴮ-is-sup        = III
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

TODO

\begin{code}

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        (𝓔 : DCPO {𝓤'} {𝓣'})
        (ρ : 𝓓 continuous-retract-of 𝓔)
       where

 open _continuous-retract-of_ ρ

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
    lemma₁ x b = ≪-is-small-valued pe 𝓓 𝓓-cont 𝓓-loc-small (r (β b)) x
     where
      𝓓-loc-small : is-locally-small 𝓓
      𝓓-loc-small = (local-smallness-preserved-by-continuous-retract
                      𝓓 𝓔 ρ (locally-small-if-small-basis 𝓔 β sb))
      𝓓-cont : is-continuous-dcpo 𝓓
      𝓓-cont = continuity-of-dcpo-preserved-by-continuous-retract 𝓓 𝓔 ρ
                ∣ structurally-continuous-if-specified-small-basis
                   𝓔 (B , (β , sb)) ∣

    σ : (x : ⟨ 𝓓 ⟩) → ↡ᴮₛ (s x) → ↡ᴮ 𝓓 (r ∘ β) x
    σ x (b , b-way-below-sx) =
     (b , continuous-retraction-≪-criterion 𝓓 𝓔 ρ (β b) x
           (≪ᴮₛ-to-≪ᴮ b-way-below-sx))

    ε : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓔 (↡ιₛ (s x))
    ε x = ↡ᴮₛ-is-directed (s x)

    eq-lemma : (x : ⟨ 𝓓 ⟩) → r (∐ 𝓔 (ε x)) ≡ x
    eq-lemma x = r (∐ 𝓔 (ε x)) ≡⟨ ap r (↡ᴮₛ-∐-≡ (s x)) ⟩
                 r (s x)       ≡⟨ s-section-of-r x     ⟩
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
