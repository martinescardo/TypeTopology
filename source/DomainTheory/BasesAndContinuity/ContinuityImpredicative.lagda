Simcha van Collem, 12th October 2023

For a locally small dcpo 𝓓, whose carrier type lives in 𝓥, we can construct
continuous and algebraic structures from their respective properties. We do this
by making a canonical choice for the approximating and compact families:
the approximating family at x consists of all elements way below x, and the
compact family at x consists of all compact elements ordered below x. Their
index types live in 𝓥, as we assumed the carrier type of 𝓓 to live in 𝓥 and 𝓓 is
locally small.

To prove the required properties for these families, we can access the
unspecified continuous/algebraic structure, as we are proving a proposition.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.ContinuityImpredicative
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Base hiding (_≈_)
open import UF.Equiv

open import UF.Size hiding (is-locally-small; is-small)
open import UF.Subsingletons

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

module _
        (pe : Prop-Ext)
        (𝓓 : DCPO {𝓥} {𝓣})
        (ls : is-locally-small 𝓓)
       where

 structurally-continuous-if-continuous : is-continuous-dcpo 𝓓
                                       → structurally-continuous 𝓓
 structurally-continuous-if-continuous c =
  record
   { index-of-approximating-family = index
   ; approximating-family = family
   ; approximating-family-is-directed = family-is-directed
   ; approximating-family-is-way-below = family-is-way-below
   ; approximating-family-∐-＝ = family-∐-＝
   }
   where
    _≪ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
    x ≪ₛ y = resized (x ≪⟨ 𝓓 ⟩ y) (≪-is-small-valued pe 𝓓 c ls x y)

    ≪ₛ-≃-≪ : {x y : ⟨ 𝓓 ⟩} → x ≪ₛ y ≃ x ≪⟨ 𝓓 ⟩ y
    ≪ₛ-≃-≪ = resizing-condition (≪-is-small-valued pe 𝓓 c ls _ _)

    ≪ₛ-to-≪ : {x y : ⟨ 𝓓 ⟩} → x ≪ₛ y → x ≪⟨ 𝓓 ⟩ y
    ≪ₛ-to-≪ = ⌜ ≪ₛ-≃-≪ ⌝

    ≪-to-≪ₛ : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ≪ₛ y
    ≪-to-≪ₛ = ⌜ ≪ₛ-≃-≪ ⌝⁻¹

    index : ⟨ 𝓓 ⟩ → 𝓥 ̇
    index x = Σ y ꞉ ⟨ 𝓓 ⟩ , y ≪ₛ x

    make-index : {x : ⟨ 𝓓 ⟩} (y : ⟨ 𝓓 ⟩) → y ≪⟨ 𝓓 ⟩ x → index x
    make-index {x} y y≪x = y , ≪-to-≪ₛ y≪x

    family : (x : ⟨ 𝓓 ⟩) → index x → ⟨ 𝓓 ⟩
    family x = pr₁

    family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (family x)
    family-is-directed x = ∥∥-rec (being-directed-is-prop _ (family x)) γ c
     where
      γ : structurally-continuous 𝓓 → is-Directed 𝓓 (family x)
      γ sc = family-is-inhabited , family-is-semidirected
       where
        open structurally-continuous sc

        approximating-family-index-to-index : (i : index-of-approximating-family x)
                                            → index x
        approximating-family-index-to-index i =
         make-index (approximating-family x i)
          (approximating-family-is-way-below x i)

        family-is-inhabited : ∥ index x ∥
        family-is-inhabited =
         ∥∥-functor
          approximating-family-index-to-index
          (inhabited-if-Directed 𝓓 _ (approximating-family-is-directed x))

        family-is-semidirected : is-Semidirected 𝓓 (family x)
        family-is-semidirected (y₁ , y₁≪ₛx) (y₂ , y₂≪ₛx) =
         ∥∥-rec₂ ∃-is-prop f h1 h2
         where
          f : Σ i ꞉ index-of-approximating-family x , y₁ ⊑⟨ 𝓓 ⟩ approximating-family x i
            → Σ j ꞉ index-of-approximating-family x , y₂ ⊑⟨ 𝓓 ⟩ approximating-family x j
            → ∃ k ꞉ index x , y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                              y₂ ⊑⟨ 𝓓 ⟩ family x k
          f (i , y₁⊑αᵢ) (j , y₂⊑αⱼ) =
           ∥∥-functor g (semidirected-if-Directed 𝓓 _ (approximating-family-is-directed x) i j)
           where
            g : Σ k ꞉ index-of-approximating-family x ,
                 approximating-family x i ⊑⟨ 𝓓 ⟩ approximating-family x k ×
                 approximating-family x j ⊑⟨ 𝓓 ⟩ approximating-family x k
              → Σ k ꞉ index x ,
                 y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                 y₂ ⊑⟨ 𝓓 ⟩ family x k
            g (k , αᵢ⊑αₖ , αⱼ⊑αₖ) =
             approximating-family-index-to-index k ,
             transitivity 𝓓 _ _ _ y₁⊑αᵢ αᵢ⊑αₖ ,
             transitivity 𝓓 _ _ _ y₂⊑αⱼ αⱼ⊑αₖ

          h1 : ∃ i ꞉ index-of-approximating-family x , y₁ ⊑⟨ 𝓓 ⟩ approximating-family x i
          h1 = (≪ₛ-to-≪ y₁≪ₛx) _ _ (approximating-family-is-directed x)
                (approximating-family-∐-⊒ x)

          h2 : ∃ i ꞉ index-of-approximating-family x , y₂ ⊑⟨ 𝓓 ⟩ approximating-family x i
          h2 = (≪ₛ-to-≪ y₂≪ₛx) _ _ (approximating-family-is-directed x)
                (approximating-family-∐-⊒ x)

    family-is-way-below : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (family x)
    family-is-way-below x (y , y≪ₛx) = ≪ₛ-to-≪ y≪ₛx

    family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (family-is-directed x) ＝ x
    family-∐-＝ x = ∥∥-rec (sethood 𝓓) γ c
     where
      γ : structurally-continuous 𝓓 → ∐ 𝓓 (family-is-directed x) ＝ x
      γ sc = antisymmetry 𝓓 _ _
              (∐-is-lowerbound-of-upperbounds 𝓓 _ _
                λ (y , y≪ₛx) → ≪-to-⊑ 𝓓 (≪ₛ-to-≪ y≪ₛx))
              (x                                        ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               ∐ 𝓓 (family-is-directed x)               ∎⟨ 𝓓 ⟩)
       where
        open structurally-continuous sc

        ⦅1⦆ = approximating-family-∐-⊒ x

        ⦅2⦆ : ∐ 𝓓 (approximating-family-is-directed x) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (family-is-directed x)
        ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 _ _
              λ i → ∐-is-upperbound 𝓓 (family-is-directed x)
                     (make-index
                      (approximating-family x i)
                      (approximating-family-is-way-below x i))

 structurally-algebraic-if-algebraic : is-algebraic-dcpo 𝓓
                                     → structurally-algebraic 𝓓
 structurally-algebraic-if-algebraic a =
  record
   { index-of-compact-family = index
   ; compact-family = family
   ; compact-family-is-directed = family-is-directed
   ; compact-family-is-compact = family-is-compact
   ; compact-family-∐-＝ = family-∐-＝
   }
   where
    open is-locally-small ls

    _≪ₛ_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
    x ≪ₛ y = resized (x ≪⟨ 𝓓 ⟩ y)
               (≪-is-small-valued pe 𝓓
                (is-continuous-dcpo-if-algebraic-dcpo 𝓓 a) ls x y)

    ≪ₛ-≃-≪ : {x y : ⟨ 𝓓 ⟩} → x ≪ₛ y ≃ x ≪⟨ 𝓓 ⟩ y
    ≪ₛ-≃-≪ = resizing-condition
                (≪-is-small-valued pe 𝓓
                 (is-continuous-dcpo-if-algebraic-dcpo 𝓓 a) ls _ _)

    ≪ₛ-to-≪ : {x y : ⟨ 𝓓 ⟩} → x ≪ₛ y → x ≪⟨ 𝓓 ⟩ y
    ≪ₛ-to-≪ = ⌜ ≪ₛ-≃-≪ ⌝

    ≪-to-≪ₛ : {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ≪ₛ y
    ≪-to-≪ₛ = ⌜ ≪ₛ-≃-≪ ⌝⁻¹

    index : ⟨ 𝓓 ⟩ → 𝓥 ̇
    index x = Σ y ꞉ ⟨ 𝓓 ⟩ , (y ≪ₛ y) × (y ⊑ₛ x)

    make-index : {x : ⟨ 𝓓 ⟩} → (y : ⟨ 𝓓 ⟩) → is-compact 𝓓 y → y ⊑⟨ 𝓓 ⟩ x → index x
    make-index y y≪y y⊑x = y , ≪-to-≪ₛ y≪y , ⊑-to-⊑ₛ y⊑x

    family : (x : ⟨ 𝓓 ⟩) → index x → ⟨ 𝓓 ⟩
    family x = pr₁

    family-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (family x)
    family-is-directed x = ∥∥-rec (being-directed-is-prop _ (family x)) γ a
     where
      γ : structurally-algebraic 𝓓 → is-Directed 𝓓 (family x)
      γ sa = family-is-inhabited , family-is-semidirected
       where
        open structurally-algebraic sa

        compact-family-index-to-index : (i : index-of-compact-family x)
                                      → index x
        compact-family-index-to-index i =
         make-index
          (compact-family x i)
          (compact-family-is-compact x i)
          (compact-family-is-upperbound x i)
         where
          ⦅1⦆ = ∐-is-upperbound 𝓓 (compact-family-is-directed x) i
          ⦅2⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

        family-is-inhabited : ∥ index x ∥
        family-is-inhabited =
         ∥∥-functor
          compact-family-index-to-index
          (inhabited-if-Directed 𝓓 _ (compact-family-is-directed x))

        family-is-semidirected : is-Semidirected 𝓓 (family x)
        family-is-semidirected (y₁ , y₁≪ₛy₁ , y₁⊑ₛx) (y₂ , y₂≪ₛy₂ , y₂⊑ₛx) =
         ∥∥-rec₂ ∃-is-prop f h1 h2
         where
          f : Σ i ꞉ index-of-compact-family x , y₁ ⊑⟨ 𝓓 ⟩ compact-family x i
            → Σ j ꞉ index-of-compact-family x , y₂ ⊑⟨ 𝓓 ⟩ compact-family x j
            → ∃ k ꞉ index x , y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                              y₂ ⊑⟨ 𝓓 ⟩ family x k
          f (i , y₁⊑αᵢ) (j , y₂⊑αⱼ) =
           ∥∥-functor g (semidirected-if-Directed 𝓓 _ (compact-family-is-directed x) i j)
           where
            g : Σ k ꞉ index-of-compact-family x ,
                 compact-family x i ⊑⟨ 𝓓 ⟩ compact-family x k ×
                 compact-family x j ⊑⟨ 𝓓 ⟩ compact-family x k
              → Σ k ꞉ index x ,
                 y₁ ⊑⟨ 𝓓 ⟩ family x k ×
                 y₂ ⊑⟨ 𝓓 ⟩ family x k
            g (k , αᵢ⊑αₖ , αⱼ⊑αₖ) =
             compact-family-index-to-index k ,
             transitivity 𝓓 _ _ _ y₁⊑αᵢ αᵢ⊑αₖ ,
             transitivity 𝓓 _ _ _ y₂⊑αⱼ αⱼ⊑αₖ

          h1 : ∃ i ꞉ index-of-compact-family x , y₁ ⊑⟨ 𝓓 ⟩ compact-family x i
          h1 = ≪-⊑-to-≪ 𝓓 (≪ₛ-to-≪ y₁≪ₛy₁) (⊑ₛ-to-⊑ y₁⊑ₛx) _ _ _
                (＝-to-⊒ 𝓓 (compact-family-∐-＝ x))

          h2 : ∃ j ꞉ index-of-compact-family x , y₂ ⊑⟨ 𝓓 ⟩ compact-family x j
          h2 = ≪-⊑-to-≪ 𝓓 (≪ₛ-to-≪ y₂≪ₛy₂) (⊑ₛ-to-⊑ y₂⊑ₛx) _ _ _
                (＝-to-⊒ 𝓓 (compact-family-∐-＝ x))

    family-is-compact : (x : ⟨ 𝓓 ⟩) (i : index x) → is-compact 𝓓 (family x i)
    family-is-compact x (y , y≪ₛy , y⊑ₛx) = ≪ₛ-to-≪ y≪ₛy

    family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (family-is-directed x) ＝ x
    family-∐-＝ x = ∥∥-rec (sethood 𝓓) γ a
     where
      γ : structurally-algebraic 𝓓 → ∐ 𝓓 (family-is-directed x) ＝ x
      γ sa = antisymmetry 𝓓 _ _
              (∐-is-lowerbound-of-upperbounds 𝓓 _ _
                λ (y , y≪ₛy , y⊑ₛx) → ⊑ₛ-to-⊑ y⊑ₛx)
              (x                                  ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
               ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
               ∐ 𝓓 (family-is-directed x)         ∎⟨ 𝓓 ⟩)
       where
        open structurally-algebraic sa

        ⦅1⦆ = ＝-to-⊒ 𝓓 (compact-family-∐-＝ x)

        ⦅2⦆ : ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (family-is-directed x)
        ⦅2⦆ = ∐-is-lowerbound-of-upperbounds 𝓓 _ _ g
         where
          g : (i : index-of-compact-family x)
            → compact-family x i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (family-is-directed x)
          g i = ∐-is-upperbound 𝓓 (family-is-directed x)
                 (make-index
                  (compact-family x i)
                  (compact-family-is-compact x i)
                  (compact-family-is-upperbound x i))

\end{code}
