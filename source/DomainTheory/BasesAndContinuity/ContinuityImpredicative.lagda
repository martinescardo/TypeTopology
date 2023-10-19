Simcha van Collem, 12th October 2023

If we assume propositional resizing, we can recover a continuity/algebraic
structure on 𝓓 from the respective properties.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.ContinuityImpredicative
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥

open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

open import UF.Size hiding (is-locally-small; is-small)

structurally-continuous-if-continuous : (psz : propositional-resizing (𝓥 ⁺ ⊔ 𝓣) 𝓥)
                                        (𝓓 : DCPO {𝓥} {𝓣})
                                      → is-continuous-dcpo 𝓓
                                      → structurally-continuous 𝓓
structurally-continuous-if-continuous psz 𝓓 c =
 record
  { index-of-approximating-family = index
  ; approximating-family = family
  ; approximating-family-is-directed = family-is-directed
  ; approximating-family-is-way-below = family-is-way-below
  ; approximating-family-∐-＝ = family-∐-＝
  }
  where
   index : ⟨ 𝓓 ⟩ → 𝓥 ̇
   index x = Σ y ꞉ ⟨ 𝓓 ⟩ , resize psz (y ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓)

   make-index : {x : ⟨ 𝓓 ⟩} (y : ⟨ 𝓓 ⟩) → y ≪⟨ 𝓓 ⟩ x → index x
   make-index y p = y , to-resize psz _ (≪-is-prop-valued 𝓓) p

   family : (x : ⟨ 𝓓 ⟩) → index x → ⟨ 𝓓 ⟩
   family x = pr₁

   ≪-from-resize : {x y : ⟨ 𝓓 ⟩}
                  → resize psz (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓)
                  → x ≪⟨ 𝓓 ⟩ y
   ≪-from-resize p = from-resize psz _ (≪-is-prop-valued 𝓓) p

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
       family-is-semidirected (y₁ , y₁≪x) (y₂ , y₂≪x) =
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
         h1 = (≪-from-resize y₁≪x) _ _ (approximating-family-is-directed x)
               (approximating-family-∐-⊒ x)

         h2 : ∃ i ꞉ index-of-approximating-family x , y₂ ⊑⟨ 𝓓 ⟩ approximating-family x i
         h2 = (≪-from-resize y₂≪x) _ _ (approximating-family-is-directed x)
               (approximating-family-∐-⊒ x)

   family-is-way-below : (x : ⟨ 𝓓 ⟩) → is-way-upperbound 𝓓 x (family x)
   family-is-way-below x (y , y≪x) = ≪-from-resize y≪x

   family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (family-is-directed x) ＝ x
   family-∐-＝ x = ∥∥-rec (sethood 𝓓) γ c
    where
     γ : structurally-continuous 𝓓 → ∐ 𝓓 (family-is-directed x) ＝ x
     γ sc = antisymmetry 𝓓 _ _
             (∐-is-lowerbound-of-upperbounds 𝓓 _ _
               λ (y , y≪x) → ≪-to-⊑ 𝓓 (≪-from-resize y≪x))
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

structurally-algebraic-if-algebraic : (psz : propositional-resizing (𝓥 ⁺ ⊔ 𝓣) 𝓥)
                                      (𝓓 : DCPO {𝓥} {𝓣})
                                    → is-algebraic-dcpo 𝓓
                                    → structurally-algebraic 𝓓
structurally-algebraic-if-algebraic psz 𝓓 a =
 record
  { index-of-compact-family = index
  ; compact-family = family
  ; compact-family-is-directed = family-is-directed
  ; compact-family-is-compact = family-is-compact
  ; compact-family-∐-＝ = family-∐-＝
  }
  where
   index : ⟨ 𝓓 ⟩ → 𝓥 ̇
   index x = Σ y ꞉ ⟨ 𝓓 ⟩ ,
              resize psz (is-compact 𝓓 y) (being-compact-is-prop 𝓓 y) ×
              resize psz (y ≪⟨ 𝓓 ⟩ x) (≪-is-prop-valued 𝓓)

   make-index : {x : ⟨ 𝓓 ⟩} → (y : ⟨ 𝓓 ⟩) → is-compact 𝓓 y → y ≪⟨ 𝓓 ⟩ x → index x
   make-index y y≪y y≪x =
    y ,
    to-resize psz _ (being-compact-is-prop 𝓓 y) y≪y ,
    to-resize psz _ (≪-is-prop-valued 𝓓) y≪x

   family : (x : ⟨ 𝓓 ⟩) → index x → ⟨ 𝓓 ⟩
   family x = pr₁

   ≪-from-resize : {x y : ⟨ 𝓓 ⟩}
                  → resize psz (x ≪⟨ 𝓓 ⟩ y) (≪-is-prop-valued 𝓓)
                  → x ≪⟨ 𝓓 ⟩ y
   ≪-from-resize p = from-resize psz _ (≪-is-prop-valued 𝓓) p

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
         (≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i)
          (compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅1⦆ ]
           ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅2⦆ ]
           x                                  ∎⟨ 𝓓 ⟩))
        where
         ⦅1⦆ = ∐-is-upperbound 𝓓 (compact-family-is-directed x) i
         ⦅2⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

       family-is-inhabited : ∥ index x ∥
       family-is-inhabited =
        ∥∥-functor
         compact-family-index-to-index
         (inhabited-if-Directed 𝓓 _ (compact-family-is-directed x))

       family-is-semidirected : is-Semidirected 𝓓 (family x)
       family-is-semidirected (y₁ , y₁≪y₁ , y₁≪x) (y₂ , y₂≪y₂ , y₂≪x) =
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
         h1 = ≪-from-resize y₁≪x _ _ _ (＝-to-⊒ 𝓓 (compact-family-∐-＝ x))

         h2 : ∃ j ꞉ index-of-compact-family x , y₂ ⊑⟨ 𝓓 ⟩ compact-family x j
         h2 = ≪-from-resize y₂≪x _ _ _ (＝-to-⊒ 𝓓 (compact-family-∐-＝ x))

   family-is-compact : (x : ⟨ 𝓓 ⟩) (i : index x) → is-compact 𝓓 (family x i)
   family-is-compact x (y , y≪y , y≪x) = ≪-from-resize y≪y

   family-∐-＝ : (x : ⟨ 𝓓 ⟩) → ∐ 𝓓 (family-is-directed x) ＝ x
   family-∐-＝ x = ∥∥-rec (sethood 𝓓) γ a
    where
     γ : structurally-algebraic 𝓓 → ∐ 𝓓 (family-is-directed x) ＝ x
     γ sa = antisymmetry 𝓓 _ _
             (∐-is-lowerbound-of-upperbounds 𝓓 _ _
               λ (y , y≪y , y≪x) → ≪-to-⊑ 𝓓 (≪-from-resize y≪x))
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
                (make-index (compact-family x i) (compact-family-is-compact x i) αᵢ≪x)
          where
           αᵢ≪x : compact-family x i ≪⟨ 𝓓 ⟩ x
           αᵢ≪x = ≪-⊑-to-≪ 𝓓 (compact-family-is-compact x i)
                   (compact-family x i                 ⊑⟨ 𝓓 ⟩[ ⦅3⦆ ]
                    ∐ 𝓓 (compact-family-is-directed x) ⊑⟨ 𝓓 ⟩[ ⦅4⦆ ]
                    x                                  ∎⟨ 𝓓 ⟩)
            where
             ⦅3⦆ = ∐-is-upperbound 𝓓 _ _
             ⦅4⦆ = ＝-to-⊑ 𝓓 (compact-family-∐-＝ x)

\end{code}
