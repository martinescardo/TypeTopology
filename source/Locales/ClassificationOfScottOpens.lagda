\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.EquivalenceExamples

module Locales.ClassificationOfScottOpens
        (𝓤  : Universe)
        (pt : propositional-truncations-exist)
        (pe : propext 𝓤)
        (fe : Fun-Ext) where

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open import Locales.Frame pt fe
open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Lifting.LiftingSet pt fe
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import Lifting.Lifting 𝓤
open import UF.PropTrunc
open import Slice.Family
open PropositionalTruncation pt

\end{code}

We first define the Sierpinski domain.

\begin{code}

𝕊 : DCPO⊥
𝕊 = 𝓛-DCPO⊥ 𝓤 pe (props-are-sets {X = 𝟙 {𝓤 ⁺}} 𝟙-is-prop)

\end{code}

\begin{code}

module _ {𝓓 : DCPO⊥ {𝓤 ⁺} {𝓤}} where

 to-predicate₀ : DCPO⊥[ 𝓓 , 𝕊 ] → (⟪ 𝓓 ⟫ → Ω 𝓤)
 to-predicate₀ (f , p) x = is-defined (f x) , being-defined-is-prop (f x)

 open DefnOfScottTopology (𝓓 ⁻) 𝓤

 predicate-is-upwards-closed : (𝒻 : DCPO⊥[ 𝓓 , 𝕊 ])
                             → is-upwards-closed (to-predicate₀ 𝒻) holds
 predicate-is-upwards-closed 𝒻@(f , υ) x y p q =
  transport is-defined (μ x y q p) p
   where
    μ : is-monotone (𝓓 ⁻) (𝕊 ⁻) f
    μ = monotone-if-continuous (𝓓 ⁻) (𝕊 ⁻) 𝒻

 ⋁ₛ_ : (Σ S ꞉ Fam 𝓤 ⟪ 𝕊 ⟫ , is-Directed (𝕊 ⁻) (S .pr₂)) → ⟪ 𝕊 ⟫
 ⋁ₛ (S , δ) =
  the-sup (underlying-order (𝕊 ⁻)) (directed-completeness (𝕊 ⁻) (index S) (S [_]) δ )

 image-on-directed-set-is-directed : {I : 𝓤  ̇}(𝒻 : DCPO⊥[ 𝓓 , 𝕊 ])
                                   → (α : I → ⟪ 𝓓 ⟫)
                                   → is-Directed (𝓓 ⁻) α
                                   → is-Directed (𝕊 ⁻) (𝒻 .pr₁ ∘ α)
 image-on-directed-set-is-directed {I = I} 𝒻@(f , _) α (∣i∣ , υ) = ∣i∣ , †
  where
   μ : is-monotone (𝓓 ⁻) (𝕊 ⁻) f
   μ = monotone-if-continuous (𝓓 ⁻) (𝕊 ⁻) 𝒻

   † : is-semidirected (underlying-order (𝕊 ⁻)) (𝒻 .pr₁ ∘ α)
   † i j = ∥∥-rec ∃-is-prop γ (υ i j)
    where
     γ : Σ k ꞉ I , α i ⊑⟨ 𝓓 ⁻ ⟩ α k × α j ⊑⟨ 𝓓 ⁻ ⟩ α k
       → ∃ k ꞉ I , f (α i) ⊑⟨ 𝕊 ⁻ ⟩ f (α k) × f (α j) ⊑⟨ 𝕊 ⁻ ⟩ f (α k)
     γ (k , p₁ , p₂) = ∣ k , μ (α i) (α k) p₁ , μ (α j) (α k) p₂ ∣

 predicate-is-ibdj : (𝒻 : DCPO⊥[ 𝓓 , 𝕊 ])
                   → is-inaccessible-by-directed-joins (to-predicate₀ 𝒻) holds
 predicate-is-ibdj 𝒻@(f , ζ) (S , (δ₁ , δ₂)) p =
  ∥∥-rec ∃-is-prop ‡ †
   where
    μ : is-monotone (𝓓 ⁻) (𝕊 ⁻) f
    μ = monotone-if-continuous (𝓓 ⁻) (𝕊 ⁻) 𝒻

    δ′ : is-Directed (𝕊 ⁻) (⁅ f x ∣ x ε S ⁆ [_])
    δ′ = image-on-directed-set-is-directed 𝒻 (S .pr₂) (δ₁ , δ₂)

    d : has-sup (underlying-order (𝕊 ⁻)) (⁅ f x ∣ x ε S ⁆ [_])
    d = directed-completeness (𝕊 ⁻) (index S) (⁅ f x ∣ x ε S ⁆ [_]) δ′

    ♣ : f (∐ (𝓓 ⁻) (δ₁ , δ₂)) ＝ the-sup (underlying-order (𝕊 ⁻)) d
    ♣ = sups-are-unique
         (underlying-order (𝕊 ⁻))
         (pr₁ (axioms-of-dcpo (𝕊 ⁻)))
         (⁅ f x ∣ x ε S ⁆ [_])
         (ζ (index S) (S [_]) (δ₁ , δ₂))
         (sup-property
          (underlying-order (𝕊 ⁻))
          (directed-completeness (𝕊 ⁻) (index S) (⁅ f x ∣ x ε S ⁆ .pr₂) δ′))

    † : is-defined (⋁ₛ (⁅ f x ∣ x ε S ⁆ , δ′))
    † = transport is-defined ♣ p

    ‡ : Σ i ꞉ index S , is-defined (f (S [ i ]))
      → ∃ i ꞉ index S , to-predicate₀ 𝒻 (S [ i ]) holds
    ‡ (i , p) = ∣ i , p ∣

 to-predicate : DCPO⊥[ 𝓓 , 𝕊 ] → 𝒪ₛ
 to-predicate 𝒻@(f , _) = to-predicate₀ 𝒻
                        , predicate-is-upwards-closed 𝒻
                        , predicate-is-ibdj 𝒻

 to-𝕊-map₀ : (⟪ 𝓓 ⟫ → Ω 𝓤) → (⟪ 𝓓 ⟫ → ⟪ 𝕊 ⟫)
 to-𝕊-map₀ P x = P x holds , (λ _ → ⋆) , holds-is-prop (P x)

 to-𝕊-map : 𝒪ₛ → DCPO⊥[ 𝓓 , 𝕊 ]
 to-𝕊-map (P , υ , ι) = to-𝕊-map₀ P , c
  where
   c : is-continuous (𝓓 ⁻) (𝕊 ⁻) (to-𝕊-map₀ P)
   c I α δ = †
    where
     u = sup-property (underlying-order (𝓓 ⁻)) ((directed-completeness (𝓓 ⁻) (index (I , α)) α δ))

     † : is-sup
          (underlying-order (𝕊 ⁻))
          (to-𝕊-map₀ P (⋁ ((I , α) , δ)))
          (to-𝕊-map₀ P ∘ α)
     † = †₀ , †₁
      where
       †₀ : (i : I)
          → underlying-order (𝕊 ⁻) (to-𝕊-map₀ P (α i)) (to-𝕊-map₀ P (⋁ ((I , α) , δ)))
       †₀ i p = to-subtype-＝
                 ((λ _ → ×-is-prop (Π-is-prop fe (λ _ → 𝟙-is-prop)) (being-prop-is-prop fe)))
                 (P (α i) holds ＝⟨ Ⅰ ⟩ 𝟙 ＝⟨ Ⅱ ⟩ P (⋁ ((I , α) , δ)) holds ∎)
        where
         q : (α i ⊑⟨ 𝓓 ⁻ ⟩ₚ (⋁ ((I , α) , δ))) holds
         q = sup-is-upperbound (underlying-order (𝓓 ⁻)) u i

         Ⅰ : P (α i) holds ＝ 𝟙
         Ⅰ = pr₁ (pr₁ (pr₂ (𝟙-＝-≃ (P (α i) holds) fe pe (holds-is-prop (P (α i)))))) p ⁻¹

         Ⅱ : 𝟙 ＝ P (⋁ ((I , α) , δ)) holds
         Ⅱ = pr₁
              (pr₁ (pr₂ (𝟙-＝-≃ (P (⋁ ((I , α) , δ)) holds) fe pe (holds-is-prop _))))
              (υ (α i) (⋁ ((I , α) , δ)) p q)

       †₁ : is-lowerbound-of-upperbounds
             (underlying-order (𝕊 ⁻))
             (to-𝕊-map₀ P (⋁ ((I , α) , δ)))
             (to-𝕊-map₀ P ∘ α)
       †₁ Q φ q =
        ∥∥-rec (sethood (𝕊 ⁻)) †₂ (ι ((I , α) , δ) q)
         where
          †₂ : Σ i ꞉ I , P (α i) holds
             → to-𝕊-map₀ P (⋁ ((I , α) , δ)) ＝ Q
          †₂ (i , r) =
           to-subtype-＝
            (λ _ → ×-is-prop (Π-is-prop fe (λ _ → 𝟙-is-prop)) (being-prop-is-prop fe))
            (P (⋁ ((I , α) , δ)) holds ＝⟨ {!!} ⟩
             P (α i) holds             ＝⟨ {!φ i ?!} ⟩
             Q .pr₁                    ∎)

\end{code}
