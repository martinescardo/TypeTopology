--------------------------------------------------------------------------------
title:          Universal property of the Sierpiński locale
author:         Ayberk Tosun
date-started:   2024-03-06
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons

module Locales.Sierpinski.UniversalProperty
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Topology.ScottTopologyProperties pt fe
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.SmallBasis pt fe sr
open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤
open import Locales.Sierpinski.Definition 𝓤 pe pt fe sr
open import Locales.Sierpinski.Properties 𝓤 pe pt fe sr
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open Locale
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

Recall that the Scott open `truth` is just the singleton Scott open `{ ⊤ }`.

\begin{code}

open DefnOfScottTopology 𝕊𝓓 𝓤
open DefnOfScottLocale 𝕊𝓓 𝓤 pe hiding (⊤ₛ)
open ScottLocaleConstruction 𝕊𝓓 hscb pe

holds-gives-equal-⊤ₛ : (P : ⟨ 𝕊𝓓 ⟩∙) → (P ∈ₛ truth) holds → P ＝ ⊤ₛ
holds-gives-equal-⊤ₛ (P , f , φ) p =
 to-subtype-＝
  (λ Q → ×-is-prop (Π-is-prop fe (λ _ → 𝟙-is-prop)) (being-prop-is-prop fe))
  (holds-gives-equal-𝟙 pe P φ p)


contains-bottom-implies-is-top : (𝔘 : ⟨ 𝒪 𝕊 ⟩) → (⊥ₛ ∈ₛ 𝔘) holds → 𝔘 ＝ 𝟏[ 𝒪 𝕊 ]
contains-bottom-implies-is-top 𝔘 p = only-𝟏-is-above-𝟏 (𝒪 𝕊) 𝔘 †
 where
  open 𝒪ₛᴿ

  ‡ : (𝟏[ 𝒪 𝕊 ] ⊆ₛ 𝔘) holds
  ‡ x ⋆ = upward-closure 𝔘 ⊥ₛ x p (⊥-is-least 𝕊𝓓⊥ x)

  † : (𝟏[ 𝒪 𝕊 ] ≤[ poset-of (𝒪 𝕊) ] 𝔘) holds
  † = ⊆ₛ-implies-⊆ₖ 𝟏[ 𝒪 𝕊 ] 𝔘 ‡

main-lemma : (𝔘 : ⟨ 𝒪 𝕊 ⟩) → (⊥ₛ ∈ₛ 𝔘 ⇒ ⊤ₛ ∈ₛ 𝔘) holds
main-lemma 𝔘 p = transport (λ - → (⊤ₛ ∈ₛ -) holds) (q ⁻¹) ⋆
 where
  open 𝒪ₛᴿ

  q : 𝔘 ＝ 𝟏[ 𝒪 𝕊 ]
  q = contains-bottom-implies-is-top 𝔘 p

contains-⊤ₛ-implies-above-truth : (𝔘 : ⟨ 𝒪 𝕊 ⟩)
                                → (⊤ₛ ∈ₛ 𝔘) holds
                                → (truth ≤[ poset-of (𝒪 𝕊) ] 𝔘) holds
contains-⊤ₛ-implies-above-truth 𝔘 μₜ = ⊆ₛ-implies-⊆ₖ truth 𝔘 †
 where
  † : (truth ⊆ₛ 𝔘) holds
  † P μₚ = transport (λ - → (- ∈ₛ 𝔘) holds) (holds-gives-equal-⊤ₛ P μₚ ⁻¹) μₜ

above-truth-implies-contains-⊤ₛ : (𝔘 : ⟨ 𝒪 𝕊 ⟩)
                                → (truth ≤[ poset-of (𝒪 𝕊) ] 𝔘) holds
                                → (⊤ₛ ∈ₛ 𝔘) holds
above-truth-implies-contains-⊤ₛ 𝔘 p = ⊆ₖ-implies-⊆ₛ truth 𝔘 p ⊤ₛ ⋆

open PropertiesAlgebraic 𝓤 𝕊𝓓 𝕊𝓓-is-structurally-algebraic



universal-property-of-sierpinski : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                                 → (U : ⟨ 𝒪 X ⟩)
                                 → ∃! (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f truth
universal-property-of-sierpinski X U =
 ((h , φ , (ψ , ϑ)) , †) , ‡
  where
   open PosetNotation (poset-of (𝒪 X))
   open PosetReasoning (poset-of (𝒪 X))
   open Joins _≤_

   I : ⟨ 𝒪 𝕊 ⟩ → 𝓤  ̇
   I 𝔘 = (⊤ₛ ∈ₛ 𝔘) holds + (⊥ₛ ∈ₛ 𝔘) holds

   α : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → (⊤ₛ ∈ₛ 𝔙) holds + (⊥ₛ ∈ₛ 𝔙) holds → ⟨ 𝒪 X ⟩
   α V (inl _) = U
   α V (inr _) = 𝟏[ 𝒪 X ]

   openₓ : ⟨ 𝒪 𝕊 ⟩ → Fam 𝓤 ⟨ 𝒪 X ⟩
   openₓ V = (I V , α V)

   h : ⟨ 𝒪 𝕊 ⟩ → ⟨ 𝒪 X ⟩
   h V = ⋁[ 𝒪 X ] openₓ V

   φ : h 𝟏[ 𝒪 𝕊 ] ＝ 𝟏[ 𝒪 X ]
   φ = only-𝟏-is-above-𝟏 (𝒪 X) (h 𝟏[ 𝒪 𝕊 ]) γ
    where
     γ : (𝟏[ 𝒪 X ] ≤ h 𝟏[ 𝒪 𝕊 ]) holds
     γ = ⋁[ 𝒪 X ]-upper ((I 𝟏[ 𝒪 𝕊 ]) , (α 𝟏[ 𝒪 𝕊 ])) (inr ⋆)

   ψ : preserves-binary-meets (𝒪 𝕊) (𝒪 X) h holds
   ψ 𝔙 𝔚 = ≤-is-antisymmetric (poset-of (𝒪 X)) ψ₁ ψ₂
    where
     ψ₁ : (h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚) ≤ (h 𝔙 ∧[ 𝒪 X ] h 𝔚)) holds
     ψ₁ = {!!}

     ψ₂ : ((h 𝔙 ∧[ 𝒪 X ] h 𝔚) ≤ h (𝔙 ∧[ 𝒪 𝕊 ] 𝔚)) holds
     ψ₂ = {!!}

   ϑ : {!!}
   ϑ = {!!}

   𝒽 : 𝒪 𝕊 ─f→ 𝒪 X
   𝒽 = h , φ , ψ , ϑ

   †₁ : (U ≤ h truth) holds
   †₁ = U ≤⟨ ⋁[ 𝒪 X ]-upper _ (inl ⋆) ⟩ h truth ■

   †₂ : (h truth ≤ U) holds
   †₂ = ⋁[ 𝒪 X ]-least (openₓ truth) (U , γ)
    where
     γ : (U is-an-upper-bound-of (openₓ truth)) holds
     γ (inl ⋆) = ≤-is-reflexive (poset-of (𝒪 X)) U


   † : U ＝ h truth
   † = ≤-is-antisymmetric (poset-of (𝒪 X)) †₁ †₂

   ‡ : is-central (Σ (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f truth) (𝒽 , †)
   ‡ (ℊ@(g , φ₀ , ψ₀ , ϑ₀) , †₀) =
    to-subtype-＝
     (λ h → carrier-of-[ poset-of (𝒪 X) ]-is-set)
     (continuous-map-equality (𝒪 𝕊) (𝒪 X) 𝒽 ℊ γ)
      where
       𝓂 : is-monotonic (poset-of (𝒪 𝕊)) (poset-of (𝒪 X)) g holds
       𝓂 = frame-morphisms-are-monotonic (𝒪 𝕊) (𝒪 X) g (φ₀ , ψ₀ , ϑ₀)

       γ₁ : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → (h 𝔙 ≤ g 𝔙) holds
       γ₁ 𝔙 = ⋁[ 𝒪 X ]-least (openₓ 𝔙) (g 𝔙 , β₁)
        where
         β₁ : (g 𝔙 is-an-upper-bound-of openₓ 𝔙) holds
         β₁ (inl p) = U ＝⟨ †₀ ⟩ₚ g truth ≤⟨ Ⅱ ⟩ g 𝔙 ■
                       where
                        Ⅱ = 𝓂 (truth , 𝔙) (contains-⊤ₛ-implies-above-truth 𝔙 p)
         β₁ (inr p) = 𝟏[ 𝒪 X ] ＝⟨ Ⅰ ⟩ₚ g 𝟏[ 𝒪 𝕊 ] ＝⟨ Ⅱ ⟩ₚ g 𝔙 ■
                       where
                        Ⅰ = φ₀ ⁻¹
                        Ⅱ = ap g (contains-bottom-implies-is-top 𝔙 p ⁻¹)

       γ₂ : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → (g 𝔙 ≤ h 𝔙) holds
       γ₂ 𝔙 = g 𝔙                      ＝⟨ ap g cov ⟩ₚ
              g (⋁[ 𝒪 𝕊 ] 𝔖)           ＝⟨ Ⅱ ⟩ₚ
              ⋁[ 𝒪 X ] ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆ ≤⟨ focus ⟩
              h 𝔙                      ■
        where
         open Joins _⊆ₛ_ renaming (_is-an-upper-bound-of_ to _is-an-upper-bound-ofₛ_)

         𝔖 = covering-familyₛ 𝕊 𝕊-is-spectralᴰ 𝔙

         Ⅱ = ⋁[ 𝒪 X ]-unique ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆ (g (⋁[ 𝒪 𝕊 ] 𝔖)) (ϑ₀ 𝔖)

         cov : 𝔙 ＝ ⋁[ 𝒪 𝕊 ] 𝔖
         cov = ⋁[ 𝒪 𝕊 ]-unique 𝔖 𝔙 (basisₛ-covers-do-cover 𝕊 𝕊-is-spectralᴰ 𝔙)

         cov₀ : (𝔙 is-an-upper-bound-ofₛ 𝔖) holds
         cov₀ bs = ⊆ₖ-implies-⊆ₛ (𝔖 [ bs ]) 𝔙 (pr₁ (basisₛ-covers-do-cover 𝕊 𝕊-is-spectralᴰ 𝔙) bs)

         final : (i : index 𝔖) → (g (𝔖 [ i ]) ≤ h 𝔙) holds
         final (bs , b) = cases₃ case₁ case₂ case₃ (basis-trichotomy bs)
          where
           open PosetReasoning poset-of-scott-opensₛ
            renaming (_≤⟨_⟩_ to _≤⟨_⟩ₛ_;
                      _■ to _■ₛ;
                      _＝⟨_⟩ₚ_ to _＝⟨_⟩ₛ_)

           case₁ : ℬ𝕊 [ bs ] ＝ 𝟏[ 𝒪 𝕊 ]
                 → (g (𝔖 [ bs , b ]) ≤ h 𝔙) holds
           case₁ q = transport (λ - → (g (𝔖 [ bs , b ]) ≤ h -) holds)
                      r
                      (g (ℬ𝕊 [ bs ]) ≤⟨ 𝟏-is-top (𝒪 X) (g (ℬ𝕊 [ bs ])) ⟩
                      𝟏[ 𝒪 X ]       ＝⟨ φ ⁻¹ ⟩ₚ h 𝟏[ 𝒪 𝕊 ] ■)
            where
             χ : (𝟏[ 𝒪 𝕊 ] ⊆ₛ (ℬ𝕊 [ bs ])) holds
             χ = reflexivity+ poset-of-scott-opensₛ (q ⁻¹)

             r : 𝟏[ 𝒪 𝕊 ] ＝ 𝔙
             r = ⊆ₛ-is-antisymmetric
                  (λ x p → cov₀ (bs , b) x (χ x p))
                  (⊤ₛ-is-top 𝔙)

           case₂ : ℬ𝕊 [ bs ] ＝ truth
                 → (g (𝔖 [ bs , b ]) ≤ h 𝔙) holds
           case₂ p = g (𝔖 [ bs , b ]) ＝⟨ refl ⟩ₚ
                     g (ℬ𝕊 [ bs ])    ＝⟨ क ⟩ₚ
                     g truth          ＝⟨ ख ⟩ₚ
                     U                ≤⟨ ग ⟩
                     h 𝔙              ■
            where
             p₀ : (truth ⊆ₛ (ℬ𝕊 [ bs ])) holds
             p₀ = reflexivity+ poset-of-scott-opensₛ (p ⁻¹)

             ζ : (truth ⊆ₛ 𝔙) holds
             ζ P μ = cov₀ (bs , b) P (p₀ P μ)

             χ : (⊤ₛ ∈ₛ 𝔙) holds
             χ = above-truth-implies-contains-⊤ₛ 𝔙 (⊆ₛ-implies-⊆ₖ truth 𝔙 ζ)

             क = ap g p
             ख = †₀ ⁻¹
             ग = ⋁[ 𝒪 X ]-upper (openₓ 𝔙) (inl χ)

           case₃ : ℬ𝕊 [ bs ] ＝ 𝟎[ 𝒪 𝕊 ]
                 → (g (𝔖 [ bs , b ]) ≤ h 𝔙) holds
           case₃ q = g (𝔖 [ bs , b ]) ＝⟨ refl   ⟩ₚ
                     g (ℬ𝕊 [ bs ])    ＝⟨ ap g q ⟩ₚ
                     g 𝟎[ 𝒪 𝕊 ]       ＝⟨ frame-homomorphisms-preserve-bottom (𝒪 𝕊) (𝒪 X) ℊ ⟩ₚ
                     𝟎[ 𝒪 X ]         ≤⟨ 𝟎-is-bottom (𝒪 X) (h 𝔙) ⟩
                     h 𝔙              ■

         focus : ((⋁[ 𝒪 X ] ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆) ≤ h 𝔙) holds
         focus = ⋁[ 𝒪 X ]-least ⁅ g 𝔅 ∣ 𝔅 ε 𝔖 ⁆ (h 𝔙 , final)

       γ : (𝔙 : ⟨ 𝒪 𝕊 ⟩) → h 𝔙 ＝ g 𝔙
       γ 𝔙 = ≤-is-antisymmetric (poset-of (𝒪 X)) (γ₁ 𝔙) (γ₂ 𝔙)

{--

-- ((f , tp , mp , jp) , equality) , uniqueness
 where
  open PosetReasoning (poset-of (𝒪 X))

  fₘ : is-monotonic (poset-of (𝒪 𝕊)) (poset-of (𝒪 X)) f holds
  fₘ (V₁ , V₂) p = ⋁[ 𝒪 X ]-least (I V₁ , α V₁) (f V₂ , †)
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

    † : (f V₂ is-an-upper-bound-of (I V₁ , α V₁)) holds
    † (inl μ) = U ≤⟨ ⋁[ 𝒪 X ]-upper (I V₂ , α V₂) (inl (p ⊤ₛ μ)) ⟩ f V₂ ■
    † (inr μ) = 𝟏[ 𝒪 X ] ≤⟨ ⋁[ 𝒪 X ]-upper (I V₂ , α V₂) (inr (p ⊥ₛ μ)) ⟩ f V₂ ■

  tp : f 𝟏[ 𝒪 𝕊 ] ＝ 𝟏[ 𝒪 X ]
  tp = only-𝟏-is-above-𝟏 (𝒪 X) (f 𝟏[ 𝒪 𝕊 ]) †
   where
    † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f 𝟏[ 𝒪 𝕊 ]) holds
    † = ⋁[ 𝒪 X ]-upper ((I 𝟏[ 𝒪 𝕊 ]) , (α 𝟏[ 𝒪 𝕊 ])) (inr ⋆)

  mp : (U V : ⟨ 𝒪 𝕊 ⟩) → f (U ∧[ 𝒪 𝕊 ] V) ＝ f U ∧[ 𝒪 X ] f V
  mp V₁ V₂ = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
   where
    † : (f (V₁ ∧[ 𝒪 𝕊 ] V₂) ≤[ poset-of (𝒪 X) ] (f V₁ ∧[ 𝒪 X ] f V₂)) holds
    † = ∧[ 𝒪 X ]-greatest (f V₁) (f V₂) (f (V₁ ∧[ 𝒪 𝕊 ] V₂)) (fₘ ((V₁ ∧[ 𝒪 𝕊 ] V₂) , V₁) (∧[ 𝒪 𝕊 ]-lower₁ V₁ V₂)) ((fₘ ((V₁ ∧[ 𝒪 𝕊 ] V₂) , V₂) (∧[ 𝒪 𝕊 ]-lower₂ V₁ V₂)))

    goal : ((i , j) : I V₁ × I V₂)
         → ((α V₁ i ∧[ 𝒪 X ] α V₂ j) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆)) holds
    goal (inl q₁ , inl q₂) = α V₁ (inl q₁) ∧[ 𝒪 X ] α V₂ (inl q₂)                       ＝⟨ refl ⟩ₚ
                             U ∧[ 𝒪 X ] U                                               ＝⟨ ∧[ 𝒪 X ]-is-idempotent U ⁻¹ ⟩ₚ
                             U                                                          ＝⟨ refl ⟩ₚ
                             α (V₁ ∧[ 𝒪 𝕊 ] V₂) (inl q)                                 ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inl q) ⟩
                             ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
                              where
                               q : (⊤ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
                               q = q₁ , q₂
    goal (inl q₁ , inr p₂) = α V₁ (inl q₁) ∧[ 𝒪 X ] α V₂ (inr p₂) ＝⟨ refl ⟩ₚ
                             U ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                  ＝⟨ 𝟏-right-unit-of-∧ (𝒪 X) U  ⟩ₚ
                             U                                   ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inl p) ⟩
                             ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
                              where
                               p : (⊤ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
                               p = q₁ , main-lemma V₂ p₂
    goal (inr p₁ , inl q₂) = {!!}
    goal (inr p₁ , inr p₂) = α V₁ (inr p₁) ∧[ 𝒪 X ] α V₂ (inr p₂)                       ＝⟨ refl ⟩ₚ
                             𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                                 ＝⟨ ∧[ 𝒪 X ]-is-idempotent 𝟏[ 𝒪 X ] ⁻¹  ⟩ₚ
                             𝟏[ 𝒪 X ]                                                   ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inr p) ⟩
                             ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
                              where
                               p : (⊥ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
                               p = p₁ , p₂
  --   goal (inl p₁ , inl p₂) = α V₁ (inl p₁) ∧[ 𝒪 X ] α V₂ (inl p₂)                       ＝⟨ refl ⟩ₚ
  --                            𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                                 ＝⟨ ∧[ 𝒪 X ]-is-idempotent 𝟏[ 𝒪 X ] ⁻¹  ⟩ₚ
  --                            𝟏[ 𝒪 X ]                                                   ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inl p) ⟩
  --                            ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
  --                             where
  --                              p : (⊤ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
  --                              p = p₁ , p₂
  --   goal (inl p₁ , inr q₂) = α V₁ (inl p₁) ∧[ 𝒪 X ] α V₂ (inr q₂)                       ＝⟨ refl ⟩ₚ
  --                            𝟏[ 𝒪 X ] ∧[ 𝒪 X ] U                                        ≤⟨ 𝟏-is-top (𝒪 X) (𝟏[ 𝒪 X ] ∧[ 𝒪 X ] U) ⟩
  --                            𝟏[ 𝒪 X ]                                                   ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inl p) ⟩
  --                            ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
  --                             where
  --                              p : (⊤ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
  --                              p = p₁ , main-lemma V₂ q₂
  --   goal (inr q₁ , inl p₂) = α V₁ (inr q₁) ∧[ 𝒪 X ] α V₂ (inl p₂) ＝⟨ refl ⟩ₚ
  --                            U ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                  ≤⟨ 𝟏-is-top (𝒪 X) (U ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]) ⟩
  --                            𝟏[ 𝒪 X ]                             ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inl p) ⟩
  --                            ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
  --                             where
  --                              p : (⊤ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
  --                              p = (main-lemma V₁ q₁) , p₂
  --   goal (inr q₁ , inr q₂) = α V₁ (inr q₁) ∧[ 𝒪 X ] α V₂ (inr q₂)                       ＝⟨ refl ⟩ₚ
  --                            U ∧[ 𝒪 X ] U                                               ＝⟨ ∧[ 𝒪 X ]-is-idempotent U ⁻¹ ⟩ₚ
  --                            U                                                          ＝⟨ refl ⟩ₚ
  --                            α (V₁ ∧[ 𝒪 𝕊 ] V₂) (inr q)                                 ≤⟨ ⋁[ 𝒪 X ]-upper ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ (inr q) ⟩
  --                            ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ■
  --                             where
  --                              q : (⊥ₛ ∈ₛ (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
  --                              q = q₁ , q₂

    ‡ : ((f V₁ ∧[ 𝒪 X ] f V₂) ≤[ poset-of (𝒪 X) ] f (V₁ ∧[ 𝒪 𝕊 ] V₂)) holds
    ‡ = f V₁ ∧[ 𝒪 X ] f V₂                               ＝⟨ refl ⟩ₚ
        f V₁ ∧[ 𝒪 X ] (⋁[ 𝒪 X ] (I V₂ , α V₂))           ＝⟨ distributivity+ (𝒪 X) (I V₁ , α V₁) (I V₂ , α V₂) ⟩ₚ
        ⋁[ 𝒪 X ] ⁅ α V₁ i₁ ∧[ 𝒪 X ] α V₂ i₂ ∣ (i₁ , i₂) ∶ I V₁ × I V₂ ⁆ ≤⟨ ⋁[ 𝒪 X ]-least (⁅ α V₁ i₁ ∧[ 𝒪 X ] α V₂ i₂ ∣ (i₁ , i₂) ∶ I V₁ × I V₂ ⁆) ((⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆) , goal)  ⟩
        ⋁[ 𝒪 X ] ⁅ α (V₁ ∧[ 𝒪 𝕊 ] V₂) i ∣ i ∶ I (V₁ ∧[ 𝒪 𝕊 ] V₂) ⁆ ＝⟨ refl ⟩ₚ
        f (V₁ ∧[ 𝒪 𝕊 ] V₂) ■

  jp : {!!}
  jp = {!!}

  𝒻 : 𝒪 𝕊 ─f→ 𝒪 X
  𝒻 = (f , tp , mp , jp)

  equality₁ : (U ≤[ poset-of (𝒪 X) ] f true) holds
  equality₁ = U ≤⟨ ⋁[ 𝒪 X ]-upper _ (inl ⋆) ⟩ f true ■

  equality₂ : (f true ≤[ poset-of (𝒪 X) ] U) holds
  equality₂ = f true ≤⟨ ⋁[ 𝒪 X ]-least (compr-syntax (I true) (λ i → α true i)) (U , †) ⟩ U ■
   where
    † : (rel-syntax (poset-of (𝒪 X)) Joins.is-an-upper-bound-of U) (I true , α true) holds
    † (inl ⋆) = ≤-is-reflexive (poset-of (𝒪 X)) U


  uniqueness : is-central (Σ (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f true) ((f , tp , mp , jp) , equality)
  uniqueness (ℊ@(g , tpg , mpg , jpg) , eq′) =
   to-subtype-＝
    (λ h → carrier-of-[ poset-of (𝒪 X) ]-is-set)
    (continuous-map-equality (𝒪 𝕊) (𝒪 X) 𝒻 ℊ goal)
     where
      goal : (V : ⟨ 𝒪 𝕊 ⟩) → f V ＝ g V
      goal V = ≤-is-antisymmetric (poset-of (𝒪 X)) goal₁ goal₂
       where
        subgoal₁ : (i : I V) → (α V i ≤[ poset-of (𝒪 X) ] g V) holds
        subgoal₁ (inl p) = α V (inl p) ＝⟨ refl ⟩ₚ U ＝⟨ eq′  ⟩ₚ g true ≤⟨ frame-morphisms-are-monotonic (𝒪 𝕊) (𝒪 X) g (tpg , mpg , jpg) (true , V) subgoal₂  ⟩ g V ■
         where
          subgoal₂ : (true ≤[ poset-of (𝒪 𝕊) ] V) holds
          subgoal₂ P μ = transport (λ - → (- ∈ₛ V) holds) (holds-gives-equal-⊤ₛ P μ ⁻¹) p
        subgoal₁ (inr p) = α V (inr p) ＝⟨ refl ⟩ₚ 𝟏[ 𝒪 X ] ＝⟨ tpg ⁻¹ ⟩ₚ g 𝟏[ 𝒪 𝕊 ] ＝⟨ ap g (contains-bottom-implies-is-top V p ⁻¹) ⟩ₚ g V ■

        goal₁ : (f V ≤[ poset-of (𝒪 X) ] g V) holds
        goal₁ = ⋁[ 𝒪 X ]-least (I V , α V) ((g V) , subgoal₁)

        goal₂ : (g V ≤[ poset-of (𝒪 X) ] f V) holds
        goal₂ = {!characterization-of-scott-opens  !}

-- --}
-- --}
-- --}

\end{code}
