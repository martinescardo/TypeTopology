--------------------------------------------------------------------------------
title:          Universal property of the Sierpiński locale
author:         Ayberk Tosun
date-started:   2024-03-06
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import MLTT.Spartan

module Locales.Sierpinski.UniversalProperty
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import Locales.DistributiveLattice.Definition fe pt
open import Locales.DistributiveLattice.Ideal pt fe pe
open import Locales.DistributiveLattice.Properties fe pt
open import Locales.Frame pt fe hiding (is-directed)
open import Locales.Sierpinski 𝓤 pe pt fe
open import Locales.ScottLocale.Definition pt fe 𝓤
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe

open AllCombinators pt fe renaming (_∧_ to _∧ₚ_; _∨_ to _∨ₚ_)
open PropositionalSubsetInclusionNotation fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

\begin{code}

open Locale

true₀ : ⟪ 𝕊-dcpo ⟫ → Ω 𝓤
true₀ (P , f , φ) = P , φ

⊤ₛ : ⟪ 𝕊-dcpo ⟫
⊤ₛ = 𝟙 , (λ _ → ⋆) , 𝟙-is-prop

⊥ₛ : ⟪ 𝕊-dcpo ⟫
⊥ₛ = 𝟘 , (λ ()) , 𝟘-is-prop

open DefnOfScottTopology (𝕊-dcpo ⁻) 𝓤

true : ⟨ 𝒪 𝕊 ⟩
true = true₀ , †
 where
  υ : is-upwards-closed true₀ holds
  υ P Q φ p = transport (λ - → true₀ - holds) (p φ) φ

  ι : is-inaccessible-by-directed-joins true₀ holds
  ι (S , δ) μ = μ

  † : is-scott-open true₀ holds
  † = υ , ι

singleton₀ : (P : Ω 𝓤) → P holds → ⟪ 𝕊-dcpo ⟫ → Ω 𝓤
singleton₀ P p (Q , f , φ) = P ⇔ (Q , φ)

singleton-is-true : ((P , f , φ) : ⟪ 𝕊-dcpo ⟫) → (p : (P , φ) holds) → true₀ ＝ singleton₀ (P , φ) p
singleton-is-true (P , f , φ) p = dfunext fe λ (Q , g , ψ) → to-subtype-＝ (λ _ → being-prop-is-prop fe) (pe ψ {!!} {!!} {!!})

contains-bottom-implies-is-top : (𝔘 : ⟨ 𝒪 𝕊 ⟩) → (⊥ₛ ∈ₛ 𝔘) holds → 𝔘 ＝ 𝟏[ 𝒪 𝕊 ]
contains-bottom-implies-is-top 𝔘 p = only-𝟏-is-above-𝟏 (𝒪 𝕊) 𝔘 †
 where
  open 𝒪ₛᴿ

  † : (𝟏[ 𝒪 𝕊 ] ≤[ poset-of (𝒪 𝕊) ] 𝔘) holds
  † x ⋆ = upward-closure 𝔘 ⊥ₛ x p λ ()

main-lemma : (U : ⟨ 𝒪 𝕊 ⟩) → (⊥ₛ ∈ₛ U ⇒ ⊤ₛ ∈ₛ U) holds
main-lemma U p = upward-closure U ⊥ₛ ⊤ₛ p λ ()
 where
  open 𝒪ₛᴿ

universal-property-of-sierpinski : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                                 → (U : ⟨ 𝒪 X ⟩)
                                 → ∃! (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f true
universal-property-of-sierpinski X U = ((f , {!!} , {!!} , {!!}) , {!!}) , {!!}
 where
  open PosetReasoning (poset-of (𝒪 X))

  I : (V : ⟨ 𝒪 𝕊 ⟩) → 𝓤  ̇
  I V = (⊤ₛ ∈ₛ V) holds + (⊥ₛ ∈ₛ V) holds

  α : (V : ⟨ 𝒪 𝕊 ⟩) → (⊤ₛ ∈ₛ V) holds + (⊥ₛ ∈ₛ V) holds → ⟨ 𝒪 X ⟩
  α V (inl _) = U
  α V (inr _) = 𝟏[ 𝒪 X ]

  f : ⟨ 𝒪 𝕊 ⟩ → ⟨ 𝒪 X ⟩
  f V = ⋁[ 𝒪 X ] (I V , α V)

{--

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

  equality : U ＝ f true
  equality = ≤-is-antisymmetric (poset-of (𝒪 X)) equality₁ equality₂

  uniqueness : is-central (Σ (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f true) ((f , tp , mp , jp) , equality)
  uniqueness (ℊ@(g , tpg , mpg , jpg) , eq′) =
   to-subtype-＝
    (λ h → carrier-of-[ poset-of (𝒪 X) ]-is-set)
    (continuous-map-equality (𝒪 𝕊) (𝒪 X) 𝒻 ℊ goal)
     where
      goal : (V : ⟨ 𝒪 𝕊 ⟩) → f V ＝ g V
      goal V = {!!}

--}

\end{code}
