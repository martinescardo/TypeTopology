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

universal-property-of-sierpinski : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                                 → (U : ⟨ 𝒪 X ⟩)
                                 → ∃! (f , _) ꞉ (𝒪 𝕊 ─f→ 𝒪 X) , U ＝ f true
universal-property-of-sierpinski X U = ((f , α , β , {!!}) , {!!}) , {!!}
 where
  open PosetReasoning (poset-of (𝒪 X))

  fam : (V : ⟨ 𝒪 𝕊 ⟩) → (⊤ₛ ∈ₛ V) holds + (⊥ₛ ∈ₛ V) holds → ⟨ 𝒪 X ⟩
  fam V (inl _) = 𝟏[ 𝒪 X ]
  fam V (inr _) = U

  f : ⟨ 𝒪 𝕊 ⟩ → ⟨ 𝒪 X ⟩
  f V = ⋁[ 𝒪 X ] (_ , fam V)

  -- f (⋁ S) ＝ ⋁ ⁅ f P ∣ P ε S ⁆
  -- f (⋁ ⁅ ↑c ∣ c ε S, c ∈ Ω ⁆) ＝ ⋁ ⁅ f(↑c) ∣ c ε S, c ∈ Ω ⁆
  -- f true ∨ f false
  -- f 1 = 1
  -- f (x ∧ y) ＝ f x ∧ f y

  fₘ : is-monotonic (poset-of (𝒪 𝕊)) (poset-of (𝒪 X)) f holds
  fₘ (V₁ , V₂) p = ⋁[ 𝒪 X ]-least (_ , fam V₁) ({!!} , {!!})

  α : f 𝟏[ 𝒪 𝕊 ] ＝ 𝟏[ 𝒪 X ]
  α = only-𝟏-is-above-𝟏 (𝒪 X) (f 𝟏[ 𝒪 𝕊 ]) †
   where
    † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f 𝟏[ 𝒪 𝕊 ]) holds
    † = ⋁[ 𝒪 X ]-upper (_ , fam 𝟏[ 𝒪 𝕊 ]) (inl ⋆)

  β : (U V : ⟨ 𝒪 𝕊 ⟩) → f (U ∧[ 𝒪 𝕊 ] V) ＝ f U ∧[ 𝒪 X ] f V
  β U V = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
   where
    † : rel-syntax (poset-of (𝒪 X)) (f (U ∧[ 𝒪 𝕊 ] V)) ((f U) ∧[ 𝒪 X ] (f V)) holds
    † = ∧[ 𝒪 X ]-greatest (f U) (f V) (f (U ∧[ 𝒪 𝕊 ] V)) {!!} {!!}

    ‡ : {!!}
    ‡ = {!!}

\end{code}
