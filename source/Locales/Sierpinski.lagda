---
title:          The Sierpiński locale and its patch
author:         Ayberk Tosun
date-completed: 2024-02-12
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Size hiding (is-locally-small)

module Locales.Sierpinski
        (𝓤  : Universe)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt) where

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.Basics.Dcpo    pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤 renaming (⊥ to ⊥∙)
open import DomainTheory.Basics.WayBelow pt fe 𝓤
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓤
open import Lifting.Lifting 𝓤
open import Lifting.Miscelanea-PropExt-FunExt 𝓤 pe fe
open import Lifting.UnivalentPrecategory 𝓤 (𝟙 {𝓤})
open import Locales.Frame pt fe hiding (𝟚; is-directed)
open import Locales.InitialFrame pt fe
open import Locales.SmallBasis pt fe sr
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap pt fe
open import Locales.Stone pt fe sr
open import Slice.Family
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open Locale

open PropositionalTruncation pt

\end{code}

We first define the Sierpinski domain

\begin{code}

𝕊𝓓⁺ : DCPO {𝓤 ⁺ } {𝓤 ⁺}
𝕊𝓓⁺ = 𝓛-DCPO {X = 𝟙 {𝓤}} 𝟙-is-set

\end{code}

which is locally small and also algebraic:

\begin{code}

𝕊-is-locally-small : is-locally-small 𝕊𝓓⁺
𝕊-is-locally-small = 𝓛-is-locally-small {X = 𝟙 {𝓤}} 𝟙-is-set

𝕊𝓓⁺-is-algebraic : is-algebraic-dcpo (𝓛-DCPO {X = 𝟙 {𝓤}} 𝟙-is-set)
𝕊𝓓⁺-is-algebraic = 𝓛-is-algebraic-dcpo 𝟙-is-set

\end{code}

Unfortunately, we do not have the required machinery for making a locally small
copy of a dcpo from an extrinsic proof that it is locally small. In hindsight,
it would have been easier for me to work with such extrinsic proofs of local
smallness, but I didn't do this and right now, I don't have the time to migrate
my formalization to this style.

Therefore, I defined the function `𝓛-DCPO⁻` which directly gives the locally
small copy of the dcpo in consideration. Instead of working with `𝕊𝓓⁺`, I work
with `𝕊𝓓` instead to circumvent this problem.

\begin{code}

𝕊𝓓 : DCPO {𝓤 ⁺} {𝓤}
𝕊𝓓 = 𝓛-DCPO⁻ {X = 𝟙 {𝓤}} 𝟙-is-set

\end{code}

These two dcpos are of course order-isomorphic.

\begin{code}

⊑-implies-⊑⁺ : (x y : ⟨ 𝕊𝓓 ⟩∙) → x ⊑⟨ 𝕊𝓓 ⟩ y → x ⊑⟨ 𝕊𝓓⁺ ⟩ y
⊑-implies-⊑⁺ x y p q = ⊑-to-⊑' p q

⊑⁺-implies-⊑ : (x y : ⟨ 𝕊𝓓 ⟩∙) → x ⊑⟨ 𝕊𝓓⁺ ⟩ y → x ⊑⟨ 𝕊𝓓 ⟩ y
⊑⁺-implies-⊑ x y p = (λ q → transport is-defined (p q) q) , λ _ → refl

\end{code}

The proposition `𝟘` is the bottom element of this dcpo, meaning it can be
made into a pointed dcpo:

\begin{code}

𝕊𝓓⊥ : DCPO⊥ {𝓤 ⁺} {𝓤}
𝕊𝓓⊥ = 𝕊𝓓 , (𝟘 , (λ ()) , 𝟘-is-prop) , λ _ → (λ ()) , λ ()

\end{code}

The proposition `𝟙` is a top element of this dcpo.

\begin{code}

𝟙-is-top : (x : ⟨ 𝕊𝓓 ⟩∙) → x ⊑⟨ 𝕊𝓓 ⟩ η ⋆
𝟙-is-top (P , q) = (λ _ → ⋆) , λ _ → refl

\end{code}

Furthermore, the dcpo `𝕊𝓓` is compact.

\begin{code}

𝕊𝓓-is-compact : is-compact 𝕊𝓓 (η ⋆)
𝕊𝓓-is-compact I α (∣i∣ , up⁻) p⁻ =
 ∥∥-rec ∃-is-prop † (ηs-are-compact 𝟙-is-set ⋆ I α δ p)
  where
   open is-locally-small 𝕊-is-locally-small

   up : is-semidirected (underlying-order 𝕊𝓓⁺) α
   up i j = ∥∥-rec ∃-is-prop † (up⁻ i j)
    where
     † : Σ k ꞉ I , (α i ⊑⟨ 𝕊𝓓  ⟩ α k) × (α j ⊑⟨ 𝕊𝓓  ⟩ α k)
       → ∃ k ꞉ I , (α i ⊑⟨ 𝕊𝓓⁺ ⟩ α k) × (α j ⊑⟨ 𝕊𝓓⁺ ⟩ α k)
     † (k , p , q) = ∣ k , ⊑-implies-⊑⁺ (α i) (α k) p  , ⊑-implies-⊑⁺ (α j) (α k) q ∣

   δ : is-directed (underlying-order 𝕊𝓓⁺) α
   δ = ∣i∣ , up

   p : η ⋆ ⊑⟨ 𝕊𝓓⁺ ⟩ (∐ (𝓛-DCPO 𝟙-is-set) δ)
   p = ⊑-to-⊑' (pr₁ p⁻ , λ _ → refl)

   † : Σ i ꞉ I , underlying-order (𝓛-DCPO 𝟙-is-set) (η ⋆) (α i)
     → ∃ i ꞉ I , η ⋆ ⊑⟨ 𝕊𝓓 ⟩ (α i)
   † (i , q) = ∣ i , ⊑⁺-implies-⊑ (η ⋆) (α i) q ∣

\end{code}

We define a function for mapping inhabitants of the Sierpiński dcpo to the type
of propositions:

\begin{code}

to-Ω : ⟨ 𝕊𝓓 ⟩∙ → Ω 𝓤
to-Ω (P , _ , h) = P , h

\end{code}

Conversely, we define a function mapping every proposition `P : Ω 𝓤` to the
carrier set of the Sierpiński dcpo.

\begin{code}

to-𝕊𝓓 : Ω 𝓤 →  ⟨ 𝕊𝓓 ⟩∙
to-𝕊𝓓 (P , h) = P , (λ _ → ⋆) , h

\end{code}

It is obvious that these form an equivalence.

\begin{code}

Ω-equivalent-to-𝕊 : Ω 𝓤 ≃ ⟨ 𝕊𝓓 ⟩∙
Ω-equivalent-to-𝕊 = to-𝕊𝓓 , ((to-Ω , †) , (to-Ω , ‡))
 where
  ψ : {A : 𝓤  ̇} → is-prop (A → 𝟙)
  ψ = Π-is-prop fe (λ _ → 𝟙-is-prop)

  ϑ : {A : 𝓤  ̇} → is-prop (is-prop A)
  ϑ = being-prop-is-prop fe

  † : (to-𝕊𝓓 ∘ to-Ω) ∼ id
  † (P , f , h) = to-subtype-＝ (λ _ → ×-is-prop ψ ϑ) refl

  ‡ : to-Ω ∘ to-𝕊𝓓 ∼ id
  ‡ (P , h) = to-subtype-＝ (λ _ → ϑ) refl

\end{code}

We now proceed to the definition of the Sierpiński locale.

First, we show that `𝕊𝓓` has a specified small compact basis.


\begin{code}

open import Locales.ScottLocale.Definition pt fe 𝓤
open import Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos pt fe 𝓤

hscb : has-specified-small-compact-basis 𝕊𝓓
hscb = (𝟙 {𝓤} + 𝟙 {𝓤}) , β , σ
 where
  β : 𝟙 + 𝟙 → ⟨ 𝕊𝓓 ⟩∙
  β (inl ⋆) = ⊥∙ (𝓛-DCPO⊥ 𝟙-is-set)
  β (inr ⋆) = 𝟙 {𝓤} , (λ { ⋆ → ⋆ }) , 𝟙-is-prop

  β-is-compact : (b : 𝟙 + 𝟙) → is-compact 𝕊𝓓 (β b)
  β-is-compact (inl ⋆) = ⊥-is-compact 𝕊𝓓⊥
  β-is-compact (inr ⋆) = 𝕊𝓓-is-compact

  β-is-upward-directed : (x : ⟨ 𝕊𝓓 ⟩∙)
                       → is-semidirected (underlying-order 𝕊𝓓) (↓-inclusion 𝕊𝓓 β x)
  β-is-upward-directed x (inl ⋆ , p) (z , q)  = let
                                                 u = (z , q)
                                                 r₁ = reflexivity 𝕊𝓓 (β (inl ⋆))
                                                 r₂ = reflexivity 𝕊𝓓 (β z)
                                                in
                                                 ∣ u , ⊥-is-least 𝕊𝓓⊥ (β z) , r₂ ∣
  β-is-upward-directed x (inr ⋆ , p₁) (z , q) = let
                                                 r₁ = reflexivity 𝕊𝓓 (β (inr ⋆))
                                                 r₂ = reflexivity 𝕊𝓓 (β (inr ⋆))
                                                in
                                                 ∣ (inr ⋆ , p₁) , r₁ , 𝟙-is-top (β z) ∣

  covering : (x : ⟨ 𝕊𝓓 ⟩∙) → is-sup (underlying-order 𝕊𝓓) x (↓-inclusion 𝕊𝓓 β x)
  covering 𝒫@(P , f , h) = pr₂ , †
   where
    † : is-lowerbound-of-upperbounds (underlying-order 𝕊𝓓) (P , f , h) (↓-inclusion 𝕊𝓓 β (P , f , h))
    † 𝒫′@(P′ , f′ , h′) υ = ‡
     where
      ♠ : P → 𝒫 ⊑⟨ 𝕊𝓓 ⟩ 𝒫′
      ♠ p = transport (λ - → - ⊑⟨ 𝕊𝓓 ⟩ 𝒫′) eq (υ (inr ⋆ , q))
       where
        q : β (inr ⋆) ⊑⟨ 𝕊𝓓 ⟩ 𝒫
        q = (λ _ → p) , λ _ → 𝟙-is-prop ⋆ (f p)

        eq : β (inr ⋆) ＝ 𝒫
        eq = antisymmetry 𝕊𝓓 (β (inr ⋆)) 𝒫 q (𝟙-is-top 𝒫)

      ‡ : underlying-order 𝕊𝓓 (P , f , h) 𝒫′
      ‡ = (λ p → pr₁ (♠ p) p) , λ p → 𝟙-is-prop ⋆ (f p)

  σ : is-small-compact-basis 𝕊𝓓 β
  σ = record
       { basis-is-compact = β-is-compact
       ; ⊑ᴮ-is-small = λ x b → (β b ⊑⟨ 𝕊𝓓 ⟩ x) , ≃-refl (β b ⊑⟨ 𝕊𝓓 ⟩ x)
       ; ↓ᴮ-is-directed = λ x → ∣ inl ⋆ , ⊥-is-least 𝕊𝓓⊥ x ∣ , β-is-upward-directed x
       ; ↓ᴮ-is-sup = covering
       }

\end{code}

Using this compact basis, we define the Sierpiński locale as the Scott locale of
`𝕊𝓓`.

\begin{code}

open ScottLocaleConstruction 𝕊𝓓 hscb pe

𝕊 : Locale (𝓤 ⁺) 𝓤 𝓤
𝕊 = ScottLocale

\end{code}

The true truth value in the Sierpiński space i.e. its only nontrivial open.

\begin{code}

open DefnOfScottLocale 𝕊𝓓 𝓤 pe

⊤𝕊 : ⟨ 𝒪 𝕊 ⟩
⊤𝕊 = ⊤ₛ

\end{code}

We now show that `𝕊𝓓` is a Scott domain. We have already shown that it is an
algebraic lattice, so it remains to show that it is bounded complete.

\begin{code}

open import DomainTheory.BasesAndContinuity.ScottDomain pt fe 𝓤

open DefinitionOfBoundedCompleteness

⊑₀-implies-⊑ : (x y : ⟨ 𝕊𝓓 ⟩∙)
             → x ⊑⟨ 𝕊𝓓 ⟩ y
             → (to-Ω x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] to-Ω y) holds
⊑₀-implies-⊑ _ _ (g , q) p = g p

⊑-implies-⊑₀ : (x y : ⟨ 𝕊𝓓 ⟩∙)
             → (to-Ω x ≤[ poset-of (𝟎-𝔽𝕣𝕞 pe) ] to-Ω y) holds
             → x ⊑⟨ 𝕊𝓓 ⟩ y
⊑-implies-⊑₀ (P , f , h) (P′ , f′ , h′) p = p , (λ _ → 𝟙-is-prop ⋆ ⋆)

𝕊𝓓-bounded-complete : bounded-complete 𝕊𝓓 holds
𝕊𝓓-bounded-complete S _ = sup , φ
 where
  S₀ : Fam 𝓤 (Ω 𝓤)
  S₀ = ⁅ to-Ω P ∣ P ε S ⁆

  sup₀ : Ω 𝓤
  sup₀ = ⋁[ (𝟎-𝔽𝕣𝕞 pe) ] S₀

  sup : ⟨ 𝕊𝓓 ⟩∙
  sup = sup₀ holds , (λ _ → ⋆) , ∃-is-prop

  υ : is-upperbound (underlying-order 𝕊𝓓) sup (S [_])
  υ i = † , ‡
   where
    † : is-defined (S [ i ]) → is-defined sup
    † p = ∣ i , p ∣

    ‡ : value (S [ i ]) ∼ (λ x₁ → value sup († x₁))
    ‡ _ = 𝟙-is-prop ⋆ ⋆

  ϑ : is-lowerbound-of-upperbounds (underlying-order 𝕊𝓓) sup (S [_])
  ϑ (P , f , h) q = ⊑-implies-⊑₀ sup (P , f , h) (⋁[ 𝟎-𝔽𝕣𝕞 pe ]-least S₀ ((P , h) , (λ i → pr₁ (q i))))

  φ : is-sup (underlying-order 𝕊𝓓) sup (S [_])
  φ = υ , ϑ

\end{code}

Finally, we show that `𝕊𝓓` trivially satisfies the decidability condition that
we assume in the proof that Scott locales of Scott domains are spectral.

\begin{code}

open import Locales.ScottLocale.ScottLocalesOfScottDomains pt fe sr 𝓤

𝕊𝓓-satisfies-dc : decidability-condition 𝕊𝓓
𝕊𝓓-satisfies-dc 𝒫₀@(P₀ , h₀ , f₀) 𝒫₁@(P₁ , h₁ , f₁) κc κd =
 inl ∣ up , ‡ ∣
  where
   up : ⟨ 𝕊𝓓 ⟩∙
   up = to-𝕊𝓓 (to-Ω 𝒫₀ ∨[ 𝟎-𝔽𝕣𝕞 pe ] to-Ω 𝒫₁)

   open Joins {A = ⟨ 𝕊𝓓 ⟩∙} (λ x y → (x ⊑⟨ 𝕊𝓓 ⟩ y) , prop-valuedness 𝕊𝓓 x y)

   ‡ : (up is-an-upper-bound-of (binary-family 𝓤 𝒫₀ 𝒫₁)) holds
   ‡ (inl ⋆) = (λ p → ∣ inl ⋆ , p ∣) , λ _ → 𝟙-is-prop ⋆ ⋆
   ‡ (inr ⋆) = (λ p → ∣ inr ⋆ , p ∣) , λ _ → 𝟙-is-prop ⋆ ⋆

\end{code}

From all these, we obtain the fact that `𝕊` is a spectral locale.

\begin{code}

𝕊𝓓-has-least : has-least (underlying-order 𝕊𝓓)
𝕊𝓓-has-least = (⊥∙ 𝕊𝓓⊥) , ⊥-is-least 𝕊𝓓⊥

open SpectralScottLocaleConstruction 𝕊𝓓 𝕊𝓓-has-least hscb 𝕊𝓓-satisfies-dc 𝕊𝓓-bounded-complete pe

𝕊-is-spectralᴰ : spectralᴰ 𝕊
𝕊-is-spectralᴰ = σᴰ

open import Locales.PatchLocale pt fe sr

𝕊-is-spectral : is-spectral 𝕊 holds
𝕊-is-spectral = spectralᴰ-gives-spectrality 𝕊 σᴰ

𝕊-has-small-𝒦 : has-small-𝒦 𝕊
𝕊-has-small-𝒦 = spectralᴰ-implies-small-𝒦 𝕊 σᴰ

open SmallPatchConstruction 𝕊 𝕊-is-spectralᴰ renaming (SmallPatch to Patch-𝕊)

\end{code}

We conclude by constructing the patch of Sierpiński.

\begin{code}

patch-of-𝕊 : Locale (𝓤 ⁺) 𝓤 𝓤
patch-of-𝕊 = Patch-𝕊

\end{code}

The universal property of Patch then specializes to the following.

\begin{code}

open import Locales.UniversalPropertyOfPatch pt fe sr

open import Locales.PatchProperties pt fe sr

open ClosedNucleus 𝕊 𝕊-is-spectral

ump-for-patch-of-𝕊 : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
                   → is-stone X holds
                   → (𝒻@(f , _) : X ─c→ 𝕊)
                   → is-spectral-map 𝕊 X 𝒻 holds
                   → ∃! 𝒻⁻@(f⁻ , _) ꞉ X ─c→ Patch-𝕊 ,
                      ((U : ⟨ 𝒪 𝕊 ⟩) → f U ＝ f⁻ ‘ U ’)
ump-for-patch-of-𝕊 = ump-of-patch 𝕊 𝕊-is-spectral 𝕊-has-small-𝒦

\end{code}
