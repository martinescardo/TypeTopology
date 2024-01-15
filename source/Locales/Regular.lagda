Ayberk Tosun, 13 September 2023

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import MLTT.List hiding ([_])
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Size

module Locales.Regular (pt : propositional-truncations-exist)
                       (fe : Fun-Ext)
                       (sr : Set-Replacement pt) where

\end{code}

Importation of foundational UF stuff.

\begin{code}

open import Slice.Family
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

Importations of other locale theory modules.

\begin{code}

open import Locales.Frame                         pt fe
open import Locales.WayBelowRelation.Definition   pt fe
open import Locales.Compactness                   pt fe
open import Locales.Complements                   pt fe
open import Locales.GaloisConnection              pt fe
open import Locales.InitialFrame                  pt fe
open import Locales.Spectrality.SpectralLocale    pt fe
open import Locales.SmallBasis                    pt fe sr
open import Locales.Clopen                        pt fe sr
open import Locales.WellInside                    pt fe sr
open import Locales.ScottContinuity               pt fe sr

open Locale

\end{code}

Definition of regularity of a frame.

\begin{code}

is-regular₀ : (F : Frame 𝓤 𝓥 𝓦) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
is-regular₀ {𝓤 = 𝓤} {𝓥} {𝓦} F =
 let
  open Joins (λ U V → U ≤[ poset-of F ] V)

  P : Fam 𝓦 ⟨ F ⟩ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
  P ℬ = Π U ꞉ ⟨ F ⟩ ,
         Σ J ꞉ Fam 𝓦 (index ℬ) ,
            (U is-lub-of ⁅ ℬ [ j ] ∣ j ε J ⁆) holds
          × (Π i ꞉ index J , (ℬ [ J [ i ] ] ⋜[ F ] U) holds)
 in
  Σ ℬ ꞉ Fam 𝓦 ⟨ F ⟩ , P ℬ

\end{code}

\begin{code}

is-regular : (F : Frame 𝓤 𝓥 𝓦) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-regular {𝓤 = 𝓤} {𝓥} {𝓦} F = ∥ is-regular₀ F ∥Ω

\end{code}

\begin{code}

is-regular-basis : (F : Frame 𝓤 𝓥 𝓦)
                 → (ℬ : Fam 𝓦 ⟨ F ⟩) → (β : is-basis-for F ℬ) → Ω (𝓤 ⊔ 𝓦)
is-regular-basis F ℬ β =
 Ɐ U ꞉ ⟨ F ⟩ , let 𝒥 = pr₁ (β U) in Ɐ j ꞉ (index 𝒥) , ℬ [ 𝒥 [ j ] ] ⋜[ F ] U

\end{code}

\begin{code}

𝟎-is-well-inside-anything : (F : Frame 𝓤 𝓥 𝓦) (U : ⟨ F ⟩)
                          → (𝟎[ F ] ⋜[ F ] U) holds
𝟎-is-well-inside-anything F U =
 ↑↑-is-upwards-closed F ∣ 𝟎-is-clopen F ∣ (𝟎-is-bottom F U)

well-inside-is-join-stable : (F : Frame 𝓤 𝓥 𝓦) {U₁ U₂ V : ⟨ F ⟩}
                           → (U₁ ⋜[ F ] V) holds
                           → (U₂ ⋜[ F ] V) holds
                           → ((U₁ ∨[ F ] U₂) ⋜[ F ] V) holds
well-inside-is-join-stable F {U₁} {U₂} {V} =
 ∥∥-rec₂ (holds-is-prop ((U₁ ∨[ F ] U₂) ⋜[ F ] V)) γ
  where
   open PosetReasoning (poset-of F)

   γ : U₁ ⋜₀[ F ] V → U₂ ⋜₀[ F ] V → ((U₁ ∨[ F ] U₂) ⋜[ F ] V) holds
   γ (W₁ , c₁ , d₁) (W₂ , c₂ , d₂) = ∣ (W₁ ∧[ F ] W₂) , c , d ∣
    where
     δ : (W₁ ∧[ F ] W₂) ∧[ F ] U₂ ＝ 𝟎[ F ]
     δ = (W₁ ∧[ F ] W₂) ∧[ F ] U₂  ＝⟨ (∧[ F ]-is-associative W₁ W₂ U₂) ⁻¹ ⟩
         W₁ ∧[ F ] (W₂ ∧[ F ] U₂)  ＝⟨ †                                   ⟩
         W₁ ∧[ F ] (U₂ ∧[ F ] W₂)  ＝⟨ ap (λ - → meet-of F W₁ -) c₂        ⟩
         W₁ ∧[ F ] 𝟎[ F ]          ＝⟨ 𝟎-right-annihilator-for-∧ F W₁      ⟩
         𝟎[ F ]                    ∎
          where
           † = ap (λ - → W₁ ∧[ F ] -) (∧[ F ]-is-commutative W₂ U₂)

     ε : ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ＝ 𝟎[ F ]
     ε = (W₁ ∧[ F ] W₂) ∧[ F ] U₁  ＝⟨ †                                   ⟩
         (W₂ ∧[ F ] W₁) ∧[ F ] U₁  ＝⟨ (∧[ F ]-is-associative W₂ W₁ U₁) ⁻¹ ⟩
         W₂ ∧[ F ] (W₁ ∧[ F ] U₁)  ＝⟨ ‡                                   ⟩
         W₂ ∧[ F ] (U₁ ∧[ F ] W₁)  ＝⟨ ap (λ - → W₂ ∧[ F ] -) c₁           ⟩
         W₂ ∧[ F ] 𝟎[ F ]          ＝⟨ 𝟎-right-annihilator-for-∧ F W₂      ⟩
         𝟎[ F ]                    ∎
          where
           † = ap (λ - → - ∧[ F ] U₁) (∧[ F ]-is-commutative W₁ W₂)
           ‡ = ap (λ - → W₂ ∧[ F ] -) (∧[ F ]-is-commutative W₁ U₁)

     c : ((U₁ ∨[ F ] U₂) ∧[ F ] (W₁ ∧[ F ] W₂)) ＝ 𝟎[ F ]
     c = (U₁ ∨[ F ] U₂) ∧[ F ] (W₁ ∧[ F ] W₂)                          ＝⟨ i    ⟩
         (W₁ ∧[ F ] W₂) ∧[ F ] (U₁ ∨[ F ] U₂)                          ＝⟨ ii   ⟩
         ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ∨[ F ] ((W₁ ∧[ F ] W₂) ∧[ F ] U₂)  ＝⟨ iii  ⟩
         ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ∨[ F ] 𝟎[ F ]                      ＝⟨ iv   ⟩
         (W₁ ∧[ F ] W₂) ∧[ F ] U₁                                      ＝⟨ ε    ⟩
         𝟎[ F ]                                                        ∎
          where
           i   = ∧[ F ]-is-commutative (U₁ ∨[ F ] U₂) (W₁ ∧[ F ] W₂)
           ii  = binary-distributivity F (W₁ ∧[ F ] W₂) U₁ U₂
           iii = ap (λ - → ((W₁ ∧[ F ] W₂) ∧[ F ] U₁) ∨[ F ] -) δ
           iv  = 𝟎-left-unit-of-∨ F ((W₁ ∧[ F ] W₂) ∧[ F ] U₁)

     d : V ∨[ F ] (W₁ ∧[ F ] W₂) ＝ 𝟏[ F ]
     d = V ∨[ F ] (W₁ ∧[ F ] W₂)            ＝⟨ i   ⟩
         (V ∨[ F ] W₁) ∧[ F ] (V ∨[ F ] W₂) ＝⟨ ii  ⟩
         𝟏[ F ] ∧[ F ] (V ∨[ F ] W₂)        ＝⟨ iii ⟩
         𝟏[ F ] ∧[ F ] 𝟏[ F ]               ＝⟨ iv  ⟩
         𝟏[ F ] ∎
          where
           i   = binary-distributivity-op F V W₁ W₂
           ii  = ap (λ - → - ∧[ F ] (V ∨[ F ] W₂)) d₁
           iii = ap (λ - → 𝟏[ F ] ∧[ F ] -) d₂
           iv  = 𝟏-right-unit-of-∧ F 𝟏[ F ]


directification-preserves-regularity : (F : Frame 𝓤 𝓥 𝓦)
                                     → (ℬ : Fam 𝓦 ⟨ F ⟩)
                                     → (β : is-basis-for F ℬ)
                                     → is-regular-basis F ℬ β holds
                                     → let
                                        ℬ↑ = directify F ℬ
                                        β↑ = directified-basis-is-basis F ℬ β
                                       in
                                        is-regular-basis F ℬ↑ β↑ holds
directification-preserves-regularity F ℬ β r U = γ
 where
  ℬ↑ = directify F ℬ
  β↑ = directified-basis-is-basis F ℬ β

  𝒥  = pr₁ (β U)
  𝒥↑ = pr₁ (β↑ U)

  γ : (Ɐ js ꞉ index 𝒥↑ , ℬ↑ [ 𝒥↑ [ js ] ] ⋜[ F ] U) holds
  γ []       = 𝟎-is-well-inside-anything F U
  γ (j ∷ js) = well-inside-is-join-stable F (r U j) (γ js)

≪-implies-⋜-in-regular-frames : (F : Frame 𝓤 𝓥 𝓦)
                              → (is-regular F) holds
                              → (U V : ⟨ F ⟩)
                              → (U ≪[ F ] V ⇒ U ⋜[ F ] V) holds
≪-implies-⋜-in-regular-frames {𝓦 = 𝓦} F r U V =
 ∥∥-rec (holds-is-prop (U ≪[ F ] V ⇒ U ⋜[ F ] V)) γ r
  where
   γ : is-regular₀ F → (U ≪[ F ] V ⇒ U ⋜[ F ] V) holds
   γ (ℬ , δ) κ = ∥∥-rec (holds-is-prop (U ⋜[ F ] V)) ζ (κ S ε c)
    where
     ℬ↑ : Fam 𝓦 ⟨ F ⟩
     ℬ↑ = directify F ℬ

     β : is-basis-for F ℬ
     β U = pr₁ (δ U) , pr₁ (pr₂ (δ U))

     β↑ : is-basis-for F ℬ↑
     β↑ = directified-basis-is-basis F ℬ β

     ρ : is-regular-basis F ℬ β holds
     ρ U = pr₂ (pr₂ (δ U))

     ρ↑ : is-regular-basis F ℬ↑ β↑ holds
     ρ↑ =  directification-preserves-regularity F ℬ β ρ

     𝒥 : Fam 𝓦 (index ℬ↑)
     𝒥 = pr₁ (β↑ V)

     S : Fam 𝓦 ⟨ F ⟩
     S = ⁅ ℬ↑ [ i ] ∣ i ε 𝒥 ⁆

     ε : is-directed F S holds
     ε = covers-of-directified-basis-are-directed F ℬ β V

     c : (V ≤[ poset-of F ] (⋁[ F ] S)) holds
     c = reflexivity+ (poset-of F) (⋁[ F ]-unique S V (pr₂ (β↑ V)))

     ζ : Σ k ꞉ index S , (U ≤[ poset-of F ] (S [ k ])) holds → (U ⋜[ F ] V) holds
     ζ (k , q) = ↓↓-is-downwards-closed F (ρ↑ V k) q

\end{code}

\begin{code}

compacts-are-clopen-in-regular-frames : (X : Locale 𝓤 𝓥 𝓦)
                                      → is-regular (𝒪 X) holds
                                      → (Ɐ U ꞉ ⟨ 𝒪 X ⟩ ,
                                          is-compact-open X U ⇒ is-clopen (𝒪 X) U) holds
compacts-are-clopen-in-regular-frames X r U =
 well-inside-itself-implies-clopen X U ∘ ≪-implies-⋜-in-regular-frames (𝒪 X) r U U

\end{code}
