Ayberk Tosun, 12 September 2023

Split out from the now-deprecated `CompactRegular` module.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size

module Locales.WellInside (pt : propositional-truncations-exist)
                          (fe : Fun-Ext)
                          (sr : Set-Replacement pt)                where

\end{code}

Importation of foundational UF stuff.

\begin{code}

open import UF.SubtypeClassifier
open import UF.Logic

open import Locales.Frame       pt fe

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

\begin{code}

well-inside₀ : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → 𝓤 ̇
well-inside₀ F U V =
 Σ W ꞉ ⟨ F ⟩ , (U ∧[ F ] W ＝ 𝟎[ F ]) × (V ∨[ F ] W ＝ 𝟏[ F ])

infix 4 well-inside₀

syntax well-inside₀ F U V = U ⋜₀[ F ] V

\end{code}

Because well inside is not propositional, we have to truncate it to get a
relation.

\begin{code}

well-inside : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → Ω 𝓤
well-inside F U V = ∥ U ⋜₀[ F ] V ∥Ω

infix 4 well-inside

syntax well-inside F U V = U ⋜[ F ] V

\end{code}

Proposition. Let `U, V : 𝒪(X)`. If `U ⋜ V` then `U ≤ V`.

\begin{code}

well-inside-implies-below : (F : Frame 𝓤 𝓥 𝓦)
                          → (U V : ⟨ F ⟩)
                          → (U ⋜[ F ] V ⇒ (U ≤[ poset-of F ] V)) holds
well-inside-implies-below F U V = ∥∥-rec (holds-is-prop (U ≤[ poset-of F ] V)) γ
 where
  _⊓_ = λ (U V : ⟨ F ⟩) → U ∧[ F ] V

  γ : U ⋜₀[ F ] V → (U ≤[ poset-of F ] V) holds
  γ (W , c₁ , c₂) = connecting-lemma₂ F δ
   where
    δ : U ＝ U ∧[ F ] V
    δ = U                        ＝⟨ 𝟏-right-unit-of-∧ F U ⁻¹              ⟩
        U ⊓ 𝟏[ F ]               ＝⟨ ap (U ⊓_) (c₂ ⁻¹)                     ⟩
        U ⊓ (V ∨[ F ] W)         ＝⟨ binary-distributivity F U V W         ⟩
        (U ⊓ V) ∨[ F ] (U ⊓ W)   ＝⟨ ap (λ - → binary-join F (U ⊓ V) -) c₁ ⟩
        (U ⊓ V) ∨[ F ] 𝟎[ F ]    ＝⟨ 𝟎-left-unit-of-∨ F (U ⊓ V)            ⟩
        U ⊓ V                    ∎

\end{code}

The set `↑↑(U) ≡ { V ∣ U ⋜ V}` is upwards-closed.

\begin{code}

↑↑-is-upwards-closed : (F : Frame 𝓤 𝓥 𝓦)
                     → {U V W : ⟨ F ⟩}
                     → (U ⋜[ F ] V) holds
                     → (V ≤[ poset-of F ] W) holds
                     → (U ⋜[ F ] W) holds
↑↑-is-upwards-closed F {U} {V} {W} p q =
 ∥∥-rec (holds-is-prop (U ⋜[ F ] W)) γ p
  where
   open PosetReasoning (poset-of F)

   γ : U ⋜₀[ F ] V → (U ⋜[ F ] W) holds
   γ (T , c₁ , c₂) = ∣ T , c₁ , d₂ ∣
    where
     β : (𝟏[ F ] ≤[ poset-of F ] (W ∨[ F ] T)) holds
     β = 𝟏[ F ]      ＝⟨ c₂ ⁻¹                  ⟩ₚ
         V ∨[ F ] T  ≤⟨ ∨[ F ]-left-monotone q ⟩
         W ∨[ F ] T  ■

     d₂ : W ∨[ F ] T ＝ 𝟏[ F ]
     d₂ = only-𝟏-is-above-𝟏 F (W ∨[ F ] T) β

\end{code}

The set `↓↓(U) ≡ { V | V ⋜ U}` is downwards-closed.

\begin{code}

↓↓-is-downwards-closed : (F : Frame 𝓤 𝓥 𝓦)
                       → {U V W : ⟨ F ⟩}
                       → (V ⋜[ F ] W) holds
                       → (U ≤[ poset-of F ] V) holds
                       → (U ⋜[ F ] W) holds
↓↓-is-downwards-closed F {U} {V} {W} p q = ∥∥-rec ∥∥-is-prop γ p
 where
  open PosetReasoning (poset-of F)

  γ : V ⋜₀[ F ] W → (U ⋜[ F ] W) holds
  γ (T , c₁ , c₂) = ∣ T , (only-𝟎-is-below-𝟎 F (U ∧[ F ] T) β , c₂) ∣
   where
    β : ((U ∧[ F ] T) ≤[ poset-of F ] 𝟎[ F ]) holds
    β = U ∧[ F ] T  ≤⟨ ∧[ F ]-left-monotone q ⟩
        V ∧[ F ] T  ＝⟨ c₁                    ⟩ₚ
        𝟎[ F ]      ■

\end{code}
