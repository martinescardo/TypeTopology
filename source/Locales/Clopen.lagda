Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.UA-FunExt

module Locales.Clopen (pt : propositional-truncations-exist)
                      (fe : Fun-Ext)                           where

open import Locales.AdjointFunctorTheoremForFrames
open import Locales.Frame pt fe
open import Locales.WayBelow pt fe
open import Locales.Compactness pt fe
open import Locales.Complements pt fe
open import Slice.Family
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier

open AllCombinators pt fe
open PropositionalTruncation pt

open import Locales.GaloisConnection pt fe

open import Locales.InitialFrame pt fe

open Locale

\end{code}

We define the notion of a clopen.

\begin{code}

is-clopen₀ : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → 𝓤 ̇
is-clopen₀ F U = Σ W ꞉ ⟨ F ⟩ , is-boolean-complement-of F W U holds

is-clopen₀-is-prop : (F : Frame 𝓤 𝓥 𝓦) → (U : ⟨ F ⟩) → is-prop (is-clopen₀ F U)
is-clopen₀-is-prop F U (W₁ , p₁ , q₁) (W₂ , p₂ , q₂) = to-subtype-＝ β γ
 where
  P = poset-of F -- we refer to the underlying poset of F as P.

  β : (W : ⟨ F ⟩) → is-prop ((U ∧[ F ] W ＝ 𝟎[ F ]) × (U ∨[ F ] W ＝ 𝟏[ F ]))
  β W = ×-is-prop carrier-of-[ P ]-is-set carrier-of-[ P ]-is-set

  γ : W₁ ＝ W₂
  γ = W₁                                  ＝⟨ (𝟏-right-unit-of-∧ F W₁) ⁻¹       ⟩
      W₁ ∧[ F ] 𝟏[ F ]                    ＝⟨ ap (λ - → meet-of F W₁ -) (q₂ ⁻¹) ⟩
      W₁ ∧[ F ] (U ∨[ F ] W₂)             ＝⟨ binary-distributivity F W₁ U W₂   ⟩
      (W₁ ∧[ F ] U) ∨[ F ] (W₁ ∧[ F ] W₂) ＝⟨ i                                 ⟩
      (U ∧[ F ] W₁) ∨[ F ] (W₁ ∧[ F ] W₂) ＝⟨ ii                                ⟩
      𝟎[ F ] ∨[ F ] (W₁ ∧[ F ] W₂)        ＝⟨ iii                               ⟩
      (U ∧[ F ] W₂) ∨[ F ] (W₁ ∧[ F ] W₂) ＝⟨ iv                                ⟩
      (W₂ ∧[ F ] U) ∨[ F ] (W₁ ∧[ F ] W₂) ＝⟨ v                                 ⟩
      (W₂ ∧[ F ] U) ∨[ F ] (W₂ ∧[ F ] W₁) ＝⟨ vi                                ⟩
      W₂ ∧[ F ] (U ∨[ F ] W₁)             ＝⟨ vii                               ⟩
      W₂ ∧[ F ] 𝟏[ F ]                    ＝⟨ viii                              ⟩
      W₂                                  ∎
       where
        i    = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (∧[ F ]-is-commutative W₁ U)
        ii   = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) p₁
        iii  = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (p₂ ⁻¹)
        iv   = ap (λ - → - ∨[ F ] (W₁ ∧[ F ] W₂)) (∧[ F ]-is-commutative U W₂)
        v    = ap (λ - → (W₂ ∧[ F ] U) ∨[ F ] -) (∧[ F ]-is-commutative W₁ W₂)
        vi   = binary-distributivity F W₂ U W₁ ⁻¹
        vii  = ap (λ - → W₂ ∧[ F ] -) q₁
        viii = 𝟏-right-unit-of-∧ F W₂

\end{code}

\begin{code}

is-clopen : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω 𝓤
is-clopen F U = is-clopen₀ F U , is-clopen₀-is-prop F U

\end{code}

\begin{code}

𝟏-is-clopen : (L : Frame 𝓤 𝓥 𝓦) → is-clopen L 𝟏[ L ] holds
𝟏-is-clopen L = 𝟎[ L ] , † , ‡
 where
  † : 𝟏[ L ] ∧[ L ] 𝟎[ L ] ＝ 𝟎[ L ]
  † = 𝟎-right-annihilator-for-∧ L 𝟏[ L ]

  ‡ : 𝟏[ L ] ∨[ L ] 𝟎[ L ] ＝ 𝟏[ L ]
  ‡ = 𝟏-left-annihilator-for-∨ L 𝟎[ L ]

\end{code}

\begin{code}

consists-of-clopens : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓦)
consists-of-clopens F S = Ɐ i ꞉ index S , is-clopen F (S [ i ])

\end{code}

\begin{code}

∧-complement : (F : Frame 𝓤 𝓥 𝓦)
             → {x y x′ y′ : ⟨ F ⟩}
             → is-boolean-complement-of F x x′ holds
             → is-boolean-complement-of F y y′ holds
             → is-boolean-complement-of F (x′ ∨[ F ] y′) (x ∧[ F ] y) holds
∧-complement F {x} {y} {x′} {y′} φ ψ = β , γ
 where
  open PosetReasoning (poset-of F)

  _⊓_ = λ x y → x ∧[ F ] y

  φ₀ : x ⊓ x′ ＝ 𝟎[ F ]
  φ₀ = x ⊓ x′ ＝⟨ ∧[ F ]-is-commutative x x′ ⟩ x′ ⊓ x ＝⟨ pr₁ φ ⟩  𝟎[ F ] ∎

  ψ₀ : y ⊓ y′ ＝ 𝟎[ F ]
  ψ₀ = y ⊓ y′ ＝⟨ ∧[ F ]-is-commutative y y′ ⟩ y′ ⊓ y  ＝⟨ pr₁ ψ ⟩ 𝟎[ F ] ∎

  φ₁ : x ∨[ F ] x′ ＝ 𝟏[ F ]
  φ₁ = x  ∨[ F ] x′ ＝⟨ ∨[ F ]-is-commutative x x′ ⟩
       x′ ∨[ F ] x  ＝⟨ pr₂ φ                      ⟩
       𝟏[ F ]       ∎

  β : (x ∧[ F ] y) ∧[ F ] (x′ ∨[ F ] y′) ＝ 𝟎[ F ]
  β = (x ⊓ y) ⊓ (x′ ∨[ F ] y′)                ＝⟨ Ⅰ ⟩
      ((x ⊓ y) ⊓ x′) ∨[ F ] ((x ⊓ y) ⊓ y′)    ＝⟨ Ⅱ ⟩
      ((y ⊓ x) ⊓ x′) ∨[ F ] ((x ⊓ y) ⊓ y′)    ＝⟨ Ⅲ ⟩
      (y ⊓ (x ⊓ x′)) ∨[ F ] ((x ⊓ y) ⊓ y′)    ＝⟨ Ⅳ ⟩
      (y ⊓ 𝟎[ F ]) ∨[ F ] ((x ⊓ y) ⊓ y′)      ＝⟨ Ⅴ ⟩
      𝟎[ F ] ∨[ F ] ((x ⊓ y) ⊓ y′)            ＝⟨ Ⅵ ⟩
      (x ⊓ y) ⊓ y′                            ＝⟨ Ⅶ ⟩
      x ⊓ (y ⊓ y′)                            ＝⟨ Ⅷ ⟩
      x ⊓ 𝟎[ F ]                              ＝⟨ Ⅸ ⟩
      𝟎[ F ]                                  ∎
       where
        Ⅰ = binary-distributivity F (x ⊓ y) x′ y′
        Ⅱ = ap (λ - → (- ⊓ x′) ∨[ F ] ((x ⊓ y) ⊓ y′)) (∧[ F ]-is-commutative x y)
        Ⅲ = ap (λ - → - ∨[ F ] ((x ⊓ y) ⊓ y′)) (∧[ F ]-is-associative y x x′ ⁻¹)
        Ⅳ = ap (λ - → (y ⊓ -) ∨[ F ] ((x ⊓ y) ⊓ y′)) φ₀
        Ⅴ = ap (λ - → - ∨[ F ] ((x ⊓ y) ⊓ y′)) (𝟎-right-annihilator-for-∧ F y)
        Ⅵ = 𝟎-right-unit-of-∨ F ((x ⊓ y) ⊓ y′)
        Ⅶ = ∧[ F ]-is-associative x y y′ ⁻¹
        Ⅷ = ap (λ - → x ⊓ -) ψ₀
        Ⅸ = 𝟎-right-annihilator-for-∧ F x


  γ : (x ⊓ y) ∨[ F ] (x′ ∨[ F ] y′) ＝ 𝟏[ F ]
  γ = (x ⊓ y) ∨[ F ] (x′ ∨[ F ] y′)                                ＝⟨ Ⅰ ⟩
      (x′ ∨[ F ] y′) ∨[ F ] (x ⊓ y)                                ＝⟨ Ⅱ ⟩
      ((x′ ∨[ F ] y′) ∨[ F ] x) ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)   ＝⟨ Ⅲ ⟩
      ((y′ ∨[ F ] x′) ∨[ F ] x) ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)   ＝⟨ Ⅳ ⟩
      (y′ ∨[ F ] (x′ ∨[ F ] x)) ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)   ＝⟨ Ⅴ ⟩
      (y′ ∨[ F ] 𝟏[ F ]) ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)          ＝⟨ Ⅵ ⟩
      𝟏[ F ] ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)                      ＝⟨ Ⅶ ⟩
      (x′ ∨[ F ] y′) ∨[ F ] y                                      ＝⟨ Ⅷ ⟩
      x′ ∨[ F ] (y′ ∨[ F ] y)                                      ＝⟨ Ⅸ ⟩
      x′ ∨[ F ] 𝟏[ F ]                                             ＝⟨ Ⅹ ⟩
      𝟏[ F ]                                                       ∎
       where
        † = ∨[ F ]-is-commutative x′ y′
        ‡ = 𝟏-right-annihilator-for-∨ F y′
        Ⅰ = ∨[ F ]-is-commutative (x ⊓ y) (x′ ∨[ F ] y′)
        Ⅱ = binary-distributivity-op F (x′ ∨[ F ] y′) x y
        Ⅲ = ap (λ - → (- ∨[ F ] x) ∧[ F ] ((_ ∨[ F ] _) ∨[ F ] y)) †
        Ⅳ = ap (λ - → - ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)) (∨[ F ]-assoc y′ x′ x)
        Ⅴ = ap (λ - → (y′ ∨[ F ] -) ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)) (pr₂ φ)
        Ⅵ = ap (λ - → - ∧[ F ] ((x′ ∨[ F ] y′) ∨[ F ] y)) ‡
        Ⅶ = 𝟏-left-unit-of-∧ F ((x′ ∨[ F ] y′) ∨[ F ] y)
        Ⅷ = ∨[ F ]-assoc x′ y′ y
        Ⅸ = ap (λ - → x′ ∨[ F ] -) (pr₂ ψ)
        Ⅹ = 𝟏-right-annihilator-for-∨ F x′

\end{code}
