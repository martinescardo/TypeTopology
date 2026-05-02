Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size

module Locales.Clopen (pt : propositional-truncations-exist)
                      (fe : Fun-Ext)
                      (sr : Set-Replacement pt) where

open import Locales.Complements pt fe
open import Locales.Frame pt fe
open import Locales.WellInside pt fe sr
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.Base using (from-Σ-＝)
open import UF.Logic
open import UF.Subsingletons
open import UF.SubtypeClassifier

open AllCombinators pt fe
open PropositionalTruncation pt



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

The definition of the notion of clopen.

\begin{code}

is-clopen : (F : Frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → Ω 𝓤
is-clopen F U = is-clopen₀ F U , is-clopen₀-is-prop F U

\end{code}

The type of clopens of a locale `X`.

\begin{code}

𝒞 : Locale 𝓤 𝓥 𝓦 → 𝓤 ̇
𝒞 X = Σ C ꞉ ⟨ 𝒪 X ⟩ , is-clopen (𝒪 X) C holds

\end{code}

The top element `𝟏` is always a clopen.

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

\begin{code}

clopens-are-closed-under-∧ : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                           → (is-clopen F x
                           ⇒  is-clopen F y
                           ⇒  is-clopen F (x ∧[ F ] y)) holds
clopens-are-closed-under-∧ F x y ϟ₁@(x′ , φ₁ , φ₂) ϟ₂@(y′ , ψ₁ , ψ₂) =
 (x′ ∨[ F ] y′) , †
  where
   ‡₁ : is-boolean-complement-of F x x′ holds
   ‡₁ = (x′ ∧[ F ] x ＝⟨ ∧[ F ]-is-commutative x′ x ⟩ x ∧[ F ] x′ ＝⟨ φ₁ ⟩ 𝟎[ F ] ∎)
      , (x′ ∨[ F ] x ＝⟨ ∨[ F ]-is-commutative x′ x ⟩ x ∨[ F ] x′ ＝⟨ φ₂ ⟩ 𝟏[ F ] ∎)

   ‡₂ : is-boolean-complement-of F y y′ holds
   ‡₂ = (y′ ∧[ F ] y ＝⟨ ∧[ F ]-is-commutative y′ y ⟩ y ∧[ F ] y′ ＝⟨ ψ₁ ⟩ 𝟎[ F ] ∎)
      , (y′ ∨[ F ] y ＝⟨ ∨[ F ]-is-commutative y′ y ⟩ y ∨[ F ] y′ ＝⟨ ψ₂ ⟩ 𝟏[ F ] ∎)

   † : is-boolean-complement-of F (x′ ∨[ F ] y′) (x ∧[ F ] y) holds
   † = ∧-complement F ‡₁ ‡₂

\end{code}

Given a family `S`, consisting of clopens, then `directify S` also consists of
clopens.

\begin{code}

clopens-are-closed-under-∨ : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                           → (is-clopen F x
                           ⇒  is-clopen F y
                           ⇒  is-clopen F (x ∨[ F ] y)) holds
clopens-are-closed-under-∨ F x y (x′ , ϡ₁ , ϟ₁) (y′ , ϡ₂ , ϟ₂) =
 (x′ ∧[ F ] y′) , † , ‡
  where
   open PosetReasoning (poset-of F)

   †₁ : (((x ∨[ F ] y) ∧[ F ] (x′ ∧[ F ] y′)) ≤[ poset-of F ] 𝟎[ F ]) holds
   †₁ =
    (x ∨[ F ] y) ∧[ F ] (x′ ∧[ F ] y′)                         ＝⟨ Ⅰ ⟩ₚ
    (x ∧[ F ] (x′ ∧[ F ] y′)) ∨[ F ] (y ∧[ F ] (x′ ∧[ F ] y′)) ≤⟨ Ⅱ ⟩
    (x ∧[ F ] x′) ∨[ F ] (y ∧[ F ] (x′ ∧[ F ] y′))             ≤⟨ Ⅲ ⟩
    (x ∧[ F ] x′) ∨[ F ] (y ∧[ F ] y′)                         ≤⟨ Ⅳ ⟩
    𝟎[ F ] ∨[ F ] (y ∧[ F ] y′)                                ≤⟨ Ⅴ ⟩
    𝟎[ F ] ∨[ F ] 𝟎[ F ]                                       ＝⟨ Ⅵ ⟩ₚ
    𝟎[ F ]                                                     ■
     where
      Ⅰ = binary-distributivity-right F
      Ⅱ = ∨[ F ]-left-monotone  (∧[ F ]-right-monotone (∧[ F ]-lower₁ x′ y′))
      Ⅲ = ∨[ F ]-right-monotone (∧[ F ]-right-monotone (∧[ F ]-lower₂ x′ y′))
      Ⅳ = ∨[ F ]-left-monotone  (reflexivity+ (poset-of F) ϡ₁)
      Ⅴ = ∨[ F ]-right-monotone (reflexivity+ (poset-of F) ϡ₂)
      Ⅵ = ∨[ F ]-is-idempotent 𝟎[ F ] ⁻¹

   † : (x ∨[ F ] y) ∧[ F ] (x′ ∧[ F ] y′) ＝ 𝟎[ F ]
   † = only-𝟎-is-below-𝟎 F _ †₁

   ‡₁ : (𝟏[ F ] ≤[ poset-of F ] ((x ∨[ F ] y) ∨[ F ] (x′ ∧[ F ] y′))) holds
   ‡₁ =
    𝟏[ F ]                                                      ＝⟨ Ⅰ ⟩ₚ
    𝟏[ F ] ∧[ F ] 𝟏[ F ]                                        ≤⟨ Ⅱ ⟩
    (x ∨[ F ] x′) ∧[ F ] 𝟏[ F ]                                 ≤⟨ Ⅲ ⟩
    (x ∨[ F ] x′) ∧[ F ] (y ∨[ F ] y′)                          ≤⟨ Ⅳ ⟩
    ((x ∨[ F ] y ) ∨[ F ] x′)∧[ F ] (y ∨[ F ] y′)               ≤⟨ Ⅴ ⟩
    ((x ∨[ F ] y ) ∨[ F ] x′) ∧[ F ] ((x ∨[ F ] y ) ∨[ F ] y′)  ＝⟨ Ⅵ ⟩ₚ
    (x ∨[ F ] y) ∨[ F ] (x′ ∧[ F ] y′)                          ■
     where
      Ⅰ = ∧[ F ]-is-idempotent 𝟏[ F ]
      Ⅱ = ∧[ F ]-left-monotone  (reflexivity+ (poset-of F) (ϟ₁ ⁻¹))
      Ⅲ = ∧[ F ]-right-monotone (reflexivity+ (poset-of F) (ϟ₂ ⁻¹))
      Ⅳ = ∧[ F ]-left-monotone (∨[ F ]-left-monotone (∨[ F ]-upper₁ x y))
      Ⅴ = ∧[ F ]-right-monotone (∨[ F ]-left-monotone (∨[ F ]-upper₂ x y))
      Ⅵ = binary-distributivity-op F (x ∨[ F ] y) x′ y′ ⁻¹

   ‡ : (x ∨[ F ] y) ∨[ F ] (x′ ∧[ F ] y′) ＝ 𝟏[ F ]
   ‡ = only-𝟏-is-above-𝟏 F _ ‡₁

\end{code}

The bottom element is always clopen.

\begin{code}

𝟎-is-clopen : (F : Frame 𝓤 𝓥 𝓦) → is-clopen₀ F 𝟎[ F ]
𝟎-is-clopen F = 𝟏[ F ] , β , γ
 where
  β : 𝟎[ F ] ∧[ F ] 𝟏[ F ] ＝ 𝟎[ F ]
  β = 𝟎-left-annihilator-for-∧ F 𝟏[ F ]

  γ : 𝟎[ F ] ∨[ F ] 𝟏[ F ] ＝ 𝟏[ F ]
  γ = 𝟏-right-annihilator-for-∨ F 𝟎[ F ]

\end{code}

\begin{code}

directification-preserves-clopenness : (F : Frame 𝓤 𝓥 𝓦)
                                     → (ℬ : Fam 𝓦 ⟨ F ⟩)
                                     → (consists-of-clopens F ℬ
                                     ⇒ consists-of-clopens F (directify F ℬ))
                                       holds
directification-preserves-clopenness F ℬ ξ []       = 𝟎-is-clopen F
directification-preserves-clopenness F ℬ ξ (i ∷ is) =
 clopens-are-closed-under-∨ F (ℬ [ i ]) (directify F ℬ [ is ]) (ξ i) ℐℋ
  where
   abstract
    ℐℋ : is-clopen F (directify F ℬ [ is ]) holds
    ℐℋ = directification-preserves-clopenness F ℬ ξ is

\end{code}


\begin{code}

well-inside-itself-implies-clopen : (X : Locale 𝓤 𝓥 𝓦)
                                  → (U : ⟨ 𝒪 X ⟩)
                                  → ((U ⋜[ 𝒪 X ] U) ⇒ is-clopen (𝒪 X) U) holds
well-inside-itself-implies-clopen X U =
 ∥∥-rec (holds-is-prop (is-clopen (𝒪 X) U)) id

\end{code}

\begin{code}

complements-are-unique : (F : Frame 𝓤 𝓥 𝓦) (U V₁ V₂ : ⟨ F ⟩)
                       → is-boolean-complement-of F V₁ U holds
                       → is-boolean-complement-of F V₂ U holds
                       → V₁ ＝ V₂
complements-are-unique F U V₁ V₂ p q =
 pr₁ (from-Σ-＝ (is-clopen₀-is-prop F U (V₁ , p) (V₂ , q)))

\end{code}
