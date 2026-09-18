Ayberk Tosun, 11 September 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.Complements (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                           where

open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import MLTT.Spartan hiding (𝟚)
open import UF.Logic
open import UF.SubtypeClassifier

open AllCombinators pt fe
open FrameHomomorphismProperties
open FrameHomomorphisms
open Locale
open PropositionalTruncation pt

\end{code}

An open `x` in a frame `L` is *clopen* iff it has complement `x′`.

\begin{code}

is-boolean-complement-of : (L : Frame 𝓤 𝓥 𝓦) → ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓤
is-boolean-complement-of F x′ x =
 (x ∧[ F ] x′ ＝[ iss ]＝ 𝟎[ F ]) ∧ (x ∨[ F ] x′ ＝[ iss ]＝ 𝟏[ F ])
  where
   iss = carrier-of-[ poset-of F ]-is-set

\end{code}

\begin{code}

complementation-is-symmetric : (F : Frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                             → (is-boolean-complement-of F x y
                             ⇒  is-boolean-complement-of F y x) holds
complementation-is-symmetric F x y (φ , ψ) = † , ‡
 where
  † : x ∧[ F ] y ＝ 𝟎[ F ]
  † = x ∧[ F ] y ＝⟨ ∧[ F ]-is-commutative x y ⟩ y ∧[ F ] x ＝⟨ φ ⟩ 𝟎[ F ] ∎

  ‡ : x ∨[ F ] y ＝ 𝟏[ F ]
  ‡ = x ∨[ F ] y ＝⟨ ∨[ F ]-is-commutative x y ⟩ y ∨[ F ] x ＝⟨ ψ ⟩ 𝟏[ F ] ∎

\end{code}

\begin{code}

complement-of-meet : (L : Frame 𝓤 𝓥 𝓦)
                   → {x y x′ y′ : ⟨ L ⟩}
                   → is-boolean-complement-of L x x′ holds
                   → is-boolean-complement-of L y y′ holds
                   → is-boolean-complement-of L (x′ ∨[ L ] y′) (x ∧[ L ] y) holds
complement-of-meet L {x} {y} {x′} {y′} φ ψ = β , γ
 where
  open PosetReasoning (poset-of L)
  F = L

  _⊓_ = λ (x y : ⟨ L ⟩) → x ∧[ L ] y

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

frame-homomorphisms-preserve-complements : (F G : Frame 𝓤 𝓥 𝓦)
                                         → (h : F ─f→ G)
                                         → {x x′ : ⟨ F ⟩}
                                         → is-boolean-complement-of F x′ x holds
                                         → is-boolean-complement-of G (h .pr₁ x) (h .pr₁ x′) holds
frame-homomorphisms-preserve-complements F G 𝒽@(h , _ , μ) {x} {x′} (φ , ψ) = † , ‡
 where
  † : (h x′) ∧[ G ] (h x) ＝ 𝟎[ G ]
  † = h x′ ∧[ G ] h x   ＝⟨ Ⅰ ⟩
      h (x′ ∧[ F ] x)   ＝⟨ Ⅱ ⟩
      h 𝟎[ F ]          ＝⟨ Ⅲ ⟩
      𝟎[ G ]            ∎
       where
        Ⅰ = frame-homomorphisms-preserve-meets F G 𝒽 x′ x ⁻¹
        Ⅱ = ap h (x′ ∧[ F ] x   ＝⟨ ∧[ F ]-is-commutative x′ x ⟩
                  x ∧[ F ] x′   ＝⟨ φ ⟩
                  𝟎[ F ]        ∎)
        Ⅲ = frame-homomorphisms-preserve-bottom F G 𝒽

  ‡ : h x′ ∨[ G ] h x ＝ 𝟏[ G ]
  ‡ = h x′ ∨[ G ] h x   ＝⟨ Ⅰ ⟩
      h (x′ ∨[ F ] x)   ＝⟨ Ⅱ ⟩
      h 𝟏[ F ]          ＝⟨ Ⅲ ⟩
      𝟏[ G ]            ∎
       where
        Ⅰ = frame-homomorphisms-preserve-binary-joins F G 𝒽 x′ x ⁻¹
        Ⅱ = ap h (x′ ∨[ F ] x ＝⟨ ∨[ F ]-is-commutative x′ x ⟩
                  x ∨[ F ] x′ ＝⟨ ψ ⟩
                  𝟏[ F ]      ∎)
        Ⅲ = frame-homomorphisms-preserve-top F G 𝒽

\end{code}
