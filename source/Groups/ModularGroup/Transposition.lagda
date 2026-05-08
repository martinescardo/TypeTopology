Lane Biocini, 21 January 2026

Transposition: the anti-automorphism reversing multiplication order.
Satisfies (x · y)ᵀ = yᵀ · xᵀ, making it a homomorphism to the opposite
group. Combined with involutivity ((xᵀ)ᵀ = x), this establishes an
isomorphism 𝓜 ≅ 𝓜ᵒᵖ.

This isomorphism reflects that the presentation ⟨s, r | s² = r³ = 1⟩
is symmetric: the relations are preserved under word reversal. Not all
groups have this property, it requires that generators be self-inverse
or that inverse pairs appear symmetrically in relations.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Groups.ModularGroup.Transposition where

open import MLTT.Spartan
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Base
open import Groups.ModularGroup.Properties
open import Groups.ModularGroup.Induction
open import Groups.ModularGroup.Multiplication

transpose-η : S-edge → PSL2Z
transpose-θ : R-edge → PSL2Z

transpose-η e₀         = E
transpose-η e₁         = S
transpose-η (cross re) = (transpose-θ re) · S

transpose-θ (r+ se) = (transpose-η se) · SR²S
transpose-θ (r- se) = (transpose-η se) · SRS

_ᵀ : PSL2Z → PSL2Z
(η se) ᵀ = transpose-η se
(θ re) ᵀ = transpose-θ re

infix 32 _ᵀ

transpose-s : (x : PSL2Z) → (s x) ᵀ ＝ x ᵀ · S
transpose-s (η e₀) = refl
transpose-s (η e₁) = refl
transpose-s (sr∙ se) =
  s (sr∙ se) ᵀ                       ＝⟨ ·-E-right (transpose-θ (r+ se)) ⁻¹ ⟩
  transpose-θ (r+ se) · E            ＝⟨ ·-assoc (transpose-θ (r+ se)) S S ⁻¹ ⟩
  transpose-θ (r+ se) · S · S        ∎
transpose-s (sr²∙ se) =
  s (sr²∙ se) ᵀ                      ＝⟨ ·-E-right (transpose-θ (r- se)) ⁻¹ ⟩
  transpose-θ (r- se) · E            ＝⟨ ·-assoc (transpose-θ (r- se)) S S ⁻¹ ⟩
  transpose-θ (r- se) · S · S        ∎
transpose-s (r∙ se) = refl
transpose-s (r²∙ se) = refl

transpose-r : (x : PSL2Z) → (r x) ᵀ ＝ x ᵀ · SR²S
transpose-r (η e₀) = refl
transpose-r (η e₁) = refl
transpose-r (sr∙ se) = refl
transpose-r (sr²∙ se) = refl
transpose-r (r∙ se) = ·-assoc (transpose-η se) SR²S SR²S ⁻¹
transpose-r (r²∙ se) =
  r (r²∙ se) ᵀ                     ＝⟨ ·-E-right (transpose-η se) ⁻¹ ⟩
  transpose-η se · (SRS · SR²S)    ＝⟨ ·-assoc (transpose-η se) SRS SR²S ⁻¹ ⟩
  transpose-η se · SRS · SR²S      ∎

transpose-r² : (x : PSL2Z) → (r² x) ᵀ ＝ x ᵀ · SRS
transpose-r² (η e₀) = refl
transpose-r² (η e₁) = refl
transpose-r² (sr∙ se) = refl
transpose-r² (sr²∙ se) = refl
transpose-r² (r∙ se) =
  r² (r∙ se) ᵀ                     ＝⟨ ·-E-right (transpose-η se) ⁻¹ ⟩
  transpose-η se · (SR²S · SRS)    ＝⟨ ·-assoc (transpose-η se) SR²S SRS ⁻¹ ⟩
  transpose-η se · SR²S · SRS      ∎
transpose-r² (r²∙ se) =
  r² (r²∙ se) ᵀ                  ＝⟨ ap _ᵀ (r²-θ-r- se) ⟩
  (r∙ se) ᵀ                      ＝⟨ ·-assoc (transpose-η se) SRS SRS ⁻¹ ⟩
  transpose-η se · SRS · SRS     ∎

transpose-product : (x y : PSL2Z) → (x · y) ᵀ ＝ (y ᵀ) · (x ᵀ)
transpose-product =
 PSL2Z-ind
  {P = λ x → (y : PSL2Z) → (x · y) ᵀ ＝ (y ᵀ) · (x ᵀ)}
  base-E base-S ind-s ind-r
 where
  base-E : (y : PSL2Z) → (E · y) ᵀ ＝ (y ᵀ) · (E ᵀ)
  base-E y = ·-E-right (y ᵀ) ⁻¹

  base-S : (y : PSL2Z) → (S · y) ᵀ ＝ (y ᵀ) · (S ᵀ)
  base-S y = transpose-s y

  ind-s : (re : R-edge)
        → ((y : PSL2Z) → ((θ re) · y) ᵀ ＝ (y ᵀ) · ((θ re) ᵀ))
        → (y : PSL2Z) → ((s∙ re) · y) ᵀ ＝ (y ᵀ) · ((s∙ re) ᵀ)
  ind-s re ih y =
    ((s∙ re) · y) ᵀ            ＝⟨ ap _ᵀ (·-s-left (θ re) y) ⟩
    (s ((θ re) · y)) ᵀ         ＝⟨ transpose-s ((θ re) · y) ⟩
    (((θ re) · y) ᵀ) · S       ＝⟨ ap (_· S) (ih y) ⟩
    ((y ᵀ) · ((θ re) ᵀ)) · S   ＝⟨ ·-assoc (y ᵀ) ((θ re) ᵀ) S ⟩
    (y ᵀ) · (((θ re) ᵀ) · S)   ＝⟨ ap ((y ᵀ) ·_) (transpose-s (θ re) ⁻¹) ⟩
    (y ᵀ) · ((s∙ re) ᵀ)        ∎

  ind-r : (d : R-sgn) (se : S-edge)
        → ((y : PSL2Z) → ((η se) · y) ᵀ ＝ (y ᵀ) · ((η se) ᵀ))
        → (y : PSL2Z) → ((ρ d se) · y) ᵀ ＝ (y ᵀ) · ((ρ d se) ᵀ)
  ind-r cw se ih y =
    ((r∙ se) · y) ᵀ              ＝⟨ ap (_ᵀ ∘ (_· y)) (r-η se ⁻¹) ⟩
    ((r (η se)) · y) ᵀ           ＝⟨ ap _ᵀ (·-r-left (η se) y) ⟩
    (r ((η se) · y)) ᵀ           ＝⟨ transpose-r ((η se) · y) ⟩
    (((η se) · y) ᵀ) · SR²S      ＝⟨ ap (_· SR²S) (ih y) ⟩
    ((y ᵀ) · ((η se) ᵀ)) · SR²S  ＝⟨ ·-assoc (y ᵀ) ((η se) ᵀ) SR²S ⟩
    (y ᵀ) · (((η se) ᵀ) · SR²S)  ＝⟨ ap ((y ᵀ) ·_) (transpose-r (η se) ⁻¹) ⟩
    (y ᵀ) · ((r (η se)) ᵀ)       ＝⟨ ap ((y ᵀ) ·_) (ap _ᵀ (r-η se)) ⟩
    (y ᵀ) · ((r∙ se) ᵀ)          ∎
  ind-r ccw se ih y =
    ((r²∙ se) · y) ᵀ             ＝⟨ ap (_ᵀ ∘ (_· y)) (r²-η se ⁻¹) ⟩
    ((r² (η se)) · y) ᵀ          ＝⟨ ap _ᵀ (·-r²-left (η se) y) ⟩
    (r² ((η se) · y)) ᵀ          ＝⟨ transpose-r² ((η se) · y) ⟩
    (((η se) · y) ᵀ) · SRS       ＝⟨ ap (_· SRS) (ih y) ⟩
    ((y ᵀ) · ((η se) ᵀ)) · SRS   ＝⟨ ·-assoc (y ᵀ) ((η se) ᵀ) SRS ⟩
    (y ᵀ) · (((η se) ᵀ) · SRS)   ＝⟨ ap ((y ᵀ) ·_) (transpose-r² (η se) ⁻¹) ⟩
    (y ᵀ) · ((r² (η se)) ᵀ)      ＝⟨ ap ((y ᵀ) ·_) (ap _ᵀ (r²-η se)) ⟩
    (y ᵀ) · ((r²∙ se) ᵀ)         ∎

transpose-involutive-η : (se : S-edge) → transpose-η se ᵀ ＝ η se
transpose-involutive-θ : (re : R-edge) → transpose-θ re ᵀ ＝ θ re

transpose-involutive-η e₀         = refl
transpose-involutive-η e₁         = refl
transpose-involutive-η (cross re) =
  ((transpose-θ re) · S) ᵀ   ＝⟨ transpose-product (transpose-θ re) S ⟩
  s ((transpose-θ re) ᵀ)     ＝⟨ ap s (transpose-involutive-θ re) ⟩
  s (θ re)                   ＝⟨ refl ⟩
  η (cross re)               ∎

transpose-involutive-θ (r+ se) =
  ((transpose-η se) · SR²S) ᵀ  ＝⟨ transpose-product (transpose-η se) SR²S ⟩
  r ((transpose-η se) ᵀ)       ＝⟨ ap r (transpose-involutive-η se) ⟩
  r (η se)                     ＝⟨ r-η se ⟩
  θ (r+ se)                    ∎

transpose-involutive-θ (r- se) =
  ((transpose-η se) · SRS) ᵀ   ＝⟨ transpose-product (transpose-η se) SRS ⟩
  r² ((transpose-η se) ᵀ)      ＝⟨ ap r² (transpose-involutive-η se) ⟩
  r² (η se)                    ＝⟨ r²-η se ⟩
  θ (r- se)                    ∎

transpose-involutive : (x : PSL2Z) → (x ᵀ) ᵀ ＝ x
transpose-involutive (η se) = transpose-involutive-η se
transpose-involutive (θ re) = transpose-involutive-θ re

\end{code}
