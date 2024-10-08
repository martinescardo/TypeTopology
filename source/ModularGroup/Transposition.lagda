Lane Biocini 30 September 2023

The transposition operator, related to inversion

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ModularGroup.Transposition where

open import MLTT.Spartan
open import Notation.General

open import ModularGroup.Type
open import ModularGroup.Composition

_ᵀ : 𝓜 → 𝓜
E ᵀ = E
S ᵀ = S
𝒔 x ᵀ = θ x ᵀ • S
𝒓 x ᵀ = η x ᵀ • SR²S
𝒓² x ᵀ = η x ᵀ • SRS

infix 32 _ᵀ

is-symmetric : 𝓜 → 𝓤₀ ̇
is-symmetric a = a ＝ a ᵀ

𝓜-symmetric : 𝓤₀ ̇
𝓜-symmetric = Σ a ꞉ 𝓜 , is-symmetric a

transpose-s : (x : 𝓜) → (s x) ᵀ ＝ x ᵀ • S
transpose-s E = refl
transpose-s S = refl
transpose-s (𝒔 x) =
 θ x ᵀ           ＝⟨ compose-right-neutral (θ x ᵀ) ⁻¹ ⟩
 θ x ᵀ • E       ＝⟨ compose-associative (θ x ᵀ) S S ⁻¹ ⟩
 (θ x ᵀ • S) • S ∎
transpose-s (θ x) = refl

transpose-r : (x : 𝓜) → (r x) ᵀ ＝ x ᵀ • SR²S
transpose-r (η x) = refl
transpose-r (𝒓 x) = compose-associative (η x ᵀ) SR²S SR²S ⁻¹
transpose-r (𝒓² x) =
 η x ᵀ                  ＝⟨ compose-right-neutral (η x ᵀ) ⁻¹ ⟩
 η x ᵀ • E              ＝⟨ compose-associative (η x ᵀ) SRS SR²S ⁻¹ ⟩
 (η x ᵀ • SRS) • SR²S ∎

transpose-r² : (x : 𝓜) → (r² x) ᵀ ＝ x ᵀ • s (r S)
transpose-r² (η x) = refl
transpose-r² (𝒓 x) =
 η x ᵀ                ＝⟨ compose-right-neutral (η x ᵀ) ⁻¹ ⟩
 η x ᵀ • E            ＝⟨ compose-associative (η x ᵀ) SR²S SRS ⁻¹ ⟩
 (η x ᵀ • SR²S) • SRS ∎
transpose-r² (𝒓² x) = compose-associative (η x ᵀ) (sr S) (sr S) ⁻¹

transpose-product : (a b : 𝓜) → (a • b) ᵀ ＝ b ᵀ • a ᵀ
transpose-product E b = compose-right-neutral (b ᵀ) ⁻¹
transpose-product S b = transpose-s b
transpose-product (𝒔 x) b =
 s (θ x • b) ᵀ     ＝⟨ transpose-s (θ x • b) ⟩
 (θ x • b) ᵀ • S   ＝⟨ ap (_• S) (transpose-product (θ x) b) ⟩
 (b ᵀ • θ x ᵀ) • S ＝⟨ compose-associative (b ᵀ) (θ x ᵀ) S ⟩
 b ᵀ • θ x ᵀ • S   ∎
transpose-product (𝒓 x) b =
 r (η x • b) ᵀ        ＝⟨ transpose-r (η x • b) ⟩
 (η x • b) ᵀ • SR²S   ＝⟨ ap (_• sr² S) (transpose-product (η x) b ) ⟩
 (b ᵀ • η x ᵀ) • SR²S ＝⟨ compose-associative (b ᵀ) (η x ᵀ) SR²S ⟩
 b ᵀ • η x ᵀ • SR²S   ∎
transpose-product (𝒓² x) b = transpose-r² (η x • b)
 ∙ (ap (_• SRS) (transpose-product (η x) b)
 ∙ compose-associative (b ᵀ) (η x ᵀ) SRS)

transpose-right-s : (x : 𝓜) → (x • S) ᵀ ＝ s (x ᵀ)
transpose-right-s x = transpose-product x S

transpose-right-r : (x : 𝓜) → (x • R) ᵀ ＝ sr²s (x ᵀ )
transpose-right-r x = transpose-product x R

transpose-right-r² : (x : 𝓜) → (x • R²) ᵀ ＝ srs (x ᵀ)
transpose-right-r² x = transpose-product x R²

transpose-involutive : involutive (_ᵀ)
transpose-involutive E = refl
transpose-involutive S = refl
transpose-involutive (𝒔 x) =
 (θ x ᵀ • S) ᵀ ＝⟨ transpose-product (θ x ᵀ) S ⟩
 s ((θ x ᵀ) ᵀ) ＝⟨ ap s (transpose-involutive (θ x)) ⟩
 𝒔 x           ∎
transpose-involutive (𝒓 x) =
 (η x ᵀ • SR²S) ᵀ ＝⟨ transpose-product (η x ᵀ) SR²S ⟩
 r ((η x ᵀ) ᵀ)    ＝⟨ ap r (transpose-involutive (η x)) ⟩
 𝒓 x              ∎
transpose-involutive (𝒓² x) =
 (η x ᵀ • SRS) ᵀ   ＝⟨ transpose-product (η x ᵀ) SRS ⟩
 r (r ((η x ᵀ) ᵀ)) ＝⟨ ap r² (transpose-involutive (η x)) ⟩
 𝒓² x              ∎

inverse-transpose : (a : 𝓜) → (a ᵀ -¹) ＝ ((a -¹) ᵀ)
inverse-transpose E = refl
inverse-transpose S = refl
inverse-transpose (𝒔 x) =
 (θ x ᵀ • S) -¹ ＝⟨ inverse-product (θ x ᵀ) S ⟩
 s ((θ x ᵀ) -¹) ＝⟨ ap s (inverse-transpose (θ x)) ⟩
 s ((θ x -¹) ᵀ) ＝⟨ transpose-product (θ x -¹) S ⁻¹ ⟩
 (θ x -¹ • S) ᵀ ∎
inverse-transpose (𝒓 x) =
 (η x ᵀ • SR²S) -¹      ＝⟨ inverse-product (η x ᵀ) SR²S ⟩
 s (r (s ((η x ᵀ) -¹))) ＝⟨ ap srs (inverse-transpose (η x)) ⟩
 s (r (s ((η x -¹) ᵀ))) ＝⟨ transpose-product (η x -¹) R² ⁻¹ ⟩
 (η x -¹ • R²) ᵀ        ∎
inverse-transpose (𝒓² x) =
 (η x ᵀ • SRS) -¹           ＝⟨ inverse-product (η x ᵀ) SRS ⟩
 s (r (r (s ((η x ᵀ) -¹)))) ＝⟨ ap sr²s (inverse-transpose (η x)) ⟩
 s (r (r (s ((η x -¹) ᵀ)))) ＝⟨ transpose-product (η x -¹) R ⁻¹ ⟩
 (η x -¹ • R) ᵀ             ∎

\end{code}
