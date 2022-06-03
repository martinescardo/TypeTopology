Martin Escardo, 6th May 2022

Arithmetic for trichotomous ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module OrdinalTrichotomousArithmetic
        (fe : FunExt)
       where

open import UF-Subsingletons

open import SpartanMLTT
open import OrdinalsType
open import OrdinalNotions
open import OrdinalArithmetic fe
open import OrdinalsWellOrderArithmetic
open import OrdinalsTrichotomousType fe

_+₃_ : Ordinal₃ 𝓤 → Ordinal₃ 𝓤 → Ordinal₃ 𝓤
τ +₃ υ = (⁅ τ ⁆ +ₒ ⁅ υ ⁆) , +ₒ-is-trichotomous ⁅ τ ⁆ ⁅ υ ⁆
                              (3is-trichotomous τ)
                              (3is-trichotomous υ)

𝟘₃ 𝟙₃ 𝟚₃ : Ordinal₃ 𝓤
𝟘₃ = 𝟘ₒ , 𝟘ₒ-is-trichotomous
𝟙₃ = 𝟙ₒ , 𝟙ₒ-is-trichotomous
𝟚₃ = 𝟙₃ +₃ 𝟙₃

ω₃ : Ordinal₃ 𝓤₀
ω₃ = ω , ω-is-trichotomous

∑³ : (τ : Ordinal₃ 𝓤) → (⦅ τ ⦆ → Ordinal₃ 𝓤) → Ordinal₃ 𝓤
∑³ {𝓤} (α@(X , _<_ , o) , t) υ = ((Σ x ꞉ X , ⦅ υ x ⦆) ,
                                 Sum.order ,
                                 Sum.well-order o (λ x → 3is-well-ordered (υ x))) ,
                                sum.trichotomy-preservation _ _ t (λ x → 3is-trichotomous (υ x))
 where
  _≺_ : {x : X} → ⦅ υ x ⦆ → ⦅ υ x ⦆ → 𝓤 ̇
  y ≺ z = y ≺⦅ υ _ ⦆ z

  module Sum = sum-cotransitive fe _<_ _≺_ (tricho-gives-cotrans _<_ (Transitivity α) t)

_×₃_ : Ordinal₃ 𝓤 → Ordinal₃ 𝓤 → Ordinal₃ 𝓤
τ ×₃ υ = ∑³ τ  (λ (_ : ⦅ τ ⦆) → υ)

\end{code}
