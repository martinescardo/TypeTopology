Martin Escardo 13 Jun 2026.

An equivalent copy of the ordinal 𝟚₀, for convenience.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.Two where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Ordinals.Notions hiding (_≺₂_)
open import Ordinals.Type
open import UF.Subsingletons
open import UF.DiscreteAndSeparated

_≺₂_ : 𝟚 → 𝟚 → 𝓤₀ ̇
b ≺₂ c = (b ＝ ₀) × (c ＝ ₁)

≺₂-left : {x y : 𝟚} → x ≺₂ y → x ＝ ₀
≺₂-left = pr₁

≺₂-right : {x y : 𝟚} → x ≺₂ y → y ＝ ₁
≺₂-right = pr₂

≺₂-left-right : {x y : 𝟚} → x ＝ ₀ → y ＝ ₁ → x ≺₂ y
≺₂-left-right = _,_

𝟚ₒ : Ordinal 𝓤₀
𝟚ₒ = 𝟚 ,
     (λ b c → (b ＝ ₀) × (c ＝ ₁)) ,
     (λ b c → ×-is-prop 𝟚-is-set 𝟚-is-set) ,
     I ,
     II ,
     (λ _ _ _ (e₀ , _) (_ , e₁) → e₀ , e₁)
 where
  I : is-well-founded (λ b c → (b ＝ ₀) × (c ＝ ₁))
  I ₀ = acc (λ _ (_ , ν) → 𝟘-elim (zero-is-not-one ν))
  I ₁ = acc (λ b (e₀ , _) → acc (λ c (_ , e₁) → 𝟘-elim
                                                 (zero-is-not-one
                                                   (e₀ ⁻¹ ∙ e₁))))

  II : is-extensional (λ b c → (b ＝ ₀) × (c ＝ ₁))
  II ₀ ₀ f g = refl
  II ₀ ₁ f g = 𝟘-elim (zero-is-not-one (pr₂ (g ₀ (refl , refl))))
  II ₁ ₀ f g = 𝟘-elim (zero-is-not-one (pr₂ (f ₀ (refl , refl))))
  II ₁ ₁ f g = refl

\end{code}
