Tom de Jong and Fredrik Nordvall Forsberg, 2 December 2024

See Ordinals.Arithmetic for the definition of the unique ordinal structure on a
proposition. We prove additional properties here that require several imports.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence

module Ordinals.Propositions (ua : Univalence) where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' = Univalence-gives-Fun-Ext ua

open import MLTT.Spartan
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import UF.Equiv
open import UF.Subsingletons

prop-ordinal-⊴ : {P : 𝓤 ̇  } {Q : 𝓥 ̇  } (i : is-prop P) (j : is-prop Q)
               → (P → Q) → prop-ordinal P i ⊴ prop-ordinal Q j
prop-ordinal-⊴ _ _ f = f , (λ _ _ → 𝟘-elim) , (λ _ _ → 𝟘-elim)

prop-ordinal-≃ₒ : {P : 𝓤 ̇  } {Q : 𝓥 ̇  } (i : is-prop P) (j : is-prop Q)
                → (P → Q) → (Q → P) → prop-ordinal P i ≃ₒ prop-ordinal Q j
prop-ordinal-≃ₒ {𝓤} {𝓥} {P} {Q} i j f g =
 bisimilarity-gives-ordinal-equiv
  (prop-ordinal P i) (prop-ordinal Q j)
  (prop-ordinal-⊴ i j f)
  (prop-ordinal-⊴ j i g)

prop-ordinal-＝ : {P Q : 𝓤 ̇  } (i : is-prop P) (j : is-prop Q)
               → (P → Q) → (Q → P) → prop-ordinal P i ＝ prop-ordinal Q j
prop-ordinal-＝ {𝓤} {P} {Q} i j f g =
 eqtoidₒ (ua 𝓤) fe'
  (prop-ordinal P i) (prop-ordinal Q j) (prop-ordinal-≃ₒ i j f g)

prop-ordinal-↓-≃ₒ : {P : 𝓤 ̇  } (i : is-prop P) (p : P)
                  → (prop-ordinal P i ↓ p) ≃ₒ 𝟘ₒ {𝓥}
prop-ordinal-↓-≃ₒ {𝓤} {P} i p =
 prop-ordinal-≃ₒ
  (λ (x , l) (y , k) → 𝟘-elim l)
  𝟘-is-prop
  (λ (x , l) → 𝟘-elim l)
  𝟘-elim

prop-ordinal-↓ : {P : 𝓤 ̇  } (i : is-prop P) (p : P)
               → (prop-ordinal P i ↓ p) ＝ 𝟘ₒ
prop-ordinal-↓ i p =
 eqtoidₒ (ua _) fe' (prop-ordinal _ i ↓ p) 𝟘ₒ (prop-ordinal-↓-≃ₒ i p)

prop-ordinal-least : {P : 𝓤 ̇  } (i : is-prop P) (p : P)
                   → is-least (prop-ordinal P i) p
prop-ordinal-least i p p' p'' l = 𝟘-elim l

𝟙ₒ-least : {x : 𝟙 {𝓤}} → is-least 𝟙ₒ x
𝟙ₒ-least = prop-ordinal-least 𝟙-is-prop _

𝟙ₒ-↓ : {x : 𝟙 {𝓤}} → 𝟙ₒ ↓ x ＝ 𝟘ₒ
𝟙ₒ-↓ {𝓤} {x} = prop-ordinal-↓ 𝟙-is-prop x

𝟙ₒ-↓-≃ₒ : {x : 𝟙 {𝓤}} → (𝟙ₒ ↓ x) ≃ₒ 𝟘ₒ {𝓥}
𝟙ₒ-↓-≃ₒ {𝓤} {𝓥} {x} = prop-ordinal-↓-≃ₒ 𝟙-is-prop x

only-one-𝟙ₒ-⊴ : 𝟙ₒ {𝓤} ⊴ 𝟙ₒ {𝓥}
only-one-𝟙ₒ-⊴ = prop-ordinal-⊴ 𝟙-is-prop 𝟙-is-prop (λ _ → ⋆)

only-one-𝟙ₒ : 𝟙ₒ {𝓤} ≃ₒ 𝟙ₒ {𝓥}
only-one-𝟙ₒ =
 bisimilarity-gives-ordinal-equiv 𝟙ₒ 𝟙ₒ only-one-𝟙ₒ-⊴ only-one-𝟙ₒ-⊴

only-one-𝟘ₒ-⊴ : 𝟘ₒ {𝓤} ⊴ 𝟘ₒ {𝓥}
only-one-𝟘ₒ-⊴ = prop-ordinal-⊴ 𝟘-is-prop 𝟘-is-prop 𝟘-elim

only-one-𝟘ₒ : 𝟘ₒ {𝓤} ≃ₒ 𝟘ₒ {𝓥}
only-one-𝟘ₒ =
 bisimilarity-gives-ordinal-equiv 𝟘ₒ 𝟘ₒ only-one-𝟘ₒ-⊴ only-one-𝟘ₒ-⊴

𝟙ₒ-⊴-shift : (α : Ordinal 𝓦) → 𝟙ₒ {𝓤} ⊴ α → 𝟙ₒ {𝓥} ⊴ α
𝟙ₒ-⊴-shift α = ⊴-trans 𝟙ₒ 𝟙ₒ α only-one-𝟙ₒ-⊴

𝟘ₒ-⊲⁻-𝟙ₒ : 𝟘ₒ {𝓤} ⊲⁻ 𝟙ₒ {𝓥}
𝟘ₒ-⊲⁻-𝟙ₒ = ⋆ , ≃ₒ-sym (𝟙ₒ ↓ ⋆) 𝟘ₒ (prop-ordinal-↓-≃ₒ 𝟙-is-prop ⋆)

𝟘ₒ-⊲-𝟙ₒ : 𝟘ₒ {𝓤} ⊲ 𝟙ₒ {𝓤}
𝟘ₒ-⊲-𝟙ₒ = ⌜ ⊲-is-equivalent-to-⊲⁻ 𝟘ₒ 𝟙ₒ ⌝⁻¹ 𝟘ₒ-⊲⁻-𝟙ₒ

holds-gives-equal-𝟙ₒ : {P : 𝓤 ̇  } (i : is-prop P) → P → prop-ordinal P i ＝ 𝟙ₒ
holds-gives-equal-𝟙ₒ i p = prop-ordinal-＝ i 𝟙-is-prop (λ _ → ⋆) (λ _ → p)

at-least-𝟙₀-iff-greater-than-𝟘ₒ : (α : Ordinal 𝓤) → 𝟙ₒ ⊴ α ↔ 𝟘ₒ ⊲ α
at-least-𝟙₀-iff-greater-than-𝟘ₒ α = right , left
 where
  right : 𝟙ₒ ⊴ α → 𝟘ₒ ⊲ α
  right 𝕗@(f , f-sim) = f ⋆ , (𝟙ₒ-↓ ⁻¹ ∙ simulations-preserve-↓ 𝟙ₒ α 𝕗 ⋆)

  left : 𝟘ₒ ⊲ α → 𝟙ₒ ⊴ α
  left (⊥ , p) = to-⊴ 𝟙ₒ α h
   where
    h : (x : 𝟙) → 𝟙ₒ ↓ x ⊲ α
    h ⋆ = ⊥ , (𝟙ₒ-↓ ∙ p)

\end{code}
