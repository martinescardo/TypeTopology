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
open import Ordinals.AdditionProperties ua
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

only-one-𝟙ₒ-⊴ : 𝟙ₒ {𝓤} ⊴ 𝟙ₒ {𝓥}
only-one-𝟙ₒ-⊴ = prop-ordinal-⊴ 𝟙-is-prop 𝟙-is-prop (λ _ → ⋆)

𝟙ₒ-⊴-shift : (α : Ordinal 𝓦) → 𝟙ₒ {𝓤} ⊴ α → 𝟙ₒ {𝓥} ⊴ α
𝟙ₒ-⊴-shift α = ⊴-trans 𝟙ₒ 𝟙ₒ α only-one-𝟙ₒ-⊴

𝟘ₒ-⊲⁻-𝟙ₒ : 𝟘ₒ {𝓤} ⊲⁻ 𝟙ₒ {𝓥}
𝟘ₒ-⊲⁻-𝟙ₒ = ⋆ , ≃ₒ-sym (𝟙ₒ ↓ ⋆) 𝟘ₒ (prop-ordinal-↓-≃ₒ 𝟙-is-prop ⋆)

𝟘ₒ-⊲-𝟙ₒ : 𝟘ₒ {𝓤} ⊲ 𝟙ₒ {𝓤}
𝟘ₒ-⊲-𝟙ₒ = ⌜ ⊲-is-equivalent-to-⊲⁻ 𝟘ₒ 𝟙ₒ ⌝⁻¹ 𝟘ₒ-⊲⁻-𝟙ₒ

\end{code}