Jon Sterling, 25th March 2023.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Retracts
open import UF.SetTrunc
open import UF.Size
open import UF.Subsingletons
import Various.LawvereFPT as LFTP

module Cardinals.Preorder
 (fe : FunExt)
 (pe : PropExt)
 (st : set-truncations-exist)
 (pt : propositional-truncations-exist)
 where

open import UF.Embeddings
open import UF.Subsingletons-FunExt
open import Cardinals.Type st

import UF.Logic

open set-truncations-exist st
open propositional-truncations-exist pt
open UF.Logic.AllCombinators pt (fe _ _)

_[≤]_ : hSet 𝓤 → hSet 𝓥 → Ω (𝓤 ⊔ 𝓥)
A [≤] B = ∥ underlying-set A ↪ underlying-set B ∥Ω

module _ {𝓤 𝓥} where
 _≤_ : Card 𝓤 → Card 𝓥 → Ω (𝓤 ⊔ 𝓥)
 _≤_ =
  set-trunc-rec _ lem·0 λ A →
  set-trunc-rec _ lem·1 λ B →
  A [≤] B
  where
   abstract
    lem·1 : is-set (Ω (𝓤 ⊔ 𝓥))
    lem·1 = Ω-is-set (fe _ _) (pe _)

    lem·0 : is-set (Card 𝓥 → Ω (𝓤 ⊔ 𝓥))
    lem·0 = Π-is-set (fe _ _) λ _ → lem·1

module _ {A : hSet 𝓤} {B : hSet 𝓥} where
 abstract
  ≤-compute : (set-trunc-in A ≤ set-trunc-in B) ＝ (A [≤] B)
  ≤-compute =
   happly (set-trunc-ind-β _ _ _ _) (set-trunc-in B)
   ∙ set-trunc-ind-β _ _ _ _

≤-refl : (α : Card 𝓤) → (α ≤ α) holds
≤-refl =
 set-trunc-ind _ (λ _ → props-are-sets (holds-is-prop (_ ≤ _))) λ A →
 transport⁻¹ _holds ≤-compute
 ∣ id , id-is-embedding ∣

-- TODO: prove transitivity

_<_ : Card 𝓤 → Card 𝓤 → Ω (𝓤 ⁺)
α < β = (α ≤ β) ∧ (α ≢ β)
