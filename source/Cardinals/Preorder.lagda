Jon Sterling, 25th March 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

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

[≤]-trans
 : (A : hSet 𝓤) (B : hSet 𝓥) (C : hSet 𝓦)
 → (A [≤] B) holds
 → (B [≤] C) holds
 → (A [≤] C) holds
[≤]-trans A B C =
 ∥∥-rec (Π-is-prop (fe _ _) (λ _ → holds-is-prop (A [≤] C))) λ AB →
 ∥∥-rec (holds-is-prop (A [≤] C)) λ BC →
 ∣ BC ∘↪ AB ∣

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

  ≤-compute-out : (set-trunc-in A ≤ set-trunc-in B) holds → (A [≤] B) holds
  ≤-compute-out = transport _holds ≤-compute

  ≤-compute-in : (A [≤] B) holds → (set-trunc-in A ≤ set-trunc-in B) holds
  ≤-compute-in = transport⁻¹ _holds ≤-compute

≤-refl : (α : Card 𝓤) → (α ≤ α) holds
≤-refl =
 set-trunc-ind _ lem λ A →
 ≤-compute-in ∣ id , id-is-embedding ∣
 where
  lem : (_ : _) → is-set _
  lem _ = props-are-sets (holds-is-prop (_ ≤ _))

≤-trans
 : (α : Card 𝓤) (β : Card 𝓥) (γ : Card 𝓦)
 → (α ≤ β) holds
 → (β ≤ γ) holds
 → (α ≤ γ) holds
≤-trans =
 set-trunc-ind _ lem·0 λ A →
 set-trunc-ind _ (lem·1 A) λ B →
 set-trunc-ind _ (lem·2 A B) λ C →
 λ AB BC →
 ≤-compute-in
  ([≤]-trans A B C
    (≤-compute-out AB)
    (≤-compute-out BC))
 where
  lem·2 : (A : hSet _) (B : hSet _) (_ : Card _) → is-set _
  lem·2 A B γ =
   Π-is-set (fe _ _) λ _ →
   Π-is-set (fe _ _) λ _ →
   props-are-sets (holds-is-prop (_ ≤ _))

  lem·1 : (A : hSet _) (β : Card _) → is-set _
  lem·1 A β =
   Π-is-set (fe _ _) λ _ →
   Π-is-set (fe _ _) λ _ →
   Π-is-set (fe _ _) λ _ →
   props-are-sets (holds-is-prop (_ ≤ _))

  lem·0 : (α : Card _) → is-set _
  lem·0 α =
   Π-is-set (fe _ _) λ _ →
   Π-is-set (fe _ _) λ _ →
   Π-is-set (fe _ _) λ _ →
   Π-is-set (fe _ _) λ _ →
   props-are-sets (holds-is-prop (_ ≤ _))


module _ {𝓤} where
 ⊥ : Ω 𝓤
 pr₁ ⊥ = 𝟘
 pr₂ ⊥ = 𝟘-is-prop

 Ω¬_ : Ω 𝓤 → Ω 𝓤
 Ω¬ ϕ = ϕ ⇒ ⊥

_<_ : Card 𝓤 → Card 𝓥 → Ω (𝓤 ⊔ 𝓥)
α < β = (α ≤ β) ∧ (Ω¬ (β ≤ α))
