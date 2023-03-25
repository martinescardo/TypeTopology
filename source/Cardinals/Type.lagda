Jon Sterling, 25th March 2023.

The HoTT book shows that under excluded middle, there are weak successor
cardinals.  I show that under suitable propositional resizing assumptions, this
holds constructively.

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

module Cardinals.Type
 (fe : FunExt)
 (pe : PropExt)
 (st : set-truncations-exist)
 (pt : propositional-truncations-exist)
 (psz : Propositional-Resizing)
 (impred : (𝓤 𝓥 : Universe) → Ω-Resizing 𝓤 𝓥)
 where

open import UF.Embeddings
open import UF.Subsingletons-FunExt

import UF.Logic

open set-truncations-exist st
open propositional-truncations-exist pt
open UF.Logic.AllCombinators pt (fe _ _)

Card : (𝓤 : Universe) → 𝓤 ⁺ ̇
Card 𝓤 = set-trunc (hSet 𝓤)

Card-is-set : is-set (Card 𝓤)
Card-is-set = set-trunc-is-set

_[≤]_ : hSet 𝓤 → hSet 𝓥 → Ω (𝓤 ⊔ 𝓥)
A [≤] B = ∥ underlying-set A ↪ underlying-set B ∥Ω


_≤_ : Card 𝓤 → Card 𝓥 → Ω (𝓤 ⊔ 𝓥)
_≤_ {𝓤} {𝓥} =
 set-trunc-rec _ lem·0 λ A →
 set-trunc-rec _ lem·1 λ B →
 A [≤] B
 where
  abstract
   lem·1 : is-set (Ω (𝓤 ⊔ 𝓥))
   lem·1 = Ω-is-set (fe _ _) (pe _)

   lem·0 : is-set (Card 𝓥 → Ω (𝓤 ⊔ 𝓥))
   lem·0 = Π-is-set (fe _ _) λ _ → lem·1

module _ {𝓤 𝓥} {A : hSet 𝓤} {B : hSet 𝓥} where
 abstract
  ≤-compute : (set-trunc-in A ≤ set-trunc-in B) ＝ (A [≤] B)
  ≤-compute =
   happly (set-trunc-ind-β _ _ _ _) (set-trunc-in B)
   ∙ set-trunc-ind-β _ _ _ _

≤-refl : (α : Card 𝓤) → (α ≤ α) holds
≤-refl =
 set-trunc-ind _ (λ _ → props-are-sets (holds-is-prop (_ ≤ _))) λ A →
 transport⁻¹ _holds ≤-compute
 ∣ (id , id-is-embedding) ∣


_<_ : Card 𝓤 → Card 𝓤 → Ω (𝓤 ⁺)
α < β = (α ≤ β) ∧ (α ≢ β)

Ω' : (𝓤 : Universe) → 𝓤 ̇
Ω' 𝓤 = resized 𝓤 (Ω 𝓤) (impred _ _)

Ω'-equiv : Ω' 𝓤 ≃ Ω 𝓤
Ω'-equiv = resizing-condition _ (Ω _) (impred _ _)

resize-Ω : Ω 𝓤 → Ω 𝓥
pr₁ (resize-Ω ϕ) = resize psz (ϕ holds) (holds-is-prop ϕ)
pr₂ (resize-Ω ϕ) = resize-is-prop psz (ϕ holds) (holds-is-prop ϕ)

resize-Ω-roundtrip : (ϕ : Ω 𝓤) → resize-Ω {𝓦} (resize-Ω ϕ) ＝ ϕ
resize-Ω-roundtrip ϕ =
 to-Σ-＝
  (main ,
   being-prop-is-prop (fe _ _) _ _)
 where
  fwd : resize-Ω (resize-Ω ϕ) holds → ϕ holds
  fwd =
   from-resize psz _ (holds-is-prop ϕ)
   ∘ from-resize psz _ (resize-is-prop psz (ϕ holds) (holds-is-prop ϕ))

  bwd : ϕ holds → resize-Ω (resize-Ω ϕ) holds
  bwd =
   to-resize psz _ (resize-is-prop psz (ϕ holds) (holds-is-prop ϕ))
    ∘ to-resize psz (ϕ holds) (holds-is-prop ϕ)

  main : (resize-Ω (resize-Ω ϕ)) holds ＝ ϕ holds
  main =
   pe _
    (holds-is-prop (resize-Ω (resize-Ω ϕ)))
    (holds-is-prop ϕ)
    fwd
    bwd


resize-Ω-is-equiv : is-equiv (resize-Ω {𝓤} {𝓥})
pr₁ (pr₁ resize-Ω-is-equiv) = resize-Ω
pr₂ (pr₁ resize-Ω-is-equiv) = resize-Ω-roundtrip
pr₁ (pr₂ resize-Ω-is-equiv) = resize-Ω
pr₂ (pr₂ resize-Ω-is-equiv) = resize-Ω-roundtrip

resize-Ω-≃ : Ω 𝓤 ≃ Ω 𝓥
pr₁ resize-Ω-≃ = resize-Ω
pr₂ resize-Ω-≃ = resize-Ω-is-equiv

Ω'-is-set : is-set (Ω' 𝓤)
Ω'-is-set =
 subtypes-of-sets-are-sets
  (eqtofun Ω'-equiv)
  (equivs-are-lc _ (eqtofun- Ω'-equiv))
  (Ω-is-set (fe _ _) (pe _))

module _ {𝓤 : Universe} where
 powerset : (A : 𝓤 ̇ ) → hSet 𝓤
 pr₁ (powerset A) = A → Ω' 𝓤
 pr₂ (powerset A) =
  Π-is-set (fe _ _) λ _ →
  Ω'-is-set

 singleton-embedding' : (A : hSet 𝓤) → underlying-set A ↪ (underlying-set A → Ω 𝓤)
 pr₁ (singleton-embedding' A) x y = (x ＝ y) , underlying-set-is-set A
 pr₂ (singleton-embedding' A) ϕ = main
  where
   main : is-prop (Σ z ꞉ underlying-set A , (λ y → (z ＝ y) , pr₂ A) ＝ ϕ)
   main (u , Hu) (v , Hv) =
    to-Σ-＝
     (transport id (ap pr₁ (happly (Hv ∙ Hu ⁻¹) v)) refl ,
      Π-is-set (fe _ _) (λ _ → Ω-is-set (fe _ _) (pe _)) _ _)

 singleton-embedding : (A : hSet 𝓤) → underlying-set A ↪ (underlying-set A → Ω' 𝓤)
 singleton-embedding A = aux ∘↪ singleton-embedding' A
  where
   aux : _ ↪ _
   pr₁ aux = back-eqtofun Ω'-equiv ∘_
   pr₂ aux =
    lc-maps-into-sets-are-embeddings _
     (λ ϕ →
      dfunext (fe _ _) λ z →
      let ψ = happly ϕ z in
      equivs-are-lc _ (inverses-are-equivs _ (pr₂ Ω'-equiv)) ψ)
     (Π-is-set (fe _ _) (λ _ → Ω'-is-set))

[weak-successor] : (A : hSet 𝓤) → Σ β ꞉ Card 𝓤 , (set-trunc-in A < β) holds
pr₁ ([weak-successor] A) =
 set-trunc-in (powerset (underlying-set A))
pr₁ (pr₂ ([weak-successor] A)) =
 transport⁻¹
  _holds
  ≤-compute
  ∣ singleton-embedding A ∣
pr₂ (pr₂ ([weak-successor] A)) H =
 ∥∥-rec 𝟘-is-prop main lem2
 where
  lem : (set-trunc-in (powerset (underlying-set A)) ≤ set-trunc-in A) holds
  lem = transport (λ β → (β ≤ set-trunc-in A) holds) H (≤-refl _)

  lem2 : (powerset (underlying-set A) [≤] A) holds
  lem2 = transport _holds ≤-compute lem

  main : ((underlying-set A → Ω' 𝓤) ↪ underlying-set A) → 𝟘
  main ι =
   LFTP.retract-version.cantor-theorem-for-embeddings fe pe psz
    (underlying-set A)
    ι'
    ι'-emb
   where
    Q : Ω₀ ≃ Ω' 𝓤
    Q = resize-Ω-≃ ● (≃-sym Ω'-equiv)

    ι' : (underlying-set A → Ω₀) → underlying-set A
    ι' U = pr₁ ι (eqtofun Q ∘ U)

    ι'-lc : left-cancellable ι'
    ι'-lc {U} {V} ϕ =
     dfunext (fe _ (𝓤₀ ⁺)) λ x →
     equivs-are-lc (eqtofun Q) (pr₂ Q)
      (happly (embeddings-are-lc (pr₁ ι) (pr₂ ι) ϕ) x)

    ι'-emb : is-embedding ι'
    ι'-emb =
     lc-maps-into-sets-are-embeddings _
      ι'-lc
      (underlying-set-is-set A)

weak-successor : (α : Card 𝓤) → Σ β ꞉ Card 𝓤 , (α < β) holds
weak-successor =
 set-trunc-ind _ lem [weak-successor]
 where
  abstract
   lem : (α : Card 𝓤) → is-set (Σ β ꞉ Card 𝓤 , (α < β) holds)
   lem α =
    Σ-is-set Card-is-set λ β →
    props-are-sets (holds-is-prop (α < β))
