(...)

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Presentation.Type
  (pt : propositional-truncations-exist)
  (fe : Fun-Ext)
  {𝓤 𝓣 𝓥 𝓦 : Universe}
  -- 𝓤 : the universe of the underlying set
  -- 𝓣 : the universe of the preorder
  -- 𝓥 : the universe of the indices of directed sets
  -- 𝓦 : the universe of covering sets
 where

open import UF.Powerset
open import Posets.Poset fe
open PosetAxioms

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥

module _
  (G : 𝓤 ̇)  -- Generators
  (_≲_ : G → G → 𝓣 ̇)
  where

  Cover-set : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇ -- This one has spurious assumptions
  Cover-set = G → {I : 𝓥 ̇} → (I → G) → Ω 𝓦

  is-dcpo-presentation : Cover-set → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇
  is-dcpo-presentation _◃_ = (≲-prop-valued × ≲-reflexive × ≲-transitive) × Cover-directed
   where
    ≲-prop-valued = {x y : G} → is-prop (x ≲ y)
    ≲-reflexive = {x : G} → x ≲ x
    ≲-transitive = {x y z : G} → x ≲ y → y ≲ z → x ≲ z
    Cover-directed = {x : G} {I : 𝓥 ̇} {U : I → G} → (x ◃ U) holds → is-directed _≲_ U

DCPO-Presentation : (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)⁺ ̇
DCPO-Presentation =
 Σ G ꞉ 𝓤 ̇ ,
 Σ _⊑_ ꞉ (G → G → 𝓣 ̇) ,
 Σ _◃_ ꞉ (Cover-set G _⊑_) ,
 (is-dcpo-presentation G _⊑_ _◃_)

module _ (𝓖 : DCPO-Presentation) where
 ⟨_⟩ₚ : 𝓤 ̇ -- We need a uniform way to refer to underlying sets
 ⟨_⟩ₚ = 𝓖 .pr₁

 underlying-preorder = 𝓖 .pr₂ .pr₁

 cover-set = 𝓖 .pr₂ .pr₂ .pr₁ -- better syntax?

 cover-directed = 𝓖 .pr₂ .pr₂ .pr₂ .pr₂

-- Defines maps from a presentation into dcpos
module Interpretation (𝓖 : DCPO-Presentation) (𝓓 : DCPO {𝓤} {𝓣}) where
 private
  _≤_ = underlying-order 𝓓
  _≲_ = underlying-preorder 𝓖
  _◃_ = cover-set 𝓖

 preserves-covers
  : (f : ⟨ 𝓖 ⟩ₚ → ⟨ 𝓓 ⟩)
  → ((x y : ⟨ 𝓖 ⟩ₚ) → x ≲ y → f x ≤ f y)
  → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇
 preserves-covers f m =
  {x : ⟨ 𝓖 ⟩ₚ} {I : 𝓥 ̇} {U : I → ⟨ 𝓖 ⟩ₚ}
  → (c : (x ◃ U) holds)
  → f x ≤ ∐ 𝓓 (image-is-directed _≲_ _≤_ m (cover-directed 𝓖 c))

\end{code}
