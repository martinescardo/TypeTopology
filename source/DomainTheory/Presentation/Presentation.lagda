(...)

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
open import MLTT.Spartan hiding (J)

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Presentation.Presentation
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤 𝓥 𝓦 : Universe)
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

  cover-set : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
  cover-set = G → {I : 𝓥 ̇} → (I → G) → Ω 𝓦

  is-dcpo-presentation : cover-set → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇
  is-dcpo-presentation _◃_ = ≲-prop-valued × ≲-reflexive × ≲-transitive × cover-directed
    where
      ≲-prop-valued = {x y : G} → is-prop (x ≲ y)
      ≲-reflexive = {x : G} → x ≲ x
      ≲-transitive = {x y z : G} → x ≲ y → y ≲ z → x ≲ z
      cover-directed = {x : G} {I : 𝓥 ̇} {U : I → G} → (x ◃ U) holds
        → is-directed _≲_ U

  -- TODO: Define structure and projections
  -- and characterize paths (better paths using powersets)

  module Interpretation
    (_◃_ : cover-set)
    (◃-is-dcpo-presentation : is-dcpo-presentation _◃_)
    {𝓓 : DCPO {𝓤} {𝓣}}
    where  -- Defines maps from a presentation into dcpos

    private
      U-is-directed : {x : G} {I : 𝓥 ̇} {U : I → G} → (x ◃ U) holds
        → is-directed _≲_ U
      U-is-directed = ◃-is-dcpo-presentation .pr₂ .pr₂ .pr₂

      _≤_ = underlying-order 𝓓

    preserves-covers : (f : G → ⟨ 𝓓 ⟩)
      → ((x y : G) → x ≲ y → f x ⊑⟨ 𝓓 ⟩ f y)
      → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇
    preserves-covers f m = {x : G} {I : 𝓥 ̇} {U : I → G}
      → (c : (x ◃ U) holds)
      → f x  ⊑⟨ 𝓓 ⟩  ∐ 𝓓 (image-is-directed _≲_ _≤_ m (U-is-directed c))

\end{code}
