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

\end{code}
