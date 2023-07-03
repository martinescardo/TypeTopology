Ayberk Tosun, 30 June 2023

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt
open import UF.EquivalenceExamples
open import MLTT.List hiding ([_])
open import MLTT.Pi
open import UF.Subsingletons
open import UF.Logic

module Locales.ScottLocale
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe)
        where

open Universal fe
open Implication fe
open import Locales.Frame pt fe
open import DomainTheory.Basics.Dcpo pt fe 𝓥 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓥 hiding (Fam)

module DefnOfScottLocale (𝓓 : DCPO {𝓤} {𝓣}) (𝓦 : Universe) where

 open DefnOfScottTopology 𝓓 𝓦

 𝒪ₛ : 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓣  ̇
 𝒪ₛ = Σ P ꞉ (⟨ 𝓓 ⟩∙ → Ω 𝓦) , is-scott-open P holds

 _≤ₛ_ : 𝒪ₛ → 𝒪ₛ → Ω (𝓤 ⊔ 𝓦)
 (U , _) ≤ₛ (V , _) = Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , U x ⇒ V x

 ⊤ₛ : 𝒪ₛ
 ⊤ₛ = (λ _ → ⊤Ω {𝓦}) , υ , ι
  where
   υ : is-upwards-closed (λ _ → ⊤Ω) holds
   υ _ _ _ _ = ⋆

   ι : is-inaccessible-by-directed-joins (λ _ → ⊤Ω) holds
   ι S ⋆ = {!∣ ? ∣!}

 𝒪ₛ-frame-structure : frame-structure (𝓤 ⊔ 𝓦) {!!} 𝒪ₛ
 𝒪ₛ-frame-structure = (_≤ₛ_ , ⊤ₛ , {!!}) , {!!}

 ScottLocale : Locale (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓦) {!!}
 ScottLocale = record { ⟨_⟩ₗ = 𝒪ₛ ; frame-str-of = 𝒪ₛ-frame-structure }

\end{code}
