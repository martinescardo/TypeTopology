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
open Existential pt
open Conjunction
open import Locales.Frame pt fe
open import DomainTheory.Basics.Dcpo pt fe 𝓥 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓥 hiding (Fam; index; _[_])

open PropositionalTruncation pt

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
   ι (S , (∣i∣ , γ)) ⋆ = ∥∥-rec ∃-is-prop † ∣i∣
    where
     † : index S → ∃ _ ꞉ index S , ⊤Ω holds
     † i = ∣ i , ⋆ ∣

 _∧ₛ_ : 𝒪ₛ → 𝒪ₛ → 𝒪ₛ
 (U , (υ₁ , ι₁)) ∧ₛ (V , (υ₂ , ι₂)) = (λ x → U x ∧ V x) , υ , ι
  where
   υ : is-upwards-closed (λ x → U x ∧ V x) holds
   υ x y (p₁ , p₂) q = υ₁ x y p₁ q , υ₂ x y p₂ q

   ι : is-inaccessible-by-directed-joins (λ x → U x ∧ V x) holds
   ι (S , δ) (p , q) = ∥∥-rec₂ ∃-is-prop γ (ι₁ (S , δ) p) (ι₂ (S , δ) q)
    where
     γ : Σ i ꞉ index S , U (S [ i ]) holds
       → Σ j ꞉ index S , V (S [ j ]) holds
       → ∃ k ꞉ index S , (U (S [ k ]) ∧ V (S [ k ])) holds
     γ (i , r₁) (j , r₂) = ∥∥-rec ∃-is-prop † (pr₂ δ i j)
      where
       † : Σ k₀ ꞉ index S ,
            ((S [ i ]) ⊑⟨ 𝓓 ⟩ₚ (S [ k₀ ]) ∧ (S [ j ]) ⊑⟨ 𝓓 ⟩ₚ (S [ k₀ ])) holds
         → ∃ k ꞉ index S , (U (S [ k ]) ∧ V (S [ k ])) holds
       † (k₀ , φ , ψ) =
        ∣ k₀ , υ₁ (S [ i ]) (S [ k₀ ]) r₁ φ , υ₂ (S [ j ]) (S [ k₀ ]) r₂ ψ ∣

 ⋁ₛ_ : Fam 𝓦 𝒪ₛ → 𝒪ₛ
 ⋁ₛ_ S = ⋃S , υ , ι
  where
   ⋃S : ⟨ 𝓓 ⟩∙ → Ω 𝓦
   ⋃S = λ x → Ǝ i ꞉ index S , pr₁ (S [ i ]) x holds

   υ : is-upwards-closed ⋃S holds
   υ x y p q = ∥∥-rec (holds-is-prop (⋃S y)) † p
    where
     † : Σ i ꞉ index S , (S [ i ]) .pr₁ x holds → ⋃S y holds
     † (i , r) = ∣ i , pr₁ (pr₂ (S [ i ])) x y r q ∣

   ι : {!!}
   ι = {!!}

 ⊤ₛ-is-top : (U : 𝒪ₛ) → (U ≤ₛ ⊤ₛ) holds
 ⊤ₛ-is-top = {!!}

 𝒪ₛ-frame-structure : frame-structure (𝓤 ⊔ 𝓦) 𝓦 𝒪ₛ
 𝒪ₛ-frame-structure = (_≤ₛ_ , ⊤ₛ , _∧ₛ_ , ⋁ₛ_) , (({!!} , {!!}) , {!!}) , ⊤ₛ-is-top , {!!}

 ScottLocale : Locale (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦 ⁺) (𝓤 ⊔ 𝓦) 𝓦
 ScottLocale = record { ⟨_⟩ₗ = 𝒪ₛ ; frame-str-of = 𝒪ₛ-frame-structure }

\end{code}
