Ayberk Tosun, 29 September 2023

This module contains a definition of the Scott locale of a dcpo, using the definition of
dcpo from the `DomainTheory` development due to Tom de Jong.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Powerset-MultiUniverse hiding (_⊆_)
open import UF.UA-FunExt
open import UF.Univalence
open import Slice.Family

\end{code}

We assume the existence of propositional truncations as well as function extensionality.

\begin{code}

module Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤  : Universe)
        where

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open import Locales.Frame pt fe

open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤

open import Locales.ScottLocale.Definition pt fe 𝓤

open PropositionalTruncation pt

\end{code}

\begin{code}

module ScottLocaleConstruction (𝓓 : DCPO {𝓤 ⁺} {𝓤}) (hscb : has-specified-small-compact-basis 𝓓) (pe : propext 𝓤) where

 open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
 open DefnOfScottTopology 𝓓 𝓤
 open DefnOfScottLocale 𝓓 𝓤 pe using (𝒪ₛ-equality)

\end{code}

`𝒪ₛ` is the type of 𝓦-Scott-opens over dcpo `𝓓`.

\begin{code}

 𝕒 : structurally-algebraic 𝓓
 𝕒 = structurally-algebraic-if-specified-small-compact-basis 𝓓 hscb

\end{code}

We denote by `I` the index type of the basis:

\begin{code}

 I = pr₁ hscb
 β = pr₁ (pr₂ hscb)

 ℬ : Fam 𝓤 ⟨ 𝓓 ⟩∙
 ℬ = (I , β)

\end{code}

These are ordered by inclusion.

\begin{code}

 open structurally-algebraic

 _⊆ₛ_ : 𝒪ₛ → 𝒪ₛ → Ω 𝓤
 (U , _) ⊆ₛ (V , _) = Ɐ i ꞉ I , U (ℬ [ i ]) ⇒ V (ℬ [ i ])

 _⊆_ : 𝒪ₛ → 𝒪ₛ → Ω (𝓤 ⁺)
 (U , _) ⊆ (V , _) = Ɐ x ꞉ ⟨ 𝓓 ⟩∙ , U x ⇒ V x

 ⊆ₛ-is-reflexive : is-reflexive _⊆ₛ_ holds
 ⊆ₛ-is-reflexive (U , δ) _ = id

 ⊆ₛ-is-transitive : is-transitive _⊆ₛ_ holds
 ⊆ₛ-is-transitive (U , δ) (V , ϵ) (W , ζ) p q x = q x ∘ p x

 ⊆ₛ-implies-⊆ : (𝔘 𝔙 : 𝒪ₛ) → (𝔘 ⊆ₛ 𝔙 ⇒ 𝔘 ⊆ 𝔙) holds
 ⊆ₛ-implies-⊆ 𝔘@(U , ι₁ , υ₁) 𝔙@(V , ι₂ , υ₂) φ x p =
  transport (λ - → (- ∈ₛ 𝔙) holds) (eq ⁻¹) †
   where
    S : Fam 𝓤 ⟨ 𝓓 ⟩∙
    S = index-of-compact-family 𝕒 x , compact-family 𝕒 x

    S↑ : Fam↑
    S↑ = S , compact-family-is-directed 𝕒 x

    eq : x ＝ ⋁ S↑
    eq = compact-family-∐-＝ 𝕒 x ⁻¹

    p′ : ((⋁ S↑) ∈ₛ 𝔘) holds
    p′ = transport (λ - → (- ∈ₛ 𝔘) holds) eq p

    † : ((⋁ S↑) ∈ₛ 𝔙) holds
    † = ∥∥-rec (holds-is-prop ((⋁ S↑) ∈ₛ 𝔙)) ‡ (υ₁ S↑ p′)
     where
      ‡ : Σ i ꞉ index S , ((S [ i ]) ∈ₛ 𝔘) holds → ((⋁ S↑) ∈ₛ 𝔙) holds
      ‡ (i , q) = ι₂ (S [ i ]) (⋁ S↑) r (⋁-is-upperbound S↑ i)
       where
        r : ((S [ i ]) ∈ₛ 𝔙) holds
        r = φ (pr₁ i) q

 𝒪ₛ-equalityₛ : (U V : 𝒪ₛ)
              → ((i : I) → (ℬ [ i ]) ∈ₛ U  ＝ (ℬ [ i ]) ∈ₛ V)
              → U ＝ V
 𝒪ₛ-equalityₛ 𝔘@(U , (υ , ι)) 𝔙 φ =
  to-subtype-＝ (holds-is-prop ∘ is-scott-open) (dfunext fe †)
   where
    † : (x : ⟨ 𝓓 ⟩∙) → x ∈ₛ 𝔘 ＝ x ∈ₛ 𝔙
    † x = to-subtype-＝ (λ _ → being-prop-is-prop fe) ‡
     where
      foo : (𝔘 ⊆ₛ 𝔙) holds
      foo i p = transport (λ - → - holds) (φ i) p

      bar : (𝔙 ⊆ₛ 𝔘) holds
      bar i p = transport _holds (φ i ⁻¹) p

      ♣ : (x ∈ₛ 𝔘 ⇒ x ∈ₛ 𝔙) holds
      ♣ = ⊆ₛ-implies-⊆ 𝔘 𝔙 foo x

      ♠ : (x ∈ₛ 𝔙 ⇒ x ∈ₛ 𝔘) holds
      ♠ = ⊆ₛ-implies-⊆ 𝔙 𝔘 bar x

      ‡ : (x ∈ₛ 𝔘) holds ＝ (x ∈ₛ 𝔙) holds
      ‡ = pe (holds-is-prop (x ∈ₛ 𝔘)) (holds-is-prop (x ∈ₛ 𝔙)) ♣ ♠

 ⊆-is-antisymmetric : is-antisymmetric _⊆_
 ⊆-is-antisymmetric {𝔘} {𝔙} p q =
  𝒪ₛ-equality 𝔘 𝔙
   (dfunext fe λ x →
     to-subtype-＝
      (λ _ → being-prop-is-prop fe)
      (pe (holds-is-prop (x ∈ₛ 𝔘)) (holds-is-prop (x ∈ₛ 𝔙)) (p x) (q x)))

 ⊆ₛ-is-antisymmetric : is-antisymmetric _⊆ₛ_
 ⊆ₛ-is-antisymmetric {𝔘} {𝔙} p q = ⊆-is-antisymmetric † ‡
  where
   † : (𝔘 ⊆ 𝔙) holds
   † = ⊆ₛ-implies-⊆ 𝔘 𝔙 p

   ‡ : (𝔙 ⊆ 𝔘) holds
   ‡ = ⊆ₛ-implies-⊆ 𝔙 𝔘 q

 ⊆ₛ-is-partial-order : is-partial-order 𝒪ₛ _⊆ₛ_
 ⊆ₛ-is-partial-order = (⊆ₛ-is-reflexive , ⊆ₛ-is-transitive) , ⊆ₛ-is-antisymmetric

\end{code}

\begin{code}

 ⊤ₛ : 𝒪ₛ
 ⊤ₛ = (λ _ → ⊤ {𝓤}) , υ , ι
  where
   υ : is-upwards-closed (λ _ → ⊤) holds
   υ _ _ _ _ = ⋆

   ι : is-inaccessible-by-directed-joins (λ _ → ⊤) holds
   ι (S , (∣i∣ , γ)) ⋆ = ∥∥-rec ∃-is-prop † ∣i∣
    where
     † : index S → ∃ _ ꞉ index S , ⊤ holds
     † i = ∣ i , ⋆ ∣

 ⊤ₛ-is-top : (U : 𝒪ₛ) → (U ⊆ₛ ⊤ₛ) holds
 ⊤ₛ-is-top U = λ _ _ → ⋆

\end{code}

\begin{code}

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

 open Meets _⊆ₛ_

 ∧ₛ-is-meet : (U V : 𝒪ₛ) → ((U ∧ₛ V) is-glb-of ((U , V))) holds
 ∧ₛ-is-meet U V = † , ‡
  where
   † : ((U ∧ₛ V) is-a-lower-bound-of (U , V)) holds
   † = (λ _ (p , _) → p) , (λ _ (_ , q) → q)

   ‡ : ((W , _) : lower-bound (U , V)) → (W ⊆ₛ (U ∧ₛ V)) holds
   ‡ (W , p) x q = pr₁ p x q , pr₂ p x q

\end{code}

\begin{code}

 ⋁ₛ_ : Fam 𝓤 𝒪ₛ → 𝒪ₛ
 ⋁ₛ_ S@(_ , up) = from-𝒪ₛᴿ 𝔘
  where
   open 𝒪ₛᴿ

   ⋃S : 𝓟 {𝓤} ⟨ 𝓓 ⟩∙
   ⋃S x = Ǝ i ꞉ index S , (x ∈ₛ (S [ i ])) holds

   υ : is-upwards-closed ⋃S holds
   υ x y p q = ∥∥-rec (holds-is-prop (⋃S y)) † p
    where
     † : Σ i ꞉ index S , (x ∈ₛ (S [ i ])) holds → ⋃S y holds
     † (i , r) = ∣ i , ♣ ∣
      where
       Sᵢᴿ : 𝒪ₛᴿ
       Sᵢᴿ = to-𝒪ₛᴿ (S [ i ])

       ♣ : (y ∈ₛ (S [ i ])) holds
       ♣ = pred-is-upwards-closed Sᵢᴿ x y r q

   ι : is-inaccessible-by-directed-joins ⋃S holds
   ι (T , δ) p = ∥∥-rec ∃-is-prop † p
    where
     † : Σ i ꞉ index S , ((⋁ (T , δ)) ∈ₛ (S [ i ])) holds
       → ∃ i ꞉ index T , ⋃S (T [ i ]) holds
     † (i , r) = ∥∥-rec ∃-is-prop ‡ ♠
      where

       Sᵢᴿ : 𝒪ₛᴿ
       Sᵢᴿ = to-𝒪ₛᴿ (S [ i ])

       ♠ : ∃ k ꞉ index T , pred Sᵢᴿ (T [ k ]) holds
       ♠ = pred-is-inaccessible-by-dir-joins Sᵢᴿ (T , δ) r

       ‡ : (Σ k ꞉ index T , pred Sᵢᴿ (T [ k ]) holds)
         → ∃ i ꞉ index T , ⋃S (T [ i ]) holds
       ‡ (k , q) = ∣ k , ∣ i , q ∣ ∣

   𝔘 : 𝒪ₛᴿ
   𝔘 = record
        { pred                              = ⋃S
        ; pred-is-upwards-closed            = υ
        ; pred-is-inaccessible-by-dir-joins = ι
        }

\end{code}
