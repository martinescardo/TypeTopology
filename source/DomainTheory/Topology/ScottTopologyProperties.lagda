---
title:      Properties of the Scott topology
author:     Ayberk Tosun
start-date: 2023-10-30
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.SubtypeClassifier

module DomainTheory.Topology.ScottTopologyProperties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe) where

open import UF.Logic
open Existential pt
open Implication fe
open Universal   fe
open Conjunction

open import UF.Size
open import UF.Equiv

open import UF.Powerset-MultiUniverse
open import Slice.Family

open PropositionalTruncation pt

open import DomainTheory.Topology.ScottTopology        pt fe 𝓥
open import DomainTheory.Basics.Dcpo                   pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥
open import DomainTheory.Basics.WayBelow               pt fe 𝓥

\end{code}

\begin{code}

principal-filter : (𝓓 : DCPO {𝓤} {𝓥}) → ⟨ 𝓓 ⟩ → 𝓟 ⟨ 𝓓 ⟩
principal-filter 𝓓 c x = c ⊑⟨ 𝓓 ⟩ x , prop-valuedness 𝓓 c x

infix 45 principal-filter

syntax principal-filter 𝓓 x = ↑[ 𝓓 ] x

\end{code}

Let `D` be a dcpo and consider a compact element `c : D` of it. The
upwards-closure of `c` is then a Scott open.

\begin{code}

module Properties (𝓓 : DCPO {𝓤} {𝓥}) where

 open DefnOfScottTopology 𝓓 𝓥

 principal-filter-is-upwards-closed : (x : ⟨ 𝓓 ⟩)
                                    → is-upwards-closed (↑[ 𝓓 ] x) holds
 principal-filter-is-upwards-closed x y z p q =
  x ⊑⟨ 𝓓 ⟩[ p ] y ⊑⟨ 𝓓 ⟩[ q ] z ∎⟨ 𝓓 ⟩

 compact-implies-principal-filter-is-scott-open : (c : ⟨ 𝓓 ⟩)
                                                → is-compact 𝓓 c
                                                → is-scott-open (↑[ 𝓓 ] c) holds
 compact-implies-principal-filter-is-scott-open c κ = Ⅰ , Ⅱ
  where
   Ⅰ : is-upwards-closed (↑[ 𝓓 ] c) holds
   Ⅰ = principal-filter-is-upwards-closed c

   Ⅱ : is-inaccessible-by-directed-joins (↑[ 𝓓 ] c) holds
   Ⅱ (S , δ) = κ (index S) (S [_]) δ

\end{code}

Conversely, if the principal filter is Scott open then `c` is a compact element.

\begin{code}

 principal-filter-scott-open-implies-compact : (c : ⟨ 𝓓 ⟩)
                                             → is-scott-open (↑[ 𝓓 ] c) holds
                                             → is-compact 𝓓 c
 principal-filter-scott-open-implies-compact c (υ , κ) I ι δ p =
  κ ((I , ι) , δ) p

\end{code}

We can now record this as a logical equivalence.

\begin{code}

 principal-filter-scott-open-iff-compact :
  (x : ⟨ 𝓓 ⟩) → is-scott-open (↑[ 𝓓 ] x) holds ↔ is-compact 𝓓 x
 principal-filter-scott-open-iff-compact x = Ⅰ , Ⅱ
  where
   Ⅰ = principal-filter-scott-open-implies-compact x
   Ⅱ = compact-implies-principal-filter-is-scott-open x

\end{code}

Notation for the principal Scott open.

\begin{code}

 ↑ˢ[_] : (Σ c ꞉ ⟨ 𝓓 ⟩ , is-compact 𝓓 c) → Σ S ꞉ 𝓟 {𝓥} ⟨ 𝓓 ⟩ , is-scott-open S holds
 ↑ˢ[ (c , κ) ] =
  principal-filter 𝓓 c , compact-implies-principal-filter-is-scott-open c κ

\end{code}

We now prove some properties of the Scott topology on a dcpo that is algebraic.

\begin{code}

module PropertiesAlgebraic (𝓓 : DCPO {𝓤} {𝓥})
                           (𝕒 : structurally-algebraic 𝓓) where

 open DefnOfScottTopology 𝓓 𝓥

 open structurally-algebraic

 is-compactₚ : ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓥 ⁺)
 is-compactₚ x = is-compact 𝓓 x , being-compact-is-prop 𝓓 x

 join-of-compact-opens : 𝓟 {𝓥} ⟨ 𝓓 ⟩ → 𝓟 {𝓤 ⊔ 𝓥 ⁺} ⟨ 𝓓 ⟩
 join-of-compact-opens U x =
  Ǝ c ꞉ ⟨ 𝓓 ⟩ , (is-compactₚ c ∧ c ∈ₚ U ∧ x ∈ₚ (↑[ 𝓓 ] c)) holds

 characterization-of-scott-opens₁ : (U : 𝓟 ⟨ 𝓓 ⟩)
                                  → is-scott-open U holds
                                  → U ⊆ join-of-compact-opens U
 characterization-of-scott-opens₁ U (υ , ξ) x p = †
  where
   S : Fam 𝓥 ⟨ 𝓓 ⟩
   S = index-of-compact-family 𝕒 x , compact-family 𝕒 x

   S↑ : Fam↑
   S↑ = S , compact-family-is-directed 𝕒 x

   q : x ＝ ⋁ S↑
   q = compact-family-∐-＝ 𝕒 x ⁻¹

   κ : (i : index S) → is-compactₚ (S [ i ]) holds
   κ = compact-family-is-compact 𝕒 x

   ψ : is-upperbound (underlying-order 𝓓) x (S [_])
   ψ i = transport (λ - → (S [ i ]) ⊑⟨ 𝓓 ⟩ -) (q ⁻¹) (⋁-is-upperbound S↑ i)

   φ : (⋁ S↑) ∈ U
   φ = transport (λ - → - ∈ U) q p

   ‡ : Σ i ꞉ index S , (S [ i ]) ∈ U
     → ∃ c₀ ꞉ ⟨ 𝓓 ⟩ , (is-compactₚ c₀ ∧ c₀ ∈ₚ U ∧ x ∈ₚ ↑[ 𝓓 ] c₀) holds
   ‡ (i , μ) = ∣ S [ i ] , κ i , μ , ψ i ∣

   † : ∃ c₀ ꞉ ⟨ 𝓓 ⟩ , (is-compactₚ c₀ ∧ c₀ ∈ₚ U ∧ x ∈ₚ ↑[ 𝓓 ] c₀) holds
   † = ∥∥-rec ∃-is-prop ‡ (ξ S↑ φ)

 characterization-of-scott-opens₂ : (U : 𝓟 ⟨ 𝓓 ⟩)
                                  → is-scott-open U holds
                                  → join-of-compact-opens U ⊆ U
 characterization-of-scott-opens₂ U (υ , _) x p =
  ∥∥-rec (holds-is-prop (x ∈ₚ U)) † p
   where
    † : Σ c ꞉ ⟨ 𝓓 ⟩ , (is-compactₚ c ∧ c ∈ₚ U ∧ principal-filter 𝓓 c x) holds
      → x ∈ₚ U holds
    † (c , _ , q , r) = υ c x q r

 characterization-of-scott-opens
  : (U : 𝓟 {𝓥} ⟨ 𝓓 ⟩)
  → (is-scott-open U ⇒ (Ɐ x ꞉ ⟨ 𝓓 ⟩ , U x ⇔ join-of-compact-opens U x)) holds
 characterization-of-scott-opens U ς x = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇒⦆ = characterization-of-scott-opens₁ U ς x
   ⦅⇐⦆ = characterization-of-scott-opens₂ U ς x

 resize-join-of-compact-opens : (U : 𝓟 {𝓥} ⟨ 𝓓 ⟩) (x : ⟨ 𝓓 ⟩)
                              → is-scott-open U holds
                              → (join-of-compact-opens U x holds) is 𝓥 small
 resize-join-of-compact-opens U x ς = x ∈ U , ε
  where
   ε : (x ∈ U) ≃ join-of-compact-opens U x holds
   ε = logically-equivalent-props-are-equivalent
        (holds-is-prop (U x))
        ∃-is-prop
        (characterization-of-scott-opens₁ U ς x)
        (characterization-of-scott-opens₂ U ς x)

\end{code}

Addition 2023-11-22.

The principal filter on the bottom element is the top open of the Scott locale.
We write this down in a different submodule as it requires the additional
assumption of a bottom element in the algebraic dcpo in consideration.

\begin{code}

module BottomLemma (𝓓  : DCPO {𝓤} {𝓥})
                   (𝕒  : structurally-algebraic 𝓓)
                   (hl : has-least (underlying-order 𝓓)) where

 ⊥ᴰ : ⟨ 𝓓 ⟩
 ⊥ᴰ = pr₁ hl

 ⊥ᴰ-is-least : is-least (underlying-order 𝓓) ⊥ᴰ
 ⊥ᴰ-is-least = pr₂ hl

 open Properties 𝓓

 open DefnOfScottTopology 𝓓 𝓥
 open PropertiesAlgebraic 𝓓 𝕒

 bottom-principal-filter-is-top : (𝔘 : 𝒪ₛ) → 𝔘 .pr₁ ⊆ ↑[ 𝓓 ] ⊥ᴰ
 bottom-principal-filter-is-top 𝔘 x _ = ⊥ᴰ-is-least x

\end{code}

Added on 2024-03-09.

If a Scott open contains `⊥` then it contains everything by upward closure.

\begin{code}

 contains-bottom-implies-is-top : (𝔘 : 𝒪ₛ) → (⊥ᴰ ∈ₛ 𝔘) holds
                                → (x : ⟨ 𝓓 ⟩) → (x ∈ₛ 𝔘) holds
 contains-bottom-implies-is-top 𝔘 μ x = upward-closure 𝔘 ⊥ᴰ x μ (⊥ᴰ-is-least x)

\end{code}
