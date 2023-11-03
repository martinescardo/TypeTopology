---
title:      Properties of the Scott topology
author:     Ayberk Tosun
start-date: 2023-10-30
---

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

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
open Conjunction

open PowersetOperations

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

 compact-implies-principal-filter-is-scott-open : (c : ⟨ 𝓓 ⟩)
                                                → is-compact 𝓓 c
                                                → is-scott-open (↑[ 𝓓 ] c) holds
 compact-implies-principal-filter-is-scott-open c κ = Ⅰ , Ⅱ
  where
   Ⅰ : is-upwards-closed (↑[ 𝓓 ] c) holds
   Ⅰ y x p q = c ⊑⟨ 𝓓 ⟩[ p ] y ⊑⟨ 𝓓 ⟩[ q ] x ∎⟨ 𝓓 ⟩

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
  (x : ⟨ 𝓓 ⟩) → is-scott-open (↑[ 𝓓 ] x) holds ⇔ is-compact 𝓓 x
 principal-filter-scott-open-iff-compact x = Ⅰ , Ⅱ
  where
   Ⅰ = principal-filter-scott-open-implies-compact x
   Ⅱ = compact-implies-principal-filter-is-scott-open x

\end{code}

\begin{code}

module PropertiesAlgebraic (𝓓 : DCPO {𝓤} {𝓥})
                           (𝕒 : structurally-algebraic 𝓓) where

 open DefnOfScottTopology 𝓓 𝓥

 open structurally-algebraic

 is-compactₚ : ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓥 ⁺)
 is-compactₚ x = is-compact 𝓓 x , being-compact-is-prop 𝓓 x

 join-of-compact-opens : 𝓟 {𝓥} ⟨ 𝓓 ⟩ → 𝓟 ⟨ 𝓓 ⟩
 join-of-compact-opens U x =
  Ǝ c ꞉ ⟨ 𝓓 ⟩ , (is-compactₚ c ∧ c ∈ₚ U ∧ x ∈ₚ (↑[ 𝓓 ] c)) holds

 characterization-of-scott-open₁ : (U : 𝓟 ⟨ 𝓓 ⟩)
                                 → is-scott-open U holds
                                 → U ⊆ join-of-compact-opens U
 characterization-of-scott-open₁ U (υ , ξ) x p = †
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

\end{code}
