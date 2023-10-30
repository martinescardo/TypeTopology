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

open import UF.Powerset-MultiUniverse
open import Slice.Family

open PropositionalTruncation pt

open import DomainTheory.Topology.ScottTopology pt fe 𝓥
open import DomainTheory.Basics.Dcpo            pt fe 𝓥
open import DomainTheory.Basics.WayBelow        pt fe 𝓥


\end{code}

\begin{code}

principal-filter : (𝓓 : DCPO {𝓤} {𝓥}) → ⟨ 𝓓 ⟩ → 𝓟 ⟨ 𝓓 ⟩
principal-filter 𝓓 c x = c ⊑⟨ 𝓓 ⟩ x , prop-valuedness 𝓓 c x

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
