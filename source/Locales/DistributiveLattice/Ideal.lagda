---
title:       Ideals of distributive lattices
author:      Ayberk Tosun
start-date:  2024-02-14
---

\begin{code}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DistributiveLattice.Ideal
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.DistributiveLattice.Definition pt fe
open import Locales.Frame pt fe
open import UF.Powerset-MultiUniverse
open import MLTT.Spartan
open import UF.Base
open import UF.SubtypeClassifier
open import UF.Logic

open Implication fe
open Universal fe

\end{code}

The type of ideals of a distributive lattice.

\begin{code}

is-downward-closed : (L : DistributiveLatticeᵣ 𝓤 𝓥) → 𝓟 {𝓥} ∣ L ∣ᵈ → Ω (𝓤 ⊔ 𝓥)
is-downward-closed L I =
 Ɐ x ꞉ ∣ P ∣ₚ , Ɐ y ꞉ ∣ P ∣ₚ , x ≤[ P ] y ⇒ y ∈ₚ I ⇒ x ∈ₚ I
  where
   open DistributiveLatticeᵣ L

is-closed-under-binary-joins : (L : DistributiveLatticeᵣ 𝓤 𝓥)
                             → 𝓟 {𝓥} ∣ L ∣ᵈ → Ω (𝓤 ⊔ 𝓥)
is-closed-under-binary-joins L I =
 Ɐ x ꞉ ∣ L ∣ᵈ , Ɐ y ꞉ ∣ L ∣ᵈ , x ∈ₚ I ⇒ y ∈ₚ I ⇒ (x ∨ y) ∈ₚ I
  where
   open DistributiveLatticeᵣ L

record Ideal (L : DistributiveLatticeᵣ 𝓤 𝓥) : 𝓤 ⁺ ⊔ 𝓥 ⁺  ̇ where
 open DistributiveLatticeᵣ L

 field
  I : 𝓟 {𝓥} ∣ P ∣ₚ
  I-is-downward-closed : is-downward-closed L I holds
  I-is-closed-under-∨  : is-closed-under-binary-joins L I holds

\end{code}

The principal ideal.

\begin{code}

module PrincipalIdeals (L : DistributiveLatticeᵣ 𝓤 𝓥) where

 open DistributiveLatticeᵣ L

 down-closure : ∣ L ∣ᵈ → 𝓟 {𝓥} ∣ L ∣ᵈ
 down-closure x = λ y → y ≤[ P ] x

 principal-ideal : ∣ L ∣ᵈ → Ideal L
 principal-ideal x =
  let
    open PosetReasoning P

    † : is-downward-closed L (down-closure x) holds
    † y z p q = y ≤⟨ p ⟩ z ≤⟨ q ⟩ x ■

    ‡ : is-closed-under-binary-joins L (down-closure x) holds
    ‡ _ _ = curry ∨-least
  in
   record { I                    = down-closure x
          ; I-is-downward-closed = †
          ; I-is-closed-under-∨  = ‡
          }

\end{code}
