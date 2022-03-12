Tom de Jong, 31 May 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-PropTrunc
open import UF-FunExt
open import UF-Subsingletons

module ScottModelOfPCF
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import NaturalNumbers-Properties
open import UF-Miscelanea

open import PCF pt

open import Dcpo pt fe 𝓤₀
open import DcpoExponential pt fe 𝓤₀
open import DcpoMiscelanea pt fe 𝓤₀

open import DcpoPCFCombinators pt fe 𝓤₀
open IfZeroDenotationalSemantics pe

open import DcpoLeastFixedPoint pt fe

open import DcpoLifting pt fe 𝓤₀ pe

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)

⟦_⟧ : type → DCPO⊥ {𝓤₁} {𝓤₁}
⟦ ι ⟧     = 𝓛-DCPO⊥ ℕ-is-set
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ ⟹ᵈᶜᵖᵒ⊥ ⟦ τ ⟧

⟦_⟧ₑ : {σ : type} (t : PCF σ) → ⟪ ⟦ σ ⟧ ⟫
⟦ Zero ⟧ₑ            = η zero
⟦ Succ ⟧ₑ            = 𝓛̇ succ , 𝓛̇-continuous ℕ-is-set ℕ-is-set succ
⟦ Pred ⟧ₑ            = 𝓛̇ pred , 𝓛̇-continuous ℕ-is-set ℕ-is-set pred
⟦ ifZero ⟧ₑ          = ⦅ifZero⦆
⟦ Fix {σ} ⟧ₑ         = μ ⟦ σ ⟧
⟦ K {σ} {τ} ⟧ₑ       = Kᵈᶜᵖᵒ⊥ ⟦ σ ⟧ ⟦ τ ⟧
⟦ S {ρ} {σ} {τ} ⟧ₑ   = Sᵈᶜᵖᵒ⊥ ⟦ ρ ⟧ ⟦ σ ⟧ ⟦ τ ⟧
⟦ _·_ {σ} {τ} s t ⟧ₑ = [ ⟦ σ ⟧ ⁻ ,  ⟦ τ ⟧ ⁻ ]⟨ ⟦ s ⟧ₑ ⟩ ⟦ t ⟧ₑ

\end{code}
