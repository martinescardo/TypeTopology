Tom de Jong, 31 May 2019

The denotational semantics of PCF based on pointed directed complete posets.

The flag --experimental-lossy-unification significantly speeds up the
typechecking of the line ⟦ S {ρ} {σ} {τ} ⟧ₑ = Sᵈᶜᵖᵒ⊥ ⟦ ρ ⟧ ⟦ σ ⟧ ⟦ τ ⟧ below.
(https://agda.readthedocs.io/en/latest/language/lossy-unification.html)


We consider the combinatory version of PCF here. This development was extended
to PCF with variables and λ-abstraction by Brendan Hart in a final year project
supervised by Martín Escardó and myself. Notably, Brendan's extension contains
an Agda formalization of soundness and computational adequacy.

Brendan's code, using a previous version of our library, can be found
here: https://github.com/BrendanHart/Investigating-Properties-of-PCF.

The repository also contains Brendan's report describing the project:
https://github.com/BrendanHart/Investigating-Properties-of-PCF/blob/master/InvestigatingPropertiesOfPCFInAgda.pdf.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module DomainTheory.ScottModelOfPCF.ScottModelOfPCF
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import MLTT.NaturalNumbers-Properties
open import UF.Miscelanea

open import PCF pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.LeastFixedPoint pt fe
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀

open import DomainTheory.ScottModelOfPCF.PCFCombinators pt fe 𝓤₀
open IfZeroDenotationalSemantics pe

open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe

open import Lifting.Lifting 𝓤₀
open import Lifting.Monad 𝓤₀ hiding (μ)

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
