Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Lambda.ScottModelOfTerms
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Curry pt fe 𝓤₀
open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.FunctionComposition pt fe 𝓤₀
open import DomainTheory.Basics.LeastFixedPoint pt fe
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Basics.Products pt fe
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe
open import Lifting.Lifting 𝓤₀
open import Lifting.Monad 𝓤₀ hiding (μ)
open import Naturals.Properties
open import PCF.Lambda.AbstractSyntax pt
open import PCF.Lambda.ScottModelOfContexts pt fe pe
open import PCF.Lambda.ScottModelOfIfZero pt fe pe
open import PCF.Lambda.ScottModelOfTypes pt fe pe
open import UF.DiscreteAndSeparated

open DcpoProductsGeneral 𝓤₀

⟦_⟧ₑ : {n : ℕ} {Γ : Context n} {σ : type} (t : PCF Γ σ)
     → DCPO⊥[ 【 Γ 】 , ⟦ σ ⟧ ]

⟦ Zero {_} {Γ} ⟧ₑ =
 (λ _ → η zero) , constant-functions-are-continuous (【 Γ 】 ⁻) (⟦ ι ⟧ ⁻)

⟦ Succ {_} {Γ} t ⟧ₑ =
 [ 【 Γ 】 , ⟦ ι ⟧ , ⟦ ι ⟧ ]
 (𝓛̇ succ , 𝓛̇-continuous ℕ-is-set ℕ-is-set succ) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ

⟦ Pred {_} {Γ} t ⟧ₑ =
 [ 【 Γ 】 , ⟦ ι ⟧ , ⟦ ι ⟧ ]
 (𝓛̇ pred , 𝓛̇-continuous ℕ-is-set ℕ-is-set pred) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ

⟦ IfZero {_} {Γ} t t₁ t₂ ⟧ₑ =
 ⦅ifZero⦆Γ Γ ⟦ t₁ ⟧ₑ ⟦ t₂ ⟧ₑ ⟦ t ⟧ₑ

⟦ ƛ {_} {Γ} {σ} {τ} t ⟧ₑ =
 curryᵈᶜᵖᵒ⊥ 【 Γ 】 ⟦ σ ⟧ ⟦ τ ⟧ ⟦ t ⟧ₑ

⟦ _·_ {_} {Γ} {σ} {τ} t t₁ ⟧ₑ =
 [ 【 Γ 】 , ( ⟦ σ ⇒ τ ⟧ ×ᵈᶜᵖᵒ⊥ ⟦ σ ⟧) , ⟦ τ ⟧ ]
 (eval⊥ ⟦ σ ⟧ ⟦ τ ⟧) ∘ᵈᶜᵖᵒ⊥ (to-×-DCPO⊥ 【 Γ 】 ⟦ σ ⇒ τ ⟧ ⟦ σ ⟧ ⟦ t ⟧ₑ ⟦ t₁ ⟧ₑ)

⟦ v {_} {Γ} x ⟧ₑ =
 var-DCPO⊥ Γ x

⟦ Fix {_} {Γ} {σ} t ⟧ₑ =
 [ 【 Γ 】 , ⟦ σ ⇒ σ ⟧ , ⟦ σ ⟧ ] (μ ⟦ σ ⟧) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ

\end{code}
