Brendan Hart 2019-2020

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module PCF.Lambda.ScottModelOfIfZero
       (pt : propositional-truncations-exist)
       (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import DomainTheory.Basics.Curry pt fe 𝓤₀
open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.FunctionComposition pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Basics.Products pt fe
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe
open import PCF.Combinatory.PCFCombinators pt fe 𝓤₀
open import PCF.Lambda.AbstractSyntax pt
open import PCF.Lambda.ScottModelOfContexts pt fe pe
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open DcpoProductsGeneral 𝓤₀
open IfZeroDenotationalSemantics pe


⦅ifZero⦆-uncurried' : DCPO⊥[ 𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
⦅ifZero⦆-uncurried' = uncurryᵈᶜᵖᵒ⊥ 𝓛ᵈℕ 𝓛ᵈℕ (𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⦅ifZero⦆

⦅ifZero⦆-uncurried : DCPO⊥[ (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ]
⦅ifZero⦆-uncurried = uncurryᵈᶜᵖᵒ⊥ (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) 𝓛ᵈℕ 𝓛ᵈℕ ⦅ifZero⦆-uncurried'

module _ {n : ℕ} (Γ : Context n) where

  ⦅ifZero⦆-arguments : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
                      → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
                      → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
                      → DCPO⊥[ 【 Γ 】 , (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
  ⦅ifZero⦆-arguments a b c = to-×-DCPO⊥ 【 Γ 】 (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) 𝓛ᵈℕ f c
     where
      f : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
      f = to-×-DCPO⊥ 【 Γ 】 𝓛ᵈℕ 𝓛ᵈℕ a b

  ⦅ifZero⦆Γ : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
              → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
              → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
              → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
  ⦅ifZero⦆Γ a b c = [ 【 Γ 】 , (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ]
                       ⦅ifZero⦆-uncurried ∘ᵈᶜᵖᵒ⊥ (⦅ifZero⦆-arguments a b c)
\end{code}
