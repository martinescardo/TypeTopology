Tom de Jong, 31 May 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module ScottModelOfPCF (pt : propositional-truncations-exist)
                       (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
                       (pe : ∀ {𝓤} → propext 𝓤)
       where

open PropositionalTruncation pt

open import UF-Miscelanea
open import NaturalNumbers-Properties

open import PCF pt
open import Dcpos pt fe 𝓤₀
open import DcpoLeastFixedPoint pt fe
open import DcpoFunctionSpace pt fe 𝓤₀
open import LiftingDcpo' 𝓤₀ fe pe pt
open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)

⟦_⟧ : type → DCPO⊥ {𝓤₁} {𝓤₁}
⟦ ι ⟧     = 𝓛ᵈℕ
⟦ σ ⇒ τ ⟧ = DCPO⊥[ ⟦ σ ⟧ , ⟦ τ ⟧ ]


\end{code}
