Tom de Jong, 28 May 2019

\begin{code}

open import UF-PropTrunc
open import SpartanMLTT

module DcpoLeastFixedPoint
       (pt : propositional-truncations-exist)
       (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

open PropositionalTruncation pt
--open import UF-Subsingletons
--open import UF-Subsingletons-FunExt
open import Dcpos pt fe 𝓤₀
open import DcpoFunctionSpace pt fe 𝓤₀
open import NaturalsOrder

module _
  (𝓓 : DCPO⊥ {𝓤} {𝓣})
  where
 
 iter-is-directed : is-directed (λ F G → ∀ f → F f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ G f) (iter 𝓓) 
 iter-is-directed = ∣ zero ∣ , δ where
  δ : (i j : ℕ) → ∃ (λ k →
           ((f : Σ (is-continuous ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫)) →
            underlying-order ⟪ 𝓓 ⟫ (iter 𝓓 i f) (iter 𝓓 k f))
           ×
           ((f : Σ (is-continuous ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫)) →
            underlying-order ⟪ 𝓓 ⟫ (iter 𝓓 j f) (iter 𝓓 k f)))
  δ i j = ∣ {!i natplus j!} , {!!} ∣


\end{code}
