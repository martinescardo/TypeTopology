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
open import NaturalsAddition renaming (_+_ to _+'_)

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
  δ i j = ∣ i +' j , l , m ∣ where
   l : (f : [ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]) → iter 𝓓 i f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter 𝓓 (i +' j) f
   l = iter-increases 𝓓 i (i +' j)
         (cosubtraction i (i +' j) (j , (addition-commutativity j i)))
   m : (f : [ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]) → iter 𝓓 j f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter 𝓓 (i +' j) f
   m = iter-increases 𝓓 j (i +' j) (cosubtraction j (i +' j) (i , refl))

 μ : [ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ , ⟪ 𝓓 ⟫ ]
 μ = continuous-functions-sup ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) iter-is-directed


\end{code}
