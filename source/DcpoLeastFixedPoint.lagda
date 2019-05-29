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

 μ-gives-a-fixed-point : (f : ⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩)
                       → pr₁ μ f ≡ (pr₁ f (pr₁ μ f)) -- use underlying-function?
 μ-gives-a-fixed-point f = antisymmetry ⟪ 𝓓 ⟫ (pr₁ μ f) (pr₁ f (pr₁ μ f)) l m where
  δ : is-directed (underlying-order ⟪ 𝓓 ⟫)
   (pointwise-family ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) f)
  δ = pointwise-family-is-directed ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) iter-is-directed f
  
  l : pr₁ μ f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ pr₁ f (pr₁ μ f)
  l = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ δ (pr₁ f (pr₁ μ f)) h where
   h : (n : ℕ) → iter 𝓓 n f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ pr₁ f (pr₁ μ f)
   h zero     = least-property 𝓓 (pr₁ f (pr₁ μ f))
   h (succ n) = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f
                (iter 𝓓 n f)
                (pr₁ μ f)
                (∐-is-upperbound ⟪ 𝓓 ⟫ δ n)
                
  m : pr₁ f (pr₁ μ f) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ pr₁ μ f
  m = is-sup-is-lowerbound-of-upperbounds (underlying-order ⟪ 𝓓 ⟫)
      (continuity-of-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f ℕ α δ) (pr₁ μ f) k where
   α : ℕ → ⟨ ⟪ 𝓓 ⟫ ⟩
   α = pointwise-family ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) f
   k : (n : ℕ) → underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (α n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ pr₁ μ f
   k n = transitivity ⟪ 𝓓 ⟫
         (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (α n)) (α (succ n)) (pr₁ μ f)
         p q where
    p : underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (α n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ α (succ n)
    p = reflexivity ⟪ 𝓓 ⟫ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (α n))
    q : α (succ n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ pr₁ μ f
    q = ∐-is-upperbound ⟪ 𝓓 ⟫ δ (succ n)

 μ-gives-lowerbound-of-fixed-points : (f : ⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩)
                                    → (d : ⟨ ⟪ 𝓓 ⟫ ⟩)
                                    → underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f d ⊑⟨ ⟪ 𝓓 ⟫ ⟩ d
                                    → (underlying-function ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ μ) f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ d
 μ-gives-lowerbound-of-fixed-points f d l =
  ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫
   (pointwise-family-is-directed ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) iter-is-directed f)
   d g where
   g : (n : ℕ) → iter 𝓓 n f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ d
   g zero     = least-property 𝓓 d
   g (succ n) = transitivity ⟪ 𝓓 ⟫
                (iter 𝓓 (succ n) f) (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f d) d
                (continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (iter 𝓓 n f) d (g n))
                l


\end{code}
