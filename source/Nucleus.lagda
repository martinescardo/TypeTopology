Ayberk Tosun, 15 October 2021

Based on `ayberkt/formal-topology-in-UF`.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-PropTrunc

module Nucleus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Subsingletons-FunExt

open import Frame pt fe

open AllCombinators pt fe

\end{code}

\begin{code}

is-nuclear : (L : frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-nuclear {𝓤 = 𝓤} {𝓥} {𝓦} F j = 𝓃₁ ∧  𝓃₂ ∧ 𝓃₃
 where
  open PosetNotation (poset-of F)

  ψ : is-set ⟨ F ⟩
  ψ = carrier-of-[ poset-of F ]-is-set

  𝓃₁ : Ω (𝓤 ⊔ 𝓥)
  𝓃₁ = Ɐ x ∶ ⟨ F ⟩ , x ≤[ poset-of F ] j x

  𝓃₂ : Ω (𝓤 ⊔ 𝓥)
  𝓃₂ = Ɐ x ∶ ⟨ F ⟩ , j (j x) ≤[ poset-of F ] j x

  𝓃₃ : Ω 𝓤
  𝓃₃ = Ɐ x ∶ ⟨ F ⟩ , Ɐ y ∶ ⟨ F ⟩ ,
        (j (x ∧[ F ] y) ≡[ ψ ]≡ j x ∧[ F ] j y)

\end{code}

The type of nuclei on a given frame.

\begin{code}

nucleus : frame 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ̇ 
nucleus F = Σ j ꞉ (⟨ F ⟩ → ⟨ F ⟩) , is-nuclear F j holds

𝓃₁ : (L : frame 𝓤 𝓥 𝓦) ((j , _) : nucleus L)
   → (x : ⟨ L ⟩) → (x ≤[ poset-of L ] j x) holds
𝓃₁ F (j , 𝓃₁ , _ , _)= 𝓃₁

𝓃₂ : (L : frame 𝓤 𝓥 𝓦) ((j , _) : nucleus L)
   → (U : ⟨ L ⟩) → (j (j U) ≤[ poset-of L ] j U) holds
𝓃₂ F (j , _ , 𝓃₂ , _) = 𝓃₂

𝓃₃ : (L : frame 𝓤 𝓥 𝓦) ((j , _) : nucleus L)
   → (U V : ⟨ L ⟩) → j (U ∧[ L ] V) ≡ j U ∧[ L ] j V
𝓃₃ F (j , _ , _ , 𝓃₃) = 𝓃₃

\end{code}
