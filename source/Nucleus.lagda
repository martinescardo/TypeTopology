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

is-inflationary : (L : frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-inflationary L j = Ɐ x ∶ ⟨ L ⟩ , x ≤[ poset-of L ] j x

is-idempotent : (L : frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-idempotent L j = Ɐ x ∶ ⟨ L ⟩ , j (j x) ≤[ poset-of L ] j x

preserves-meets : (L : frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω 𝓤
preserves-meets L j =
 Ɐ x ∶ ⟨ L ⟩ , Ɐ y ∶ ⟨ L ⟩ , (j (x ∧[ L ] y) ≡[ ψ ]≡ j x ∧[ L ] j y)
  where
   ψ : is-set ⟨ L ⟩
   ψ = carrier-of-[ poset-of L ]-is-set

is-nuclear : (L : frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-nuclear {𝓤 = 𝓤} {𝓥} {𝓦} F j = 𝓃₁ ∧  𝓃₂ ∧ 𝓃₃
 where
  open PosetNotation (poset-of F)

  𝓃₁ : Ω (𝓤 ⊔ 𝓥)
  𝓃₁ = is-inflationary F j

  𝓃₂ : Ω (𝓤 ⊔ 𝓥)
  𝓃₂ = is-idempotent F j

  𝓃₃ : Ω 𝓤
  𝓃₃ = preserves-meets F j

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
