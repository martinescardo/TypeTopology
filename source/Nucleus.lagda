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

is-inflationary : (L : Frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-inflationary L j = Ɐ x ∶ ⟨ L ⟩ , x ≤[ poset-of L ] j x

is-idempotent : (L : Frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-idempotent L j = Ɐ x ∶ ⟨ L ⟩ , j (j x) ≤[ poset-of L ] j x

is-nucleus : (L : Frame 𝓤 𝓥 𝓦) → (⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-nucleus {𝓤 = 𝓤} {𝓥} {𝓦} F j = 𝓃₁ ∧  𝓃₂ ∧ 𝓃₃
 where
  open PosetNotation (poset-of F)

  𝓃₁ : Ω (𝓤 ⊔ 𝓥)
  𝓃₁ = is-inflationary F j

  𝓃₂ : Ω (𝓤 ⊔ 𝓥)
  𝓃₂ = is-idempotent F j

  𝓃₃ : Ω 𝓤
  𝓃₃ = preserves-binary-meets F F j

\end{code}

The type of nuclei on a given frame.

\begin{code}

Nucleus : Frame 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ̇
Nucleus F = Σ j ꞉ (⟨ F ⟩ → ⟨ F ⟩) , is-nucleus F j holds

𝓃₁ : (L : Frame 𝓤 𝓥 𝓦) ((j , _) : Nucleus L)
   → (x : ⟨ L ⟩) → (x ≤[ poset-of L ] j x) holds
𝓃₁ F (j , 𝓃₁ , _ , _)= 𝓃₁

𝓃₂ : (L : Frame 𝓤 𝓥 𝓦) ((j , _) : Nucleus L)
   → (U : ⟨ L ⟩) → (j (j U) ≤[ poset-of L ] j U) holds
𝓃₂ F (j , _ , 𝓃₂ , _) = 𝓃₂

𝓃₃ : (L : Frame 𝓤 𝓥 𝓦) ((j , _) : Nucleus L)
   → (U V : ⟨ L ⟩) → j (U ∧[ L ] V) ≡ j U ∧[ L ] j V
𝓃₃ F (j , _ , _ , 𝓃₃) = 𝓃₃

\end{code}

\begin{code}

identity-nucleus : (L : Frame 𝓤 𝓥 𝓦) → Nucleus L
identity-nucleus L = id , n₁ , n₂ , n₃
 where
  n₁ : is-inflationary L id holds
  n₁ = ≤-is-reflexive (poset-of L)

  n₂ : is-idempotent L id holds
  n₂ = ≤-is-reflexive (poset-of L)

  n₃ : preserves-binary-meets L L id holds
  n₃ x y = refl {x = x ∧[ L ] y}

\end{code}

In this development, it will be useful to define and work with the notion of a
prenucleus: a meet-preserving inflationary endomap (that is not necessary
idempotent):

\begin{code}

is-prenucleus : (L : Frame 𝓤 𝓥 𝓦) (j : ⟨ L ⟩ → ⟨ L ⟩) → Ω (𝓤 ⊔ 𝓥)
is-prenucleus L j = is-inflationary L j  ∧ preserves-binary-meets L L j

Prenucleus : Frame 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥) ̇
Prenucleus L = Σ j ꞉ (⟨ L ⟩ → ⟨ L ⟩) , is-prenucleus L j holds

module PrenucleusApplicationSyntax (L : Frame 𝓤 𝓥 𝓦) where

 _$ₚ_ : Prenucleus L → ⟨ L ⟩ → ⟨ L ⟩
 _$ₚ_ = pr₁

 infixr 2 _$ₚ_

\end{code}

Inclusion of nuclei into the type of prenuclei:

\begin{code}

nucleus-pre : (L : Frame 𝓤 𝓥 𝓦) → Nucleus L → Prenucleus L
nucleus-pre L 𝒿@(j , _) = j , 𝓃₁ L 𝒿 , 𝓃₃ L 𝒿

\end{code}

Prenuclei are monotone:

\begin{code}

prenuclei-are-monotone : (L : Frame 𝓤 𝓥 𝓦)
                       → ((j , _) : Prenucleus L)
                       → is-monotonic (poset-of L) (poset-of L) j holds
prenuclei-are-monotone L (j , _ , μ) =
 meet-preserving-implies-monotone L L j μ

\end{code}

As a corollary, nuclei are monotone:

\begin{code}

nuclei-are-monotone : (L : Frame 𝓤 𝓥 𝓦) ((j , _) : Nucleus L)
                    → is-monotonic (poset-of L) (poset-of L) j holds
nuclei-are-monotone L 𝒿 = prenuclei-are-monotone L (nucleus-pre L 𝒿)

\end{code}

\begin{code}

prenucleus-property₁ : (L : Frame 𝓤 𝓥 𝓦)
                     → ((j , _) (k , _) : Prenucleus L)
                     → (Ɐ x ∶ ⟨ L ⟩ , j x ≤[ poset-of L ] (j ∘ k) x) holds
prenucleus-property₁ L (j , _ , μj) (k , ζ , _) x =
 meet-preserving-implies-monotone L L j μj (x , k x) (ζ x)

prenucleus-property₂ : (L : Frame 𝓤 𝓥 𝓦)
                     → ((j , _) (k , _) : Prenucleus L)
                     → (Ɐ x ∶ ⟨ L ⟩ , k x ≤[ poset-of L ] (j ∘ k) x) holds
prenucleus-property₂ L (j , ζj , _) (k , _) x = ζj (k x)

\end{code}
