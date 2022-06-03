\section{Preamble}

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline #-}

open import Universes
open import SpartanMLTT
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import Sigma

module HeytingImplication
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         where

open import Frame pt fe
open import GaloisConnection pt fe
open import UF-Subsingletons

open import UF-Subsingleton-Combinators

open AllCombinators pt fe
open PropositionalTruncation pt

open import AdjointFunctorTheoremForFrames pt fe

open Locale

is-heyting-implication-of : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ × ⟨ 𝒪 X ⟩ →  Ω (𝓤 ⊔ 𝓥)
is-heyting-implication-of X z (x , y) =
 Ɐ w ∶ ⟨ 𝒪 X ⟩ , ((w ∧[ 𝒪 X ] x) ≤[ poset-of (𝒪 X) ] y) ↔ (w ≤[ poset-of (𝒪 X) ] z)

is-heyting-implication-operation : (X : Locale 𝓤 𝓥 𝓦)
                                 → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
                                 → Ω (𝓤 ⊔ 𝓥)
is-heyting-implication-operation X _==>_ =
 Ɐ x ∶ ⟨ 𝒪 X ⟩ , Ɐ y ∶ ⟨ 𝒪 X ⟩ , is-heyting-implication-of X (x ==> y) (x , y)

modus-ponens : (X : Locale 𝓤 𝓥 𝓦) {U V W : ⟨ 𝒪 X ⟩}
             → is-heyting-implication-of X W (U , V) holds
             → ((W ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] V) holds
modus-ponens X {x} {y} {z} p = pr₂ (p z) (≤-is-reflexive (poset-of (𝒪 X)) z)
 where
  open PosetReasoning (poset-of (𝒪 X))

module HeytingImplicationConstruction (X : Locale 𝓤  𝓥  𝓥)
                                      (𝒷 : has-basis (𝒪 X) holds) where

\end{code}

\begin{code}

 L  = 𝒪 X
 Lₚ = poset-of (𝒪 X)

 open GaloisConnectionBetween
 open AdjointFunctorTheorem X X 𝒷

 ∧-right-preserves-joins : (U : ⟨ 𝒪 X ⟩)
                         → (is-join-preserving (𝒪 X) (𝒪 X) (meet-of (𝒪 X) U)) holds
 ∧-right-preserves-joins = distributivity (𝒪 X)

 meet-right-is-monotonic : (U : ⟨ 𝒪 X ⟩) → is-monotonic Lₚ Lₚ (meet-of (𝒪 X) U) holds
 meet-right-is-monotonic U = scott-continuous-implies-monotone L L (meet-of L U) ν
  where
   ν : is-scott-continuous (𝒪 X) (𝒪 X) (meet-of (𝒪 X) U) holds
   ν = join-preserving-implies-scott-continuous L L (meet-of L U) (∧-right-preserves-joins U)

 meet-rightₘ : ⟨ L ⟩ → Lₚ ─m→ Lₚ
 meet-rightₘ U = (λ V → U ∧[ L ] V) , meet-right-is-monotonic U

 _==>_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 _==>_ U = pr₁ (pr₁ (aft-backward (meet-rightₘ U) (∧-right-preserves-joins U)))

 ==>-is-heyting-implication : is-heyting-implication-operation X _==>_ holds
 ==>-is-heyting-implication U V W = β , γ
  where
   open PosetReasoning (poset-of L)

   ψ = aft-backward (meet-rightₘ U) (∧-right-preserves-joins U)

   β : ((W ∧[ L ] U) ≤[ poset-of L ] V ⇒ W ≤[ poset-of L ] (U ==> V)) holds
   β p = pr₁ (pr₂ ψ W V) (U ∧[ L ] W   ≡⟨ ∧[ L ]-is-commutative U W ⟩ₚ
                          W ∧[ L ] U   ≤⟨ p ⟩
                          V            ■)

   † : ((U ∧[ L ] (U ==> V)) ≤[ poset-of L ] V) holds
   † = pr₂ (pr₂ ψ (U ==> V) V) (≤-is-reflexive (poset-of L) (U ==> V))

   γ : (W ≤[ poset-of L ] (U ==> V) ⇒ (W ∧[ L ] U) ≤[ poset-of L ] V) holds
   γ p = W ∧[ L ] U            ≤⟨ ∧[ L ]-left-monotone p            ⟩
         (U ==> V) ∧[ L ] U    ≡⟨ ∧[ L ]-is-commutative (U ==> V) U ⟩ₚ
         U ∧[ L ] (U ==> V)    ≤⟨ †                                 ⟩
         V                     ■

\end{code}
