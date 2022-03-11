\section{Preamble}

\begin{code}

{-# OPTIONS --without-K --safe #-}

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

is-heyting-implication-of : (L : frame 𝓤 𝓥 𝓦) → ⟨ L ⟩ → ⟨ L ⟩ × ⟨ L ⟩ →  Ω (𝓤 ⊔ 𝓥)
is-heyting-implication-of L z (x , y) =
 Ɐ w ∶ ⟨ L ⟩ , ((w ∧[ L ] x) ≤[ poset-of L ] y) ↔ (w ≤[ poset-of L ] z)

is-heyting-implication-operation : (L : frame 𝓤 𝓥 𝓦)
                                 → (⟨ L ⟩ → ⟨ L ⟩ → ⟨ L ⟩)
                                 → Ω (𝓤 ⊔ 𝓥)
is-heyting-implication-operation L _==>_ =
 Ɐ x ∶ ⟨ L ⟩ , Ɐ y ∶ ⟨ L ⟩ , is-heyting-implication-of L (x ==> y) (x , y)

modus-ponens : (L : frame 𝓤 𝓥 𝓦) {x y z : ⟨ L ⟩}
             → is-heyting-implication-of L z (x , y) holds
             → ((z ∧[ L ] x) ≤[ poset-of L ] y) holds
modus-ponens L {x} {y} {z} p = pr₂ (p z) (≤-is-reflexive (poset-of L) z)
 where
  open PosetReasoning (poset-of L)

module HeytingImplicationConstruction (L : frame 𝓤  𝓥  𝓥)
                                      (𝒷 : has-basis L holds) where

\end{code}

\begin{code}

 Lₚ = poset-of L

 open GaloisConnectionBetween
 open AdjointFunctorTheorem L 𝒷 L

 ∧-right-preserves-joins : (x : ⟨ L ⟩)
                         → (is-join-preserving L L (meet-of L x)) holds
 ∧-right-preserves-joins = distributivity L

 meet-right-is-monotonic : (x : ⟨ L ⟩) → is-monotonic Lₚ Lₚ (meet-of L x) holds
 meet-right-is-monotonic x = scott-continuous-implies-monotone L L (meet-of L x) ν
  where
   ν : is-scott-continuous L L (meet-of L x) holds
   ν = join-preserving-implies-scott-continuous L L (meet-of L x) (∧-right-preserves-joins x)

 meet-rightₘ : ⟨ L ⟩ → Lₚ ─m→ Lₚ
 meet-rightₘ x = (λ y → x ∧[ L ] y) , meet-right-is-monotonic x

 _==>_ : ⟨ L ⟩ → ⟨ L ⟩ → ⟨ L ⟩
 _==>_ x = pr₁ (pr₁ (aft-backward (meet-rightₘ x) (∧-right-preserves-joins x)))

 ==>-is-heyting-implication : is-heyting-implication-operation L _==>_ holds
 ==>-is-heyting-implication x y w = β , γ
  where
   open PosetReasoning (poset-of L)

   ψ = aft-backward (meet-rightₘ x) (∧-right-preserves-joins x)

   β : ((w ∧[ L ] x) ≤[ poset-of L ] y ⇒ w ≤[ poset-of L ] (x ==> y)) holds
   β p = pr₁ (pr₂ ψ w y) (x ∧[ L ] w   ≡⟨ ∧[ L ]-is-commutative x w ⟩ₚ
                          w ∧[ L ] x   ≤⟨ p ⟩
                          y            ■)

   † : ((x ∧[ L ] (x ==> y)) ≤[ poset-of L ] y) holds
   † = pr₂ (pr₂ ψ (x ==> y) y) (≤-is-reflexive (poset-of L) (x ==> y))

   γ : (w ≤[ poset-of L ] (x ==> y) ⇒ (w ∧[ L ] x) ≤[ poset-of L ] y) holds
   γ p = w ∧[ L ] x            ≤⟨ ∧[ L ]-left-monotone p            ⟩
         (x ==> y) ∧[ L ] x    ≡⟨ ∧[ L ]-is-commutative (x ==> y) x ⟩ₚ
         x ∧[ L ] (x ==> y)    ≤⟨ †                                 ⟩
         y                     ■

\end{code}
