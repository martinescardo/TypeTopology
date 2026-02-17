Tom de Jong & Martín Escardó, 8 & 10 September 2023.
Moved to its own file on 29 October 2025.

The type of non-empty types is injective. This should be contrasted with the
fact that the type of inhabited types is not necessarily injective, see
InjectiveTypes.InhabitedTypesTaboo.

An alternative proof of the injectivity of the type of non-empty types
may be found in InjectiveTypes.MathematicalStrutures.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.NonEmptyTypes
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

 pe' : Prop-Ext
 pe' {𝓤} = pe 𝓤

open import InjectiveTypes.Blackboard fe

Non-Empty : 𝓤 ⁺ ̇
Non-Empty = Σ X ꞉ 𝓤 ̇ , is-nonempty X

Non-Empty-retract : retract Non-Empty of (𝓤 ̇ )
Non-Empty-retract = ρ , σ , ρσ
 where
  ρ : 𝓤 ̇ → Non-Empty
  ρ X = (¬¬ X → X) , double-negation-elimination-inside-double-negation X
  σ : Non-Empty → 𝓤 ̇
  σ = pr₁
  ρσ : ρ ∘ σ ∼ id
  ρσ (X , X-non-empty) = to-subtype-＝ (λ Y → negations-are-props fe')
                                       (eqtoid (ua 𝓤) (¬¬ X → X) X e)
   where
    e = (¬¬ X → X) ≃⟨ I ⟩
        (𝟙{𝓤} → X) ≃⟨ ≃-sym (𝟙→ fe') ⟩
        X          ■
     where
      I = →cong'' fe' fe' (idtoeq (¬¬ X) 𝟙 II)
       where
        II : ¬¬ X ＝ 𝟙
        II = holds-gives-equal-𝟙 pe' (¬¬ X) (negations-are-props fe') X-non-empty

Non-Empty-is-injective : ainjective-type Non-Empty 𝓤 𝓤
Non-Empty-is-injective =
 retract-of-ainjective Non-Empty (𝓤 ̇ )
                       (universes-are-ainjective (ua 𝓤))
                       Non-Empty-retract

\end{code}
