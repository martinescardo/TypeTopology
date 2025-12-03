Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.Construction (𝓣 : Universe) where

open import UF.Subsingletons
open import UF.SubtypeClassifier hiding (⊥)

𝓛 : 𝓤 ̇ → 𝓣 ⁺ ⊔  𝓤 ̇
𝓛 X = Σ P ꞉ 𝓣 ̇ , (P → X) × is-prop P

is-defined : {X : 𝓤 ̇ } → 𝓛 X → 𝓣 ̇
is-defined (P , φ , i) = P

is-def : {X : 𝓤 ̇ } → 𝓛 X → Ω 𝓣
is-def (P , φ , i) = (P , i)

being-defined-is-prop : {X : 𝓤 ̇ } (l : 𝓛  X) → is-prop (is-defined l)
being-defined-is-prop (P , φ , i) = i

value : {X : 𝓤 ̇ } (l : 𝓛  X) → is-defined l → X
value (P , φ , i) = φ

\end{code}

The "total" elements of 𝓛 X:

\begin{code}

η : {X : 𝓤 ̇ } → X → 𝓛 X
η x = 𝟙 , (λ _ → x) , 𝟙-is-prop

\end{code}

Its "undefined" element:

\begin{code}

⊥ : {X : 𝓤 ̇ } → 𝓛 X
⊥ = 𝟘 , unique-from-𝟘 , 𝟘-is-prop

\end{code}

Added 7th November 2025. I don't know why we didn't work with the
following more natural definition.

\begin{code}

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier-Properties

𝓛' : 𝓤 ̇ → 𝓣 ⁺ ⊔  𝓤 ̇
𝓛' X = Σ p ꞉ Ω 𝓣 , (p holds → X)

𝓛-is-equiv-to-𝓛' : {X : 𝓤 ̇ } → 𝓛 X ≃ 𝓛' X
𝓛-is-equiv-to-𝓛' {𝓤} {X} =
 (Σ P ꞉ 𝓣 ̇ , (P → X) × is-prop P) ≃⟨ Σ-cong (λ P → ×-comm)  ⟩
 (Σ P ꞉ 𝓣 ̇ , is-prop P × (P → X)) ≃⟨ ≃-sym Σ-assoc ⟩
 (Σ p ꞉ Ω 𝓣 , (p holds → X))     ■

\end{code}

With this representation, it is easy to prove that 𝓛 X is a set if X is.

\begin{code}

open import UF.FunExt

𝓛-is-set : funext 𝓣 𝓣
         → funext 𝓣 𝓤
         → propext 𝓣
         → {X : 𝓤 ̇ } → is-set X → is-set (𝓛 X)
𝓛-is-set fe fe' pe X-is-set = equiv-to-set
                                𝓛-is-equiv-to-𝓛'
                                (Σ-is-set
                                  (Ω-is-set fe pe)
                                  (λ p → Π-is-set fe' λ _ → X-is-set))

\end{code}
