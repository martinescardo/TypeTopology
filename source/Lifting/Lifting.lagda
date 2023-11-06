Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting). Constructions and
properties of lifting are discussed in other modules.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.Lifting (𝓣 : Universe) where

open import UF.Subsingletons

𝓛 : 𝓤 ̇ → 𝓣 ⁺ ⊔  𝓤 ̇
𝓛 X = Σ P ꞉ 𝓣 ̇ , (P → X) × is-prop P

is-defined : {X : 𝓤 ̇ } → 𝓛 X → 𝓣 ̇

is-defined (P , φ , i) = P

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
