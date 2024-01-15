.Tom de Jong, 4 & 5 April 2022.

Assuming set quotients, we derive propositional truncations in the
presence of function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Quotient.GivesPropTrunc where

open import MLTT.Spartan

open import Quotient.Type

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

module _ (sq : set-quotients-exist) where

 open general-set-quotients-exist sq

 private
  module _ {X : 𝓤 ̇ } where
   _≈_ : X → X → 𝓤₀ ̇
   x ≈ y = 𝟙
   ≋ : EqRel X
   ≋ = _≈_ , (λ x y → 𝟙-is-prop) , (λ x → ⋆) , (λ x y _ → ⋆) , (λ x y z _ _ → ⋆)

  ∥_∥ : 𝓤 ̇  → 𝓤 ̇
  ∥_∥ X = X / ≋

  ∣_∣ : {X : 𝓤 ̇ } → X → ∥ X ∥
  ∣_∣ = η/ ≋

  ∥∥-is-prop : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → is-prop ∥ X ∥
  ∥∥-is-prop {𝓤} {X} fe = /-induction ≋ (λ x' → Π-is-prop fe (λ y' → /-is-set ≋))
                           (λ x → /-induction ≋ (λ y' → /-is-set ≋)
                                  (λ y → η/-identifies-related-points ≋ ⋆))

  ∥∥-rec : {X : 𝓤 ̇ } {P : 𝓥 ̇ } → is-prop P → (X → P) → ∥ X ∥ → P
  ∥∥-rec {𝓤} {𝓥} {X} {P} i f =
   ∃!-witness (/-universality ≋ (props-are-sets i) f
                              (λ {x} {x'}_ → i (f x) (f x')))

 abstract
  propositional-truncations-from-set-quotients :
   Fun-Ext → propositional-truncations-exist
  propositional-truncations-from-set-quotients fe = record
   { ∥_∥        = ∥_∥
   ; ∥∥-is-prop = ∥∥-is-prop fe
   ; ∣_∣        = ∣_∣
   ; ∥∥-rec     = ∥∥-rec
   }

\end{code}
