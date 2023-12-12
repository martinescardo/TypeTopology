Tom de Jong 22nd May 2019

The lifting of a set is a set.
We need to assume propositional extensionality for the fixed universe 𝓣 of
propositions and two instances of function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.Set
  (𝓣 : Universe) -- fix a universe for the propositions
  where

open import Lifting.Lifting 𝓣
open import UF.Base
open import UF.FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

lifting-of-set-is-set : funext 𝓣 𝓤
                      → funext 𝓣 𝓣
                      → propext 𝓣
                      → (X : 𝓤 ̇ )
                      → is-set X
                      → is-set (𝓛 X)
lifting-of-set-is-set fe' fe pe  X i {l} {m} p q  = retract-of-prop r j p q
 where
  r : Σ has-section
  r = (to-Σ-＝ , from-Σ-＝ , tofrom-Σ-＝)

  j : is-prop (Σ (λ p₁ → transport (λ P → (P → X) × is-prop P)
               p₁ (pr₂ l) ＝ pr₂ m))
  j = Σ-is-prop
       (identifications-with-props-are-props pe fe (is-defined m)
        (being-defined-is-prop m) (is-defined l))
       (λ d → ×-is-set (Π-is-set fe' λ _ → i)
                       (props-are-sets (being-prop-is-prop fe)))

\end{code}
