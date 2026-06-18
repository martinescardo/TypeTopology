Tom de Jong, 9 March 2020
Refactored 9 February 2022.

Taking the rounded ideal completion of the dyadics (𝔻,≺) we obtain an example of
a continuous dcpo without any compact elements. Hence, it cannot be algebraic.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Examples.IdlDyadics
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import DyadicsInductive.Dyadics
open import DyadicsInductive.DyadicOrder
open import DyadicsInductive.DyadicOrder-PropTrunc pt

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.WayBelow pt fe 𝓤₀

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤₀
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤₀

open import DomainTheory.IdealCompletion.Properties pt fe pe 𝓤₀

open Ideals-of-small-abstract-basis
      (record
         { basis-carrier = 𝔻
         ; _≺_ = _≺_
         ; ≺-prop-valued = λ {x} {y} → ≺-is-prop-valued x y
         ; ≺-trans = λ {x} {y} {z} → ≺-is-transitive x y z
         ; INT₀ = ≺-has-no-left-endpoint
         ; INT₂ = λ {x} {y} {z} → ≺-interpolation₂ x y z
        })

Idl-𝔻 : DCPO {𝓤₁} {𝓤₀}
Idl-𝔻 = Idl-DCPO

Idl-𝔻-is-continuous : is-continuous-dcpo Idl-𝔻
Idl-𝔻-is-continuous = Idl-is-continuous-dcpo

Idl-𝔻-has-small-basis : has-specified-small-basis Idl-𝔻
Idl-𝔻-has-small-basis = 𝔻 , ↓_ , ↓-is-small-basis

Idl-𝔻-has-no-compact-elements : (I : Idl) → ¬ (is-compact Idl-𝔻 I)
Idl-𝔻-has-no-compact-elements I κ = ∥∥-rec 𝟘-is-prop γ g
 where
  γ : ¬ (Σ x ꞉ 𝔻 , x ∈ᵢ I × I ⊑ (↓ x))
  γ (x , xI , s) = ≺-to-≠ {x} {x} r refl
   where
    r : x ≺ x
    r = s x xI
  g : ∃ x ꞉ 𝔻 , x ∈ᵢ I × I ⊑ (↓ x)
  g = Idl-≪-in-terms-of-⊑ I I κ

Idl-𝔻-is-not-algebraic : ¬ (is-algebraic-dcpo Idl-𝔻)
Idl-𝔻-is-not-algebraic = ∥∥-rec 𝟘-is-prop γ
 where
  γ : ¬ (structurally-algebraic Idl-𝔻)
  γ str-alg = ∥∥-rec 𝟘-is-prop r I-inh
   where
    open structurally-algebraic str-alg
    x : 𝔻
    x = middle
    I-inh : ∥ index-of-compact-family (↓ x) ∥
    I-inh = inhabited-if-Directed Idl-𝔻 (compact-family (↓ x))
                                         (compact-family-is-directed (↓ x))
    r : ¬ (index-of-compact-family (↓ x))
    r i = Idl-𝔻-has-no-compact-elements (compact-family (↓ x) i)
                                        (compact-family-is-compact (↓ x) i)

\end{code}
