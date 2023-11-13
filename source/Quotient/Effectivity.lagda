Martin Escardo and Tom de Jong, written in Agda 12 September 2023, done in 2022.

A quotient is said to be effective if for every x, y : X, we have
x ≈ y whenever η/ x ＝ ‌η/ y. Notice that we didn't include effectivity
as a requirement in 'set-quotients-exist', but it turns out that
effectivity follows from the other properties, at least in the
presence of function extensionality and propositonal
extensionality. The proof is as follows:

 (1) First construct propositional truncations using assumed set
     quotients.

 (2) Construct another (large) quotient as described in
     Quotient.Large.

 (3) This large quotient is effective, but has to be isomorphic to the assumed
     set quotient, hence this quotient has to be effective as well.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Subsingletons

module Quotient.Effectivity
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import MLTT.Spartan
open import Quotient.Type
open import Quotient.Large
open import Quotient.GivesPropTrunc
open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons-FunExt

effectivity : (sq : set-quotients-exist)
            → are-effective sq
effectivity sq = sq-effective
 where
  pt : propositional-truncations-exist
  pt = propositional-truncations-from-set-quotients sq fe

  lsq : large-set-quotients-exist
  lsq = large-set-quotients pt fe pe

  lsq-effective : are-effective lsq
  lsq-effective = large-effective-set-quotients pt fe pe

  sq-effective : are-effective sq
  sq-effective {𝓤} {𝓥} {X} R {x} {y} p = γ
   where
    module s = general-set-quotients-exist sq
    module l = general-set-quotients-exist lsq

    X/R : 𝓤 ⊔ 𝓥 ̇
    X/R = X s./ R

    η : X → X/R
    η = s.η/ R

    have-p : η x ＝ η y
    have-p = p

    X/ₗR : 𝓤 ⊔ (𝓥 ⁺) ̇
    X/ₗR = X l./ R

    ηₗ : X → X/ₗR
    ηₗ = l.η/ R

    e : ∃! f ꞉ (X/R → X/ₗR) , f ∘ η ∼ ηₗ
    e = s./-universality R (l./-is-set R) ηₗ (l.η/-identifies-related-points R)

    f : X/R → X/ₗR
    f = ∃!-witness e

    f-property : f ∘ η ∼ ηₗ
    f-property = ∃!-is-witness e

    q = ηₗ x    ＝⟨ (f-property x)⁻¹ ⟩
        f (η x) ＝⟨ ap f p ⟩
        f (η y) ＝⟨ f-property y ⟩
        ηₗ y    ∎

    γ : x ≈[ R ] y
    γ = lsq-effective R {x} {y} q

\end{code}
