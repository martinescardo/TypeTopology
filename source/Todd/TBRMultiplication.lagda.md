```agda

{-- OPTIONS --allow-unsolved-metas --}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons

module Todd.TBRMultiplication
 (pt : propositional-truncations-exist)
 (fe : FunExt)
 (pe : PropExt)
 (sq : set-quotients-exist)
 where

open import Todd.TBRDyadicReals pt fe pe sq
open import Todd.TBRFunctions pt fe pe sq
open PropositionalTruncation pt


```
