Martin Escardo & Tom de Jong, June 2023.

More about iterative ordinals and their relation to iterative (multi)sets.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Ordinals-working
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Ordinals 𝓤 ua
open import Iterative.Sets 𝓤 ua
open import W.Type
open import Ordinals.Equivalence
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type hiding (Ord)
open import Ordinals.Underlying
open import Ordinals.WellOrderTransport
open import UF.Equiv-FunExt
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

𝕍-recursion : (P : 𝓥 ̇ )
            → ((X : 𝓤 ̇ ) → (X → P) → P)
            → 𝕍 → P
𝕍-recursion P RH = 𝕍-induction
                    (λ _ → P)
                    (λ X _ _ → RH X)


rank : 𝕍 → 𝕆
rank = 𝕍-induction (λ _ → 𝕆) {!!}
 where
  f : (X : 𝓤 ̇) (ϕ : X → 𝕍) → is-embedding ϕ
    → (X → 𝕆) → 𝕆
  f = {!!}


open import UF.PropTrunc
open import Quotient.Type -- hiding (is-prop-valued)

open import Ordinals.Arithmetic fe'
open import Ordinals.ArithmeticProperties ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua

module 𝕍-to-Ord-construction
        (pt : propositional-truncations-exist)
        (sq : set-quotients-exist)
       where

 open suprema pt (set-replacement-from-set-quotients sq pt)

 𝕍-to-Ord : 𝕍 → Ord
 𝕍-to-Ord = 𝕍-induction (λ _ → Ord) f
  where
   f : (X : 𝓤 ̇  ) (ϕ : X → 𝕍) (e : is-embedding ϕ)
     → ((x : X) → Ord) → Ord
   f X ϕ e r = sup (λ x → r x +ₒ 𝟙ₒ)

 𝕍-to-Ord-behaviour : (A : 𝕍)
                    → 𝕍-to-Ord A ＝ sup (λ x → 𝕍-to-Ord (𝕍-forest A x) +ₒ 𝟙ₒ)
 𝕍-to-Ord-behaviour A =
  𝕍-to-Ord A ＝⟨ ap 𝕍-to-Ord ((𝕍-η A) ⁻¹) ⟩
  𝕍-to-Ord {!!} ＝⟨ {!!} ⟩
  {!!} ∎

\end{code}
