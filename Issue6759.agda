{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

{-# OPTIONS -v tc.meta.assign:15 #-}
{-# OPTIONS -v tc.meta.occurs:45 #-}
{-# OPTIONS -v tc.instance:45 #-}

open import MLTT.Spartan
open import UF.Univalence

module Issue6759
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

open import Iterative.Ordinals6759 𝓤 ua

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
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
open import W.Type

Ord-to-𝕍-behaviour : (α : Ord)
                   → Ord-to-𝕍 α ＝ 𝕍-ssup ⟨ α ⟩
                                    (λ (x : ⟨ α ⟩) → Ord-to-𝕍 (α ↓ x))
                                    (Ord-to-𝕍↓-is-embedding α)
Ord-to-𝕍-behaviour α = {! to-subtype-＝ being-iset-is-prop (Ord-to-𝕄-behaviour α) !}

-- -- Provoke a type error

-- crash : Set₁ → Set
-- crash A = A
