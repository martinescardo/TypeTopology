Martin Escardo, 28 June 2018

For a universe (and hence an injective type) 𝓦 and an embedding
j : X → A, if every type in a family Y : X → 𝓦 has the structure of an
ordinal, then so does every type in the extended family Y/j : A → 𝓦.

                   j
              X ------> A
               \       /
                \     /
             Y   \   / Y/j
                  \ /
                   v
                   𝓦

This is a direct application of the construction in the module
OrdinalArithmetic.prop-indexed-product-of-ordinals.

This assumes X A : 𝓦, and that the given ordinal structure is
W-valued. More generally, we have the following typing, for which the
above triangle no longer makes sense, because Y / j : A → 𝓤 ⊔ 𝓥 ⊔ 𝓦,
but the constructions still work.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.WellOrderExtension where

open import MLTT.Spartan
open import Ordinals.Notions
open import UF.FunExt
open import UF.Subsingletons
open import UF.Embeddings
open import Ordinals.WellOrderArithmetic

module extension
        (fe : FunExt)
        {𝓤 𝓥 𝓦}
        {X : 𝓤 ̇ }
        {A : 𝓥 ̇ }
        (Y : X → 𝓦 ̇ )
        (j : X → A)
        (j-is-embedding : is-embedding j)
        (_<_ : {x : X} → Y x → Y x → 𝓦 ̇ )
        (a : A)
       where

 open import InjectiveTypes.Blackboard fe

 private
  _≺_ : (Y / j) a → (Y / j) a → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  u ≺ v = Σ p ꞉ fiber j a , u p < v p

 order = _≺_

 well-order : ((x : X) → is-well-order (_<_ {x}))
            → is-well-order _≺_
 well-order o = pip.well-order
                 (fe (𝓤 ⊔ 𝓥) 𝓦)
                 (fiber j a)
                 (j-is-embedding a)
                 (λ (p : fiber j a) → Y (pr₁ p))
                 (λ {p : fiber j a} y y' → y < y')
                 (λ (p : fiber j a) → o (pr₁ p))

 top-preservation : ((x : X) → has-top (_<_ {x})) → has-top _≺_
 top-preservation f = φ , g
  where
   φ : (p : fiber j a) → Y (pr₁ p)
   φ (x , r) = pr₁ (f x)

   g : (ψ : (Y / j) a) → ¬ (φ ≺ ψ)
   g ψ ((x , r) , l) = pr₂ (f x) (ψ (x , r)) l

\end{code}
