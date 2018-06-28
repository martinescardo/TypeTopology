Martin Escardo, 28 June 2018

For a universe (and hence an injective type) W and an embedding
j : X → A, if every type in a family Y : X → W has the structure of an
ordinal, then so does every type in the extended family Y/j : A → W.

                   j
              X ------> A
               \       / 
                \     /
             Y   \   / Y/j
                  \ /
                   v
                   W

This is a direct application of the construction in the module
OrdinalArithmetic.prop-indexed-product-of-ordinals.

This assumes X : W, A : W, and that the given ordinal structure is
W-valued. More generally, we have the following typing, for which the
above triangle no longer makes sense, because Y / j : A → U ⊔ V ⊔ W,
but the constructions still work.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Embedding
open import OrdinalArithmetic
open import UF-Equiv
open import UF-Subsingletons
open import Ordinals

module ExtensionOrdinalFamily
        (fe : ∀ U V → funext U V)
        {U V W}
        {X : U ̇}
        {A : V ̇}
        {Y : X → W ̇}
        (j : X → A)
        (ise : is-embedding j)
        (_<_ : {x : X} → Y x → Y x → W ̇) 
        (o : (x : X) → is-ordinal (_<_ {x}))
        (a : A)
       where

open import UF-InjectiveTypes (fe)

_≺_ : (Y / j) a → (Y / j) a → U ⊔ V ⊔ W ̇
u ≺ v = Σ \(p : fiber j a) → u p < v p 

ordinal : is-ordinal _≺_
ordinal = prop-indexed-product-of-ordinals.ordinal
           (fiber j a)
           (ise a)
           (λ (p : fiber j a) → Y (pr₁ p))
           (λ {p : fiber j a} y y' → y < y')
           (λ (p : fiber j a) → o (pr₁ p))
           (fe (U ⊔ V) W) 

\end{code}
