Martin Escardo, 28 June 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Embedding
open import OrdinalArithmetic
open import UF-Equiv
open import UF-Subsingletons
open import Ordinals

module ExtensionOrdinal (fe : ∀ U V → funext U V)
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

open prop-indexed-product-of-ordinals
            (fiber j a)
            (ise a)
            (λ (p : fiber j a) → Y (pr₁ p))
            (λ {p : fiber j a} y y' → y < y')
            (λ (p : fiber j a) → o (pr₁ p))
            (fe (U ⊔ V) W) 

_≺_ : (Y / j) a → (Y / j) a → U ⊔ V ⊔ W ̇
_≺_ = order

o' : is-ordinal _≺_
o' = ordinal

\end{code}
