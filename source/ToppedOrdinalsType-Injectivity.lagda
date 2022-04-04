Martin Escardo, 2018

The type of topped ordinals is (algebraically) injective.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module ToppedOrdinalsType-Injectivity (fe : FunExt) where

open import SpartanMLTT

open import UF-Base
open import UF-Equiv
open import UF-Embeddings

open import OrdinalNotions
open import OrdinalsType
open import OrdinalsWellOrderArithmetic
open import InjectiveTypes fe
open import ToppedOrdinalsType fe
open import OrdinalsType-Injectivity fe
     renaming (_↗_ to _↗ₒ_ ; ↗-property to ↗ₒ-property)

_↗_ : {I : 𝓤  ̇ } {J : 𝓥 ̇ }
    → (I → Ordinalᵀ 𝓦)
    → (I ↪ J)
    → (J → Ordinalᵀ (𝓤 ⊔ 𝓥 ⊔ 𝓦))
τ ↗ (e , e-is-embedding) = λ j → ((t / e) j ,
                                  Extension.order j ,
                                  Extension.well-order j (λ i → tis-well-ordered (τ i))) ,
                                  Extension.top-preservation j (λ i → topped (τ i))
 where
  t = λ x → ⟪ τ x ⟫
  module Extension = extension fe t e e-is-embedding (λ {i} → tunderlying-order (τ i))

\end{code}

Added 1st April 2022.

\begin{code}

↗-property : {I : 𝓤  ̇ } {J : 𝓥 ̇ }
             (α : I → Ordinalᵀ 𝓤)
           → (𝓮@(e , e-is-embedding) : I ↪ J)
           → (i : I) → [ (α ↗ 𝓮) (e i) ] ≃ₒ [ α i ]
↗-property α = ↗ₒ-property (λ i → [ α i ])

\end{code}
