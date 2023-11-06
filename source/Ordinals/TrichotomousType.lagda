Martin Escardo, 3rd May 2022

The subtype Ordinal₃ 𝓤 of Ordinal 𝓤 consisting of trichotomous ordinals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Ordinals.TrichotomousType
        (fe : FunExt)
       where

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Notions
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.Sets
open import UF.Subsingletons

Ordinal₃ : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinal₃ 𝓤 = Σ α ꞉ Ordinal 𝓤 , is-trichotomous-order (underlying-order α)

instance
 canonical-map-Ordinal₃-Ordinal : Canonical-Map (Ordinal₃ 𝓤) (Ordinal 𝓤)
 ι {{canonical-map-Ordinal₃-Ordinal}} (α , _) = α

instance
 underlying-type-of-3-ordinal : Underlying (Ordinal₃ 𝓤)
 ⟨_⟩ {{underlying-type-of-3-ordinal}} (α , _) = ⟨ α ⟩
 underlying-order {{underlying-type-of-3-ordinal}} (α , _) = underlying-order α


underlying-type-is-set₃ : FunExt
                        → (β : Ordinal₃ 𝓤)
                        → is-set ⟨ β ⟩
underlying-type-is-set₃ fe (α , t) = underlying-type-is-set fe α

\end{code}

Topped ordinals are ranged over by τ,υ.

\begin{code}

≼-prop-valued : (τ : Ordinal₃ 𝓤) (x y : ⟨ τ ⟩) → is-prop (x ≼⟨ τ ⟩ y)
≼-prop-valued {𝓤} τ = extensional-po-is-prop-valued (underlying-order τ) fe
                       (Prop-valuedness [ τ ])

3is-well-ordered : (τ : Ordinal₃ 𝓤) → is-well-order (underlying-order τ)
3is-well-ordered ((X , _<_ , o) , t) = o

3is-trichotomous : (τ : Ordinal₃ 𝓤) → is-trichotomous-order (underlying-order τ)
3is-trichotomous ((X , _<_ , o) , t) = t

\end{code}
