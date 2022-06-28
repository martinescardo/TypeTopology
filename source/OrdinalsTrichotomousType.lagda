Martin Escardo, 3rd May 2022

The subtype Ordinal₃ 𝓤 of Ordinal 𝓤 consisting of trichotomous ordinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module OrdinalsTrichotomousType
        (fe : FunExt)
       where

open import SpartanMLTT
open import OrdinalNotions
open import OrdinalsType

open import UF-Base
open import UF-Subsingletons

Ordinal₃ : ∀ 𝓤 → 𝓤 ⁺ ̇
Ordinal₃ 𝓤 = Σ α ꞉ Ordinal 𝓤 , is-trichotomous-order (underlying-order α)

⁅_⁆ : Ordinal₃ 𝓤 → Ordinal 𝓤
⁅ α , t ⁆ = α

⦅_⦆ : Ordinal₃ 𝓤 → 𝓤 ̇
⦅ (X , _<_ , o) , t ⦆ = X

underlying-type-is-set₃ : FunExt
                        → (β : Ordinal₃ 𝓤)
                        → is-set ⦅ β ⦆
underlying-type-is-set₃ fe (α , t) = underlying-type-is-set fe α

\end{code}

Topped ordinals are ranged over by τ,υ.

\begin{code}

3underlying-order : (τ : Ordinal₃ 𝓤) → ⦅ τ ⦆ → ⦅ τ ⦆ → 𝓤 ̇
3underlying-order ((X , _<_ , o) , t) = _<_

syntax 3underlying-order τ x y = x ≺⦅ τ ⦆ y

3underlying-rorder : (τ : Ordinal₃ 𝓤) → ⦅ τ ⦆ → ⦅ τ ⦆ → 𝓤 ̇
3underlying-rorder τ x y = ¬ (y ≺⦅ τ ⦆ x)

syntax 3underlying-rorder τ x y = x ≼⦅ τ ⦆ y

≼-prop-valued : (τ : Ordinal₃ 𝓤) (x y : ⦅ τ ⦆) → is-prop (x ≼⦅ τ ⦆ y)
≼-prop-valued {𝓤} τ x y l m = dfunext (fe 𝓤 𝓤₀) (λ x → 𝟘-elim (m x))

3is-well-ordered : (τ : Ordinal₃ 𝓤) → is-well-order (3underlying-order τ)
3is-well-ordered ((X , _<_ , o) , t) = o

3is-trichotomous : (τ : Ordinal₃ 𝓤) → is-trichotomous-order (3underlying-order τ)
3is-trichotomous ((X , _<_ , o) , t) = t

\end{code}
