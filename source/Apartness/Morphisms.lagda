Martin Escardo, 26 January 2018.

Moved from the file TypeTopology.TotallySeparated 22 August 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Apartness.Morphisms where

open import Apartness.Definition
open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

A map is called strongly extensional if it reflects apartness. In the
category of apartness types, the morphisms are the strongly
extensional maps.

\begin{code}

is-strongly-extensional : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → (X → X → 𝓦 ̇ ) → (Y → Y → 𝓣 ̇ ) → (X → Y) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
is-strongly-extensional _♯_ _♯'_ f = ∀ x x' → f x ♯' f x' → x ♯ x'

being-strongly-extensional-is-prop : Fun-Ext
                                   → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                   → (_♯_ : X → X → 𝓦 ̇ )
                                   → (_♯'_ : Y → Y → 𝓣 ̇ )
                                   → is-prop-valued _♯_
                                   → (f : X → Y)
                                   → is-prop (is-strongly-extensional _♯_ _♯'_ f)
being-strongly-extensional-is-prop fe _♯_ _♯'_ ♯p f =
 Π₃-is-prop  fe (λ x x' a → ♯p x  x')

preserves : ∀ {𝓣} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
          → (X → X → 𝓦 ̇ ) → (Y → Y → 𝓣 ̇ ) → (X → Y) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
preserves R S f = ∀ {x x'} → R x x' → S (f x) (f x')

\end{code}
