Martin Escardo

For the moment we consider 0-connected types only, referred to as
connected types for the sake of brevity.

There is a formulation that doesn't require propositional truncations,
but increases universe levels. We start with that formulation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.PropTrunc

module UF.Connected (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import UF.FunExt
open import UF.Hedberg
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

is-wconnected : 𝓤 ̇ → 𝓤 ̇
is-wconnected X = (x y : X) → ∥ x ＝ y ∥

is-connected : 𝓤 ̇ → 𝓤 ̇
is-connected X = ∥ X ∥ × is-wconnected X

being-wconnected-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-wconnected X)
being-wconnected-is-prop fe = Π-is-prop fe (λ x → Π-is-prop fe (λ y → ∥∥-is-prop))

being-connected-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-connected X)
being-connected-is-prop fe = ×-is-prop ∥∥-is-prop (being-wconnected-is-prop fe)

maps-of-wconnected-types-into-sets-are-constant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                                → is-set Y
                                                → is-wconnected X
                                                → (f : X → Y) → wconstant f
maps-of-wconnected-types-into-sets-are-constant {𝓤} {𝓥} {X} {Y} s w f x x' = γ
 where
  a : ∥ x ＝ x' ∥
  a = w x x'
  γ : f x ＝ f x'
  γ = ∥∥-rec s (ap f) a

\end{code}
