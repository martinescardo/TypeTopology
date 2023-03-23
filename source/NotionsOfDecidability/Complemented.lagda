Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module NotionsOfDecidability.Complemented where

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import NotionsOfDecidability.Decidable

\end{code}

We again have a particular case of interest.  Complemented subsets,
defined below, are often known as decidable subsets. Agda doesn't
allow overloading of terminology, and hence we gladly accept the
slighly non-universal terminology.

\begin{code}

complemented : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
complemented A = ∀ x → decidable(A x)

characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → complemented A
                        → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ →   A x)
                                                   × (p x ＝ ₁ → ¬ (A x)))
characteristic-function = indicator

co-characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           → complemented A
                           → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → ¬ (A x))
                                                      × (p x ＝ ₁ →   A x))
co-characteristic-function d = indicator(λ x → +-commutative(d x))

\end{code}
