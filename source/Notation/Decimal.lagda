Martin Escardo 12th September 2024

This file provides an interface to implement automatic converscxion of
decimal literals to types other than just the natural numbers.

See https://agda.readthedocs.io/en/latest/language/literal-overloading.html

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Notation.Decimal where

open import MLTT.Universes
open import MLTT.NaturalNumbers

record Decimal {𝓤 𝓥 : Universe} (A : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    constraint : ℕ → 𝓥 ̇
    fromℕ : (n : ℕ) {{_ : constraint n}} → A

open Decimal {{...}} public using (fromℕ)

{-# BUILTIN FROMNAT fromℕ #-}
{-# DISPLAY Decimal.fromℕ _ n = fromℕ n #-}

record Negative {𝓤 𝓥 : Universe} (A : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ⁺ ̇ where
  field
    constraint : ℕ → 𝓥 ̇
    fromNeg : (n : ℕ) {{_ : constraint n}} → A

open Negative {{...}} public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}
{-# DISPLAY Negative.fromNeg _ n = fromNeg n #-}

data No-Constraint : 𝓤₀ ̇ where
 no-constraint : No-Constraint

instance
 really-no-constraint : No-Constraint
 really-no-constraint = no-constraint

make-decimal-with-no-constraint
 : {A : 𝓤 ̇ }
 → ((n : ℕ)  {{_ : No-Constraint}} → A)
 → Decimal A
make-decimal-with-no-constraint f =
 record {
   constraint = λ _ → No-Constraint
 ; fromℕ = f
 }

make-negative-with-no-constraint
 : {A : 𝓤 ̇ }
 → ((n : ℕ)  {{_ : No-Constraint}} → A)
 → Negative A
make-negative-with-no-constraint f =
 record {
   constraint = λ _ → No-Constraint
 ; fromNeg = f
 }

\end{code}

The natural place for this would be MLTT.NaturalNumbers, but then we
would get a circular dependency.

\begin{code}

instance
 Decimal-ℕ-to-ℕ : Decimal ℕ
 Decimal-ℕ-to-ℕ = make-decimal-with-no-constraint (λ n → n)

\end{code}
