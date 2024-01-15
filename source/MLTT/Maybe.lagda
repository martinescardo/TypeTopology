\begin{code}

{-# OPTIONS --safe --without-K #-} --

module MLTT.Maybe where

open import MLTT.Spartan

data Maybe {𝓤 : Universe} (A : 𝓤 ̇ ) : 𝓤 ̇ where
 Nothing : Maybe A
 Just    : A → Maybe A

{-# BUILTIN MAYBE Maybe #-}

Just-is-not-Nothing : {A : 𝓤 ̇ } {a : A} → Just a ≠ Nothing
Just-is-not-Nothing ()

Nothing-is-isolated : {A : 𝓤 ̇ } (x : Maybe A) → is-decidable (Nothing ＝ x)
Nothing-is-isolated Nothing  = inl refl
Nothing-is-isolated (Just a) = inr (λ (p : Nothing ＝ Just a) → Just-is-not-Nothing (p ⁻¹))

Nothing-is-isolated' : {A : 𝓤 ̇ } (x : Maybe A) → is-decidable (x ＝ Nothing)
Nothing-is-isolated' Nothing  = inl refl
Nothing-is-isolated' (Just a) = inr Just-is-not-Nothing

open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons

Nothing-is-h-isolated : {A : 𝓤 ̇ } (x : Maybe A) → is-prop (Nothing ＝ x)
Nothing-is-h-isolated x = isolated-is-h-isolated Nothing Nothing-is-isolated

Nothing-is-h-isolated' : {A : 𝓤 ̇ } (x : Maybe A) → is-prop (x ＝ Nothing)
Nothing-is-h-isolated' x = equiv-to-prop ＝-flip (Nothing-is-h-isolated x)

\end{code}
