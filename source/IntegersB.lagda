18/05/22 - Andrew Sneap

This file defines Integers using existing natural numbers, the
successor and predecessor functions, induction on integers and the
canonical inclusion of natural numbers in the integers.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

module IntegersB where

\end{code}

In order to avoid having positive and negative 0, a standard solutions
to have the negative constructor denote λ n → - (n + 1).
For example, negsucc 0 = -1
             negsucc 4 = -5.

\begin{code}

data ℤ : 𝓤₀ ̇ where 
 pos     : ℕ → ℤ
 negsucc : ℕ → ℤ

\end{code}

Now we have the predecessor and successor functions on integers.
By case analysis and reflexivity, these functions are inverses.

\begin{code}

predℤ : ℤ → ℤ
predℤ (pos 0)        = negsucc 0
predℤ (pos (succ x)) = pos x
predℤ (negsucc x)    = negsucc (succ x)

succℤ : ℤ → ℤ
succℤ (pos x)            = pos (succ x)
succℤ (negsucc 0)        = pos 0
succℤ (negsucc (succ x)) = negsucc x

succpredℤ : (x : ℤ) → succℤ (predℤ x) ≡ x 
succpredℤ (pos 0)        = refl
succpredℤ (pos (succ x)) = refl
succpredℤ (negsucc x)    = refl

predsuccℤ : (x : ℤ) → predℤ (succℤ x) ≡ x 
predsuccℤ (pos x)            = refl
predsuccℤ (negsucc 0)        = refl
predsuccℤ (negsucc (succ x)) = refl
{-
ℤ-decidable : (x y : ℤ) → (x ≡ y) ∔ ¬ (x ≡ y)
ℤ-decidable (pos x) (pos y) = {!!}
ℤ-decidable (pos x) (negsucc y) = inr {!!}
ℤ-decidable (negsucc x) (pos y) = {!!}
ℤ-decidable (negsucc x) (negsucc y) = {!!}
-}
\end{code}



\begin{code}
{-
open import NaturalNumbers-Properties

ℤ-cases : {A : ℤ → 𝓤 ̇}
        → (b : ℤ)
        → A b
        → ((k : ℤ) → A k → A (succℤ k))
        → ((k : ℤ) → A (succℤ k) → A k)
        → (x : ℤ)
        → A x
ℤ-cases {𝓤} {A} b C₀ Cₚ Cₙ x = {!!}
-}
{-
ℤ-induction' : {A : ℤ → 𝓤 ̇} → A (pos 0)
                             → ((k : ℤ) → A k → A (succℤ k))
                             → ((k : ℤ) → A (succℤ k) → A k)
                             → (x : ℤ)          
                             → A x
ℤ-induction' c₀ cₛ cₙ x = ℤ-cases x (λ e → transport (λ v → {!!}) (e ⁻¹) c₀) (λ y e → {!!}) {!!}                            
-}
ℤ-induction : {A : ℤ → 𝓤 ̇} → A (pos 0)
                             → ((k : ℤ) → A k → A (succℤ k))
                             → ((k : ℤ) → A (succℤ k) → A k)
                             → (x : ℤ)          
                             → A x 
ℤ-induction base step₀ step₁ (pos 0)            = base
ℤ-induction base step₀ step₁ (pos (succ x))     = step₀ (pos x) (ℤ-induction base step₀ step₁ (pos x))
ℤ-induction base step₀ step₁ (negsucc 0)        = step₁ (negsucc 0) base
ℤ-induction base step₀ step₁ (negsucc (succ x)) = step₁ (negsucc (succ x)) (ℤ-induction base step₀ step₁ (negsucc x))


open import CanonicalMapNotation

instance
 canonical-map-ℕ-to-ℤ : Canonical-Map ℕ ℤ
 ι {{canonical-map-ℕ-to-ℤ}} = λ x → pos x

\end{code}
