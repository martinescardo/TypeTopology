Martin Escardo, 7 May 2014.

For any function f : ℕ∞ → ℕ, it is decidable whether f is non-continuous.

  Π (f : ℕ∞ → ℕ). ¬ (continuous f) + ¬¬ (continuous f).

Based on the paper

    Mathematical Structures in Computer Science , Volume 25,
    October 2015 , pp. 1578 - 1589
    DOI: https://doi.org/10.1017/S096012951300042X

The title of this paper is a bit misleading. It should have been
called "Decidability of non-continuity".

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.DecidabilityOfNonContinuity (fe : funext 𝓤₀ 𝓤₀) where

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import NotionsOfDecidability.Decidable
open import TypeTopology.ADecidableQuantificationOverTheNaturals fe
open import UF.DiscreteAndSeparated

Lemma-3·1 : (q : ℕ∞ → ℕ∞ → 𝟚)
          → is-decidable ((m : ℕ) → ¬ ((n : ℕ) → q (ι m) (ι n) ＝ ₁))
Lemma-3·1 q = claim₄
 where
  A : ℕ∞ → 𝓤₀ ̇
  A u = (n : ℕ) → q u (ι n) ＝ ₁

  claim₀ :  (u : ℕ∞) → is-decidable (A u)
  claim₀ u = Theorem-8·2 (q u)

  p : ℕ∞ → 𝟚
  p = indicator-map claim₀

  claim₁ : is-decidable ((n : ℕ) → p (ι n) ＝ ₁)
  claim₁ = Theorem-8·2 p

  claim₂ : ((n : ℕ) → ¬ A (ι n)) → (n : ℕ) → p (ι n) ＝ ₁
  claim₂ φ n = different-from-₀-equal-₁
                (λ v → φ n (indicator-property₀ claim₀ (ι n) v))

  claim₃ : ((n : ℕ) → p (ι n) ＝ ₁) → (n : ℕ) → ¬ A (ι n)
  claim₃ f n = indicator-property₁ claim₀ (ι n) (f n)

  claim₄ : is-decidable ((n : ℕ) → ¬ (A (ι n)))
  claim₄ = map-decidable claim₃ claim₂ claim₁

\end{code}

Omitting the inclusion function, or coercion,

   ι : ℕ → ℕ∞,

a map f : ℕ∞ → ℕ is called continuous iff

   ∃ m. ∀ n ≥ m. f n ＝ ∞,

where m and n range over the natural numbers.

The negation of this statement is equivalent to

   ∀ m. ¬ ∀ n ≥ m. f n ＝ ∞.

We can implement ∀ y ≥ x. A y as ∀ x. A (max x y), so that the
continuity of f amounts to

   ∃ m. ∀ n. f (max m n) ＝ ∞,

and its negation to

   ∀ m. ¬ ∀ n. f (max m n) ＝ ∞.

\begin{code}

continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
continuous f = Σ m ꞉ ℕ , ((n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)

Theorem-3·2 : (f : ℕ∞ → ℕ) → is-decidable (¬ continuous f)
Theorem-3·2 f = V
 where
  ncf : 𝓤₀ ̇
  ncf = (m : ℕ) → ¬ ((n : ℕ) → f (max (ι m) (ι n)) ＝[ℕ] f ∞)

  I : ncf → ¬ continuous f
  I ν (m , a) = ν m (λ n → lr-implication
                            (＝-agrees-with-＝[ℕ]
                              (f (max (ι m) (ι n)))
                              (f ∞))
                            (a n))

  II : ¬ continuous f → ncf
  II ν m a = ν (m , (λ n → rl-implication
                            (＝-agrees-with-＝[ℕ]
                               (f (max (ι m) (ι n)))
                               (f ∞))
                            (a n)))

  III : is-decidable ncf
  III = Lemma-3·1 (λ x y → χ＝ (f (max x y)) (f ∞))

  V : is-decidable (¬ continuous f)
  V = map-decidable I II III

\end{code}

(Maybe) to be continued (see the paper for the moment).

 * MP gives that continuity and doubly negated continuity agree.

 * WLPO is equivalent to the existence of a noncontinuous function ℕ∞ → ℕ.

 * ¬WLPO is equivalent to the doubly negated continuity of all functions ℕ∞ → ℕ.

 * If MP and ¬WLPO then all functions ℕ∞ → ℕ are continuous.
