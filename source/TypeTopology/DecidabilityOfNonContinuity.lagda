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

{-# OPTIONS --safe --without-K --lossy-unification #-}

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

 1. MP gives that continuity and doubly negated continuity agree.

 2. WLPO is equivalent to the existence of a noncontinuous function ℕ∞ → ℕ.

 3. ¬ WLPO is equivalent to the doubly negated continuity of all functions ℕ∞ → ℕ.

 4. If MP and ¬WLPO then all functions ℕ∞ → ℕ are continuous.

Added 24th July 2024. Still based on the same paper. We write down the proof of 3.

\begin{code}

open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness fe

discontinuous-map-gives-WLPO : (f : ℕ∞ → ℕ) → ¬ continuous f → WLPO
discontinuous-map-gives-WLPO f f-non-cts = VII
 where
  A : ℕ∞ → ℕ∞ → 𝓤₀ ̇
  A u v = f (max u v) ＝ f ∞

  A-is-complemented : (u v : ℕ∞) → is-decidable (A u v)
  A-is-complemented u v = ℕ-is-discrete (f (max u v)) (f ∞)

  I : (u : ℕ∞) → Σ v₀ ꞉ ℕ∞ , (f (max u v₀) ＝ f ∞ → (v : ℕ∞) → f (max u v) ＝ f ∞)
  I u = ℕ∞-Compact∙ (A u) (A-is-complemented u)

  G : ℕ∞ → ℕ∞
  G u = max u (pr₁ (I u))

  G-property : (u : ℕ∞)
             → f (G u) ＝ f ∞
             → (v : ℕ∞)
             → f (max u v) ＝ f ∞
  G-property u = pr₂ (I u)

  G-property₁ : (u : ℕ∞)
              → (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
              → f (G u) ≠ f ∞
  G-property₁ u (v , d) = contrapositive
                            (λ (e : f (G u) ＝ f ∞) → G-property u e v)
                            d

  II : (u : ℕ∞)
     → ¬¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
     → (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
  II u = Σ-Compactness-gives-Markov
          ℕ∞-Compact
          (λ v → f (max u v) ≠ f ∞)
          (λ v → ¬-preserves-decidability
                  (ℕ-is-discrete (f (max u v)) (f ∞)))

  III : (u : ℕ∞)
      → ¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
      → (v : ℕ∞) → f (max u v) ＝ f ∞
  III u ν v  = discrete-is-¬¬-separated
                ℕ-is-discrete
                (f (max u v))
                (f ∞)
                (λ (d : f (max u v) ≠ f ∞) → ν (v , d))

  IV : (u : ℕ∞)
     → ¬ ((v : ℕ∞) → f (max u v) ＝ f ∞)
     → ¬¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
  IV u = contrapositive (III u)

  G-property₂ : (u : ℕ∞)
              → ¬ ((v : ℕ∞) → f (max u v) ＝ f ∞)
              → f (G u) ≠ f ∞
  G-property₂ u a = G-property₁ u (II u (IV u a))

  G-property₃ : (n : ℕ) → f (G (ι n)) ≠ f ∞
  G-property₃ n = G-property₂ (ι n) h
   where
    h : ¬ ((v : ℕ∞) → f (max (ι n) v) ＝ f ∞)
    h a = f-non-cts (n , (λ n → a (ι n)))

  G-property∞ : G ∞ ＝ ∞
  G-property∞ = max∞-property (pr₁ (I ∞))

  V : (u : ℕ∞) → u ＝ ∞ → f (G u) ＝ f ∞
  V u refl = ap f G-property∞

  VI : (u : ℕ∞) → f (G u) ＝ f ∞ → u ＝ ∞
  VI u a = not-finite-is-∞ fe VI₀
   where
    VI₀ : (n : ℕ) → u ≠ ι n
    VI₀ n refl = G-property₃ n a

  VII : WLPO
  VII u = map-decidable (VI u) (V u) (ℕ-is-discrete (f (G u)) (f ∞))

open import Taboos.BasicDiscontinuity fe
open import Naturals.Properties

WLPO-iff-there-is-a-noncontinous-map : WLPO ↔ (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
WLPO-iff-there-is-a-noncontinous-map =
  I ,
  (λ (f , ν) → discontinuous-map-gives-WLPO f ν)
 where
  I : WLPO → Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f
  I wlpo = f , f-non-cts
   where
    p : ℕ∞ → 𝟚
    p = pr₁ (WLPO-is-discontinuous wlpo)

    p-spec : ((n : ℕ) → p (ι n) ＝ ₀) × (p ∞ ＝ ₁)
    p-spec = pr₂ (WLPO-is-discontinuous wlpo)

    g : 𝟚 → ℕ
    g ₀ = 0
    g ₁ = 1

    f : ℕ∞ → ℕ
    f = g ∘ p

    f₀ : (n : ℕ) → f (ι n) ＝ 0
    f₀ n =  f (ι n) ＝⟨ ap g (pr₁ p-spec n) ⟩
            g ₀     ＝⟨ refl ⟩
            0       ∎

    f∞ : (n : ℕ) → f (ι n) ≠ f ∞
    f∞ n e = zero-not-positive 0
              (0       ＝⟨ f₀ n ⁻¹ ⟩
               f (ι n) ＝⟨ e ⟩
               f ∞     ＝⟨ ap g (pr₂ p-spec) ⟩
               1       ∎)

    f-non-cts : ¬ continuous f
    f-non-cts (m , a) = f∞ m
                         (f (ι m)             ＝⟨ ap f ((max∞-idemp fe (ι m))⁻¹) ⟩
                          f (max (ι m) (ι m)) ＝⟨ a m ⟩
                          f ∞                 ∎)

¬WLPO-iff-all-maps-are-¬¬-continuous : ¬ WLPO ↔ ((f : ℕ∞ → ℕ) → ¬¬ continuous f)
¬WLPO-iff-all-maps-are-¬¬-continuous =
 (λ nwlpo f f-non-cts
   → contrapositive
      (rl-implication WLPO-iff-there-is-a-noncontinous-map)
      nwlpo
      (f , f-non-cts)) ,
 (λ (a : (f : ℕ∞ → ℕ) → ¬¬ continuous f)
   → contrapositive
      (lr-implication WLPO-iff-there-is-a-noncontinous-map)
      (λ (f , f-non-cts) → a f f-non-cts))

\end{code}
