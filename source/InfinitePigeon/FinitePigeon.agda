-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.FinitePigeon where

open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Equality
open import InfinitePigeon.Finite
open import InfinitePigeon.InfinitePigeon
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals
open import InfinitePigeon.Order
open import InfinitePigeon.Two


-- We use the classical, infinite pigeonhole principle (in another
-- module) to derive a finite one:


Finite-Pigeonhole : ₂ℕ → ℕ → Ω
Finite-Pigeonhole α m =
    ∃ \(b : ₂) → ∃ \(s : smaller(m + 1) → ℕ) →
                    (∀(n : smaller m) → s(coerce n) < s(fsucc n))
                  ∧ (∀(n : smaller(m + 1)) → α(s n) ≡ b)


-- Before proving this in the theorem below, we prove it prefixed by K
-- in the following lemma, where some sublemmas have K deep inside,
-- prefixing the equation:


Finite-Pigeonhole-K : {R : Ω} → ₂ℕ → ℕ → Ω
Finite-Pigeonhole-K {R} α m =
    ∃ \(b : ₂) → ∃ \(s : smaller(m + 1) → ℕ) →
                    (∀(n : smaller m) → s(coerce n) < s(fsucc n))
                  ∧ (∀(n : smaller(m + 1)) → K{R}(α(s n) ≡ b))


finite-pigeonhole-lemma : {R : Ω} →
-----------------------

 ∀(α : ₂ℕ) → ∀(m : ℕ) → K(Finite-Pigeonhole α m)


finite-pigeonhole-lemma {R} α m =  K-extend lemma₂ lemma₁
 where
  lemma₀ : Pigeonhole α → Finite-Pigeonhole-K {R} α m
  lemma₀ (∃-intro b (∃-intro g h)) =
          ∃-intro b (∃-intro s (∧-intro fact₁ fact₃))
    where
      s : smaller(m + 1) → ℕ
      s = restriction g

      fact₀ : ∀(n : smaller m) → g(embed n) ≡ s(coerce n)
      fact₀ n = compositionality g embed-coerce-lemma

      fact₁ : ∀(n : smaller m) → s(coerce n) < s(fsucc n)
      fact₁ n = binary-predicate-compositionality {ℕ} {ℕ} {_<_}
                  (fact₀ n) reflexivity (∧-elim₀(h(embed n)))

      fact₂ : ∀(n : smaller(m + 1)) → α(g(embed n)) ≡ b → α(s n) ≡ b
      fact₂ n = two-things-equal-to-a-third-are-equal reflexivity

      fact₃ : ∀(n : smaller(m + 1)) → K(α(s n) ≡ b)
      fact₃ n = K-functor (fact₂ n) (∧-elim₁(h(embed n)))

  lemma₁ : K(Finite-Pigeonhole-K α m)
  lemma₁ = K-functor lemma₀ (pigeonhole α)

  lemma₂ : Finite-Pigeonhole-K α m → K(Finite-Pigeonhole α m)

  lemma₂ (∃-intro b (∃-intro s (∧-intro h k))) =
         K-∃-shift(∃-intro b (K-∃-shift(∃-intro s
           (K-strength(∧-intro h (fK-∀-shift k))))))


-- We now apply Friedman's trick. For given α and m, we let R be the
-- proposition we want to prove, namely Finite-Pigeonhole α m. But we
-- have proved K{R}R in the above lemma. Because this is (R→R)→R, we
-- get R if we apply it to the proof id: R→R.


Theorem :
-------

 ∀(α : ₂ℕ) → ∀(m : ℕ) → Finite-Pigeonhole α m

Theorem α m = finite-pigeonhole-lemma {Finite-Pigeonhole α m} α m id


-- NB. If we remove the implicit parameter in this call to
-- finite-pigeonhole-lemma, Agda infers the required R.
