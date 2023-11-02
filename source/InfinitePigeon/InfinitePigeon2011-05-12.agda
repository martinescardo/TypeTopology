-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K #-}

module InfinitePigeon.InfinitePigeon2011-05-12 where

----------------------------------------------------------------------
--
-- Running a classical proof with choice in Agda.
--
----------------------------------------------------------------------
-- Martin Escardo & Paulo Oliva.
-- Version of 12th May 2011.
--
----------------------------------------------------------------------
--     Theorem (Pigeonhole Principle).
--
--             Every infinite boolean sequence has a constant infinite
--             subsequence.
----------------------------------------------------------------------
--
-- We give a proof that uses excluded middle and countable choice.
--
-- In the module FinitePigeon.agda we derive a corollary that we run
-- in the module Examples.agda, namely that every infinite sequence
-- has constant subsequences of arbitrary length. The point is to
-- illustrate in Agda how we can get witnesses from classical proofs
-- that use countable choice. The finite pigeonhole principle has a
-- simple constructive proof, of course, and hence this is really for
-- illustration purposes only.

-- We work with Friedman's A-translation, which prefixes the
-- generalized double-negation modality K in front of existential
-- quantifiers, disjunctions and equations, where KA = ((A→R)→R) is
-- defined in the module JK-Monads.agda. The proposition R is
-- arbitrary in the proofs of this module, but carefully chosen in the
-- main theorem of the module FinitePigeon.agda, by an application of
-- Friedman's trick. We don't work strictly with the A-translation:
-- when we can get away with it, we place fewer K's than the
-- formal definition of the translation demands.
--
-- Because ⊥ (false) is the empty disjunction, it gets translated to
-- K ⊥, which is equivalent to R. So think of R as ⊥ in the proofs
-- below. Of course, it is not true that R→A for any A (ex falso
-- quodlibet, or ⊥-elimination). But this does hold for any A in the
-- image of the translation.
--
-- Classical countable choice (i.e. choice formulated with the
-- classical existential quantifier) is given a proof term via the
-- K-shift (more commonly known as the double negation shift) in the
-- module K-AC-N.agda and K-Shift.agda. We use either of (1) the
-- Berardi-Bezem-Coquand functional (1998), (2) Berger-Oliva's
-- modified bar recursion (2005), (3) Escardo-Oliva's countable
-- product of selection functions (2010).
--
-- References.
--
--    S. Berardi, M. Bezem, and T. Coquand.  On the Computational
--    Content of the Axiom of Choice.  J. Symbolic Logic, Volume 63,
--    Issue 2 (1998), 600-622.
--
--    U. Berger and P. Oliva. Modified bar recursion.  Mathematical
--    Structures in Computer Science, 16(2):163-183, 2006
--
--    U. Berger and P.Oliva. Modified bar recursion and classical
--    dependent choice. Lecture Notes in Logic, 20:89-107, 2005
--
--    M. Escardo and P. Oliva.  Selection functions, bar recursion,
--    and backward induction.  Mathematical Structures in Computer
--    Science, Volume 20, Issue 2, 2010, Cambridge University Press.
--
--    M. Escardo and P. Oliva.  The Peirce translation and the double
--    negation shift. CiE 2010, Springer LNCS.
--
--    M. Escardo and P. Oliva.  What Sequential Games, the Tychonoff
--    Theorem and the Double-Negation Shift have in Common. ACM
--    SIGPLAN MSFP 2010.
--
-----------------------------------------------------------------------
-- Navigate the automatically generated html version of this set of
-- files by clicking at any word or symbol, to be taken to where it is
-- defined.
-----------------------------------------------------------------------


open import InfinitePigeon.Addition
open import InfinitePigeon.Cantor
open import InfinitePigeon.Equality
open import InfinitePigeon.JK-LogicalFacts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.K-AC-N
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals
open import InfinitePigeon.Order
open import InfinitePigeon.Two


Pigeonhole : {R : Ω} → ₂ℕ → Ω
Pigeonhole {R} α =
   ∃ \(b : ₂) → ∃ \(g : ℕ → ℕ) →
   ∀(i : ℕ) → g i < g(i + 1) ∧ K {R} (α(g i) ≡ b)


pigeonhole : {R : Ω} →
----------

    ∀(α : ₂ℕ) → K(Pigeonhole α)

pigeonhole {R} α = K-∨-elim case₀ case₁ K-Excluded-Middle
 where
  A : Ω
  A = K∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i) ≡ ₀)

  case₀ : A → K(Pigeonhole α)
  case₀ a = K-functor lemma₁ a
   where
    lemma₁ : (∃ \(n : ℕ) → ∀(i : ℕ) → K(α(n + i) ≡ ₀)) → Pigeonhole α
    lemma₁ (∃-intro n h) =
            ∃-intro ₀ (∃-intro (λ i → n + i)
                                λ i → (∧-intro (less-proof 0) (h i)))

  case₁ : (A → R) → K(Pigeonhole α)
  case₁ assumption =  K-functor lemma₇ lemma₆
   where
    lemma₂ : ∀(n : ℕ) → (∀(i : ℕ) → K(α(n + i) ≡ ₀)) → R
    lemma₂ = not-exists-implies-forall-not(three-negations-imply-one assumption)

    lemma₃ : ∀(n : ℕ) → K∃ \(i : ℕ) → K(α(n + i) ≡ ₁)
    lemma₃ = lemma₄ lemma₂
     where
      lemma₄ : (∀(n : ℕ) → (∀(i : ℕ) → K(α(n + i) ≡ ₀)) → R) →
               (∀(n : ℕ) → K∃ \(i : ℕ) → K(α(n + i) ≡ ₁))
      lemma₄ h n = K-functor lemma₅ (not-forall-not-implies-K-exists(h n))
       where
        lemma₅ : (∃ \(i : ℕ) → α(n + i) ≡ ₀ → R) → ∃ \(i : ℕ) → K(α(n + i) ≡ ₁)
        lemma₅ (∃-intro i r) = (∃-intro i (two-equality-cases (α(n + i)) r))

    lemma₆ : K∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n) ≡ ₁)
    lemma₆ = K-AC-ℕ efqs lemma₃
     where efqs : ∀(n : ℕ) → R → ∃ \(i : ℕ) → K(α(n + i) ≡ ₁)
           efqs n r = ∃-intro 0 (λ p → r)

    lemma₇ : (∃ \(f : ℕ → ℕ) → ∀(n : ℕ) → K(α(n + f n) ≡ ₁)) → Pigeonhole α
    lemma₇ (∃-intro f h) =
            ∃-intro ₁ (∃-intro g λ i → (∧-intro (fact₀ i) (fact₁ i)))
     where
      g : ℕ → ℕ
      g 0 = 0 + f 0
      g(succ i) = let j = g i + 1 in  j + f j

      fact₀ : ∀(i : ℕ) → g i < g(i + 1)
      fact₀ i = let n = f(g i + 1)
                in ∃-intro n (trivial-addition-rearrangement (g i) n 1)


      fact₁ : ∀(i : ℕ) → K(α(g i) ≡ ₁)
      fact₁ 0 = h 0
      fact₁ (succ i) = h(g i + 1)
