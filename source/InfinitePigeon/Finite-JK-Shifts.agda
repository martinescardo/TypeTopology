-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.Finite-JK-Shifts where

open import InfinitePigeon.Equality
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts

J-∧-shift : {R A₀ A₁ : Ω} →
---------
            J A₀ ∧ J A₁ → J(A₀ ∧ A₁)

J-∧-shift {R} (∧-intro ε₀ ε₁) =
 J-extend {R} (λ a₀ → J-strength (∧-intro a₀ ε₁))(ε₀)


-- This was defined in the following alternative way in Escardo's
-- LICS2007 and LMCS2008 papers:

J-∧-shift-lics : {R A₀ A₁ : Ω} →
--------------
                 J A₀ ∧ J A₁ → J(A₀ ∧ A₁)

J-∧-shift-lics {R} {A₀} {A₁} (∧-intro ε₀ ε₁) r = ∧-intro a₀ a₁
            where a₀ : A₀
                  a₀ = ε₀(λ x₀ → J-K {R} ε₁ (λ x₁ → r (∧-intro x₀ x₁)))
                  a₁ : A₁
                  a₁ = ε₁ (λ x₁ → r (∧-intro a₀ x₁))


observation₁ : {R A₀ A₁ : Ω} →
------------
               (ε₀ : J {R} A₀) → (ε₁ : J A₁) → (r : (A₀ ∧ A₁ → R)) →

               J-∧-shift (∧-intro ε₀ ε₁) r ≡ J-∧-shift-lics (∧-intro ε₀ ε₁) r

observation₁ ε₀ ε₁ r = reflexivity


K-∧-shift : {R A₀ A₁ : Ω} →
---------
            K A₀ ∧ K A₁ → K(A₀ ∧ A₁)

K-∧-shift {R} (∧-intro φ₀ φ₁) =
 K-extend {R} (λ a₀ → K-strength (∧-intro a₀ φ₁))(φ₀)


observation₂ : {R A₀ A₁ : Ω} →
------------
          (φ₀ : K {R} A₀) → (φ₁ : K A₁) → (r : (A₀ ∧ A₁ → R)) →

          K-∧-shift (∧-intro φ₀ φ₁) r ≡ φ₀(λ a₀ → φ₁(λ a₁ → r (∧-intro a₀ a₁)))

observation₂ φ₀ φ₁ r = reflexivity


observation₃ : {R A₀ A₁ : Ω} →
------------
         (ε₀ : J {R} A₀) → (ε₁ : J A₁) →

         J-K(J-∧-shift (∧-intro ε₀ ε₁)) ≡ K-∧-shift (∧-intro (J-K ε₀) (J-K ε₁))

observation₃ ε₀ ε₁ = reflexivity


-- Preliminary lemmas for the countable shifts (in another module).
-- The following definitions are the same with a parameter J/K.

open import InfinitePigeon.Naturals


J-∧-shift' : {R : Ω} {A : ℕ → Ω} →
----------
           J(A O) ∧ J(∀(n : ℕ) → A(succ n)) → J(∀(n : ℕ) → A n)

J-∧-shift' {R} = (J-functor {R} cons) ∘ J-∧-shift



K-∧-shift' : {R : Ω} {A : ℕ → Ω} →
----------
           K(A O) ∧ K(∀(n : ℕ) → A(succ n)) → K(∀(n : ℕ) → A n)

K-∧-shift' {R} = (K-functor {R}  cons) ∘ K-∧-shift
