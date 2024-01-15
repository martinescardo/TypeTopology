-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --without-K --no-termination-check #-}

-- Termination is proved externally, using bar induction and
-- continuity in the case of this module (Escardo-Oliva 2010).

module InfinitePigeon.J-Shift-Selection where

open import InfinitePigeon.Finite-JK-Shifts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals

-- Definition given by Escardo and Oliva MSCS2010
-- (infinite iteration of the J-∧-shift'):


J-∀-shift-selection : {R : Ω} {A : ℕ → Ω} →
-------------------

            (∀(n : ℕ) → J {R} (A n)) → J {R} (∀(n : ℕ) → A n)

J-∀-shift-selection εs =
  J-∧-shift'(∧-intro (head εs) (J-∀-shift-selection(tail εs)))



-- That's it. What follows is for information only.



-- This is one of definitions given in both LICS2007 and LMCS2008
-- (Section 8.1, called Π):


prod : {R : Ω} {A : ℕ → Ω} →
----
       (∀ (n : ℕ) → J {R} (A n)) → J {R} (∀ (n : ℕ) → A n)

prod {R} {A} εs p = cons (∧-intro a₀ ((prod {R} (tail εs)) (prefix a₀ p)))
 where a₀ : A O
       a₀ = head εs (λ a → prefix a p ((prod {R} (tail εs))(prefix a p)))


-- It is equivalent after we expand the definitions (both satisfy the
-- same recursive equation in normal form).
