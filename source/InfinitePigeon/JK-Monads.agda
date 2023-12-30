-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.JK-Monads where

open import InfinitePigeon.Equality
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts


-----------------------------------------------
--                                           --
-- The selection and continuation monads.    --
--                                           --
-----------------------------------------------

J : {R : Ω} → Ω → Ω
J {R} A = (A → R) → A

K : {R : Ω} → Ω → Ω
K {R} A = (A → R) → R


-- The monads we'll consider are, for a parameter R fixed in
-- advance, or passed around,
--
--      T A = J R A,
-- and
--      T A = K R A.
--

-- This will be a monad morphism:

J-K :  {R A : Ω} →
---
       J {R} A → K A

J-K ε p = p(ε p)


-- Under a (necessary) hypothesis, the following goes in the direction
-- opposite to J-K, but is not a morphism.  (Preservation of the unit
-- fails.)


K-J :  {R A : Ω} →
---
       (R → A) →     -- efq (ex falso quodlibet)
       K A → J A

K-J efq φ = efq ∘ φ


-- Notational conventions:
--
--   +-------------+---------------------+
--   |   proofs of |  are ranged over by |
--   +-------------+---------------------+
--   |     J R A   |    ε                |
--   |     K R A   |    φ                |
--   |     A→R     |    p                |
--   +-------------+---------------------+
--
-- For variables ranging over sequences,
-- we append the suffix "s".


J-functor : {R A B : Ω} →
---------
            (A → B) → J {R} A → J B

J-functor f ε = λ q → f(ε(q ∘ f))



K-functor : {R A B : Ω} →
---------
            (A → B) → K {R} A → K B

K-functor f φ = λ q → φ(q ∘ f)



------------
--        --
-- Units  --
--        --
------------


ηJ : {R A : Ω} →
--
     A → J {R} A

ηJ a = λ p → a


ηK : {R A : Ω} →
--
     A → K {R} A

ηK a = λ p → p a


-----------------------
--                   --
--  Multiplications  --
--                   --
-----------------------


μJ : {R A : Ω} →
--
     J(J A) → J A

μJ {R} E = λ p → E (λ ε → J-K {R} ε p) p


μK : {R A : Ω} →
--
     K(K A) → K {R} A

μK Φ = λ p → Φ (λ φ → φ p)


----------------------------------------------------------
--                                                      --
--                                                      --
-- Monad laws for J (for K they are well known to hold) --
--                                                      --
----------------------------------------------------------


-- The proofs of the laws are automatic. We just need to write the
-- equations we want to prove. Then agda normalizes each side and sees
-- that they are equal, and accepts our proof "reflexivity".


J-functoriality₀ : {R A : Ω} →
----------------
                   J-functor id ≡ id {J {R} A}

J-functoriality₀ = reflexivity


J-functoriality₁ : {R A B C : Ω} →
----------------
                   (f : (A → B)) → (g : (B → C)) →
                   J-functor {R} (g ∘ f) ≡ (J-functor g) ∘ (J-functor f)

J-functoriality₁ f g = reflexivity


J-η-naturality : {R A B : Ω} →
--------------
                 (f : (A → B)) → (ηJ {R}) ∘ f ≡ (J-functor f) ∘ ηJ

J-η-naturality f = reflexivity


J-μ-naturality : {R A B : Ω} →
--------------
   (f : (A → B)) →
   (μJ {R} {B}) ∘ (J-functor (J-functor f)) ≡ (J-functor f) ∘ (μJ {R})

J-μ-naturality f = reflexivity


J-assoc : {R A : Ω} →
-------
          (μJ {R} {A}) ∘ (J-functor μJ) ≡ μJ ∘ μJ

J-assoc = reflexivity


J-unit₀ : {R A : Ω} →
--------
           μJ ∘ (J-functor ηJ) ≡ id {J {R} A}

J-unit₀ = reflexivity


J-unit₁ : {R A : Ω} →
--------
           μJ ∘ ηJ ≡ id {J {R} A}

J-unit₁ = reflexivity


-- Digression. Verification that J-K is a monad morphism:


J-K-morphism₀ : {R A : Ω} →
-------------
                (J-K {R} {A}) ∘ ηJ ≡ ηK

J-K-morphism₀ = reflexivity


J-K-morphism₁ : {R A : Ω} →
-------------
                (J-K {R} {A}) ∘ μJ ≡ μK ∘ J-K ∘ (J-functor J-K)

J-K-morphism₁ = reflexivity


---------------------------
--                       --
-- Extension operators.  --
--                       --
---------------------------


J-extend : {R A B : Ω} →
--------
           (A → J B) → (J A → J B)

J-extend {R} f = μJ ∘ (J-functor {R} f)


observation-J-extend : {R A B : Ω} →
--------------------
               (f : (A → J {R} B)) → (ε : J A) → (q : (B → R)) →

               J-extend f ε q ≡ f(ε(λ a → q(f a q))) q

observation-J-extend f ε q = reflexivity


K-extend : {R A B : Ω} →
--------
           (A → K B) → (K A → K B)

K-extend {R} f = μK ∘ (K-functor {R} f)


observation-K-extend : {R A B : Ω} →
--------------------
               (f : (A → K B)) → (φ : K A) → (q : (B → R)) →
               K-extend f φ q ≡ φ(λ a → f a q)

observation-K-extend f φ q = reflexivity

-----------------
--             --
-- Strengths.  --
--             --
-----------------


-- Any lambda-defined monad in a cartesian closed category is
-- enriched over the category, and hence is strong. This is why the
-- following two strengths have the same definition, although,
-- concretely, they are given by different lambda definitions
-- (observation-J-strength and observation-K-strength):


J-strength : {R A₀ A₁ : Ω} →
----------
             A₀ ∧ J A₁ → J(A₀ ∧ A₁)

J-strength {R} (∧-intro a₀ ε₁) = J-functor {R} (λ a₁ → ∧-intro a₀ a₁) ε₁


observation-J-strength :  {R A₀ A₁ : Ω}
----------------------
  (a₀ : A₀) → (ε₁ : J {R} A₁) →

  J-strength (∧-intro a₀ ε₁) ≡ λ p → ∧-intro a₀ (ε₁(λ a₁ → p(∧-intro a₀ a₁)))

observation-J-strength a₀ ε₁ = reflexivity


K-strength : {R A₀ A₁ : Ω} →
----------
             A₀ ∧ K A₁ → K(A₀ ∧ A₁)

K-strength {R} (∧-intro a₀ φ₁) = K-functor {R} (λ a₁ → ∧-intro a₀ a₁) φ₁


observation-K-strength :  {R A₀ A₁ : Ω}
----------------------
  (a₀ : A₀) → (φ₁ : K {R} A₁) →

  K-strength (∧-intro a₀ φ₁) ≡ λ p → φ₁(λ a₁ → p(∧-intro a₀ a₁))

observation-K-strength a₀ φ₁ = reflexivity


-- The verification that this is indeed a strength
-- (see http://en.wikipedia.org/wiki/Strong_monad)
-- is not needed.
