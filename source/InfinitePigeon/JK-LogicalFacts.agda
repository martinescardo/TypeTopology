-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.JK-LogicalFacts where

open import InfinitePigeon.Equality
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Two

-- Classical existential quantifier:

K∃ : {R : Ω} → {X : Set} → (A : X → Ω) → Ω
K∃ {R} {X} A = K {R} (∃ {X} A)


-- Another one (which is not fully investigated here):

J∃ : {R : Ω} → {X : Set} → (A : X → Ω) → Ω
J∃ {R} {X} A = J {R} (∃ {X} A)


-- K∃ is really the classical existential quantifier:


K-exists-implies-not-forall-not : {R : Ω} → {X : Set} → {A : X → Ω} →

 (K∃ \(x : X) → A x)  →  (∀(x : X) → A x → R) → R

K-exists-implies-not-forall-not = contra-positive forall-not-implies-not-exists


not-forall-not-implies-K-exists : {R : Ω} → {X : Set} → {A : X → Ω} →

 ((∀(x : X) → A x → R) → R)  →  K∃ \(x : X) → A x

not-forall-not-implies-K-exists = contra-positive not-exists-implies-forall-not

 where NB-special-case : {R : Ω} → {X : Set} → {A : X → Ω} →

        ((∀(x : X) → K(A x)) → R)  →  K∃ \(x : X) → A x → R

       NB-special-case = not-forall-not-implies-K-exists


K-∃-shift : {R : Ω} {X : Set} {A : X → Ω} →

  (∃ \(x : X) → K(A x)) → K∃ \(x : X) → A x

K-∃-shift {R} (∃-intro x φ) = K-functor {R} (∃-intro x) φ


J-Excluded-Middle : {R A : Ω} →

                     J {R } (A ∨ (A → R))

J-Excluded-Middle = λ p → ∨-intro₁(λ a → p (∨-intro₀ a))


K-Excluded-Middle : {R A : Ω} →

                    K {R} (A ∨ (A → R))

K-Excluded-Middle = J-K(J-Excluded-Middle)


J-∨-elim : {R A₀ A₁ B : Ω} → (A₀ → J B) → (A₁ → J B) → J(A₀ ∨ A₁) → J B

J-∨-elim {R} case₀ case₁ = J-extend {R} (∨-elim case₀ case₁)


K-∨-elim : {R A₀ A₁ B : Ω} → (A₀ → K B) → (A₁ → K B) → K(A₀ ∨ A₁) → K B

K-∨-elim {R} case₀ case₁ = K-extend {R} (∨-elim case₀ case₁)

-- call/cc is Peirce's Law:

PeircesLaw : {R A : Ω} → J(K A) → K A
PeircesLaw {R} = μK {R} ∘ J-K


not-1-must-be-0 : {R : Ω} →

 ∀(b : ₂) → K(b ≡ ₁ → R) → K(b ≡ ₀)

not-1-must-be-0 b = contra-positive (two-equality-cases b)
