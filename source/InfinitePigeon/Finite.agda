-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.Finite where

open import InfinitePigeon.Equality
open import InfinitePigeon.Finite-JK-Shifts
open import InfinitePigeon.JK-Monads
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals


data smaller : ℕ → Set where
  fzero : {n : ℕ} → smaller(succ n)
  fsucc : {n : ℕ} → smaller n → smaller(succ n)


embed : {n : ℕ} → smaller n → ℕ
embed {O} ()
embed {succ n} fzero = O
embed {succ n} (fsucc i) = succ(embed i)


restriction : {m : ℕ} {X : Set} → (ℕ → X) → smaller m → X
restriction f = f ∘ embed


coerce : {n : ℕ} → smaller n → smaller(succ n)
coerce {O} ()
coerce {succ n} (fzero) = fzero
coerce {succ n} (fsucc i) = fsucc(coerce i)


-- In summary, embed i ≡ embed (coerce i).

embed-coerce-lemma : {n : ℕ} → {i : smaller n} →

   embed {n} i ≡ embed {succ n} (coerce {n} i)

embed-coerce-lemma {O} {()}
embed-coerce-lemma {succ n} {fzero} = reflexivity
embed-coerce-lemma {succ n} {fsucc i} = lemma₄
  where induction-hypothesis : embed {n} i ≡ embed {succ n} (coerce {n} i)
        induction-hypothesis = embed-coerce-lemma {n} {i}

        lemma₀ : embed {succ n} (fsucc i) ≡ succ(embed {n} i)
        lemma₀ = reflexivity

        lemma₁ : succ(embed {n} i) ≡ succ(embed{succ n} (coerce {n} i))
        lemma₁ = compositionality succ induction-hypothesis

        lemma₂ : embed {succ n} (fsucc i) ≡ succ(embed{succ n} (coerce {n} i))
        lemma₂ = transitivity lemma₀ lemma₁

        lemma₃ :   succ(embed{succ n} (coerce {n} i))
                 ≡ embed{succ(succ n)} (coerce {succ n} (fsucc i))
        lemma₃ = reflexivity

        lemma₄ :   embed {succ n} (fsucc i)
                 ≡ embed{succ(succ n)} (coerce {succ n} (fsucc i))
        lemma₄ = transitivity lemma₂ lemma₃


fmin : (m : ℕ) → ℕ → smaller(succ m)

fmin O n = fzero
fmin (succ m)  0 = fzero
fmin (succ m) (succ n) = fsucc(fmin m n)



-- The following mimicks the definition of the infinite shifts
-- (in the modules Naturals.agda and J-Shift-Selection.agda):


fhead : {m : ℕ} {A : smaller(succ m) → Ω} →
-----
       (∀(n : smaller(succ m)) → A n) → A fzero

fhead α = α fzero


ftail : {m : ℕ} {A : smaller(succ m) → Ω} →
-----
       (∀(n : smaller(succ m)) → A n) → ∀(n : smaller m) → A(fsucc n)

ftail α n = α(fsucc n)



fcons : {m : ℕ} {A : smaller(succ m) → Ω} →
-----
       A fzero ∧ (∀(n : smaller m) → A(fsucc n)) → ∀(n : smaller(succ m)) → A n

fcons (∧-intro a α) fzero = a
fcons (∧-intro a α) (fsucc n) = α n


fK-∧-shift' : {R : Ω} {m : ℕ} {A : smaller(succ m) → Ω} →
----------
             K(A fzero) ∧ K(∀(n : smaller m) → A(fsucc n)) →
             K(∀(n : smaller(succ m)) → A n)

fK-∧-shift' {R} = (K-functor {R} fcons) ∘ K-∧-shift


fK-∀-shift : {m : ℕ} {R : Ω} {A : smaller m → Ω} →
----------
             (∀(n : smaller m) → K {R} (A n)) →
       K {R} (∀(n : smaller m) → A n)

fK-∀-shift  {O} φs = λ p → p λ()
fK-∀-shift {succ m}  φs =
 fK-∧-shift' (∧-intro (fhead φs) (fK-∀-shift (ftail φs)))


-- This is used for Berger's modified bar recursion.


override : {X : ℕ → Set} → {m : ℕ} →

 (s : (i : smaller m) → X(embed i)) →
 ((n : ℕ) → X n) → ((n : ℕ) → X n)

override {X} {m} s α n = less-cases {X} m n s (α n)
 where
  less-cases : {X : ℕ → Set} → (m n : ℕ) →
   (s : (i : smaller m) → X(embed i)) → X n → X n

  less-cases 0 n s a = a
  less-cases (succ m) 0 s a = s fzero
  less-cases {X} (succ m) (succ n) s a
   = less-cases {λ n → X(succ n)} m n (ftail s) a


append : {X : ℕ → Set} → {m : ℕ} →
 ((i : smaller m) → X(embed i)) → X m → (i : smaller(succ m)) → X(embed i)

append {X} {0} s x fzero = x
append {X} {0} s x (fsucc ())
append {X} {succ m} s x fzero = s fzero
append {X} {succ m} s x (fsucc i)
 = append {λ n → X(succ n)} {m} (ftail s) x i
