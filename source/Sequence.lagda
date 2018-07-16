Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module Sequence (fe : ∀ U V → funext U V) where

open import SpartanMLTT hiding (_+_)
open import UF-Retracts
open import NaturalsAddition

_∶∶_ : ∀ {U} {X : ℕ → U ̇} → X 0 → ((n : ℕ) → X(succ n)) → ((n : ℕ) → X n)
(x ∶∶ α) 0 = x
(x ∶∶ α) (succ n) = α n

hd : ∀ {U} {X : ℕ → U ̇} → ((n : ℕ) → X n) → X 0
hd α = α 0

tl : ∀ {U} {X : ℕ → U ̇} → ((n : ℕ) → X n) → ((n : ℕ) → X(succ n))
tl α n = α(succ n)

hd-tl-eta : ∀ {U} {X : ℕ → U ̇} {α : (n : ℕ) → X n} → (hd α ∶∶ tl α) ≡ α
hd-tl-eta {U} {X} = dfunext (fe U₀ U) lemma
 where
  lemma : {α : (n : ℕ) → X n} → (i : ℕ) → (hd α ∶∶ tl α) i ≡ α i
  lemma 0 = refl
  lemma (succ i) = refl

private cons : ∀ {U} {X : ℕ → U ̇} → X 0 × ((n : ℕ) → X(succ n)) → ((n : ℕ) → X n)
cons(x , α) = x ∶∶ α

cons-retraction : ∀ {U} {X : ℕ → U ̇} → retraction(cons {U} {X})
cons-retraction α = (hd α , tl α) , hd-tl-eta

\end{code}

(In fact it is an equivalence, but I won't bother, until this is
needed.)

\begin{code}

itail : ∀ {U} {X : ℕ → U ̇} → (n : ℕ) → ((i : ℕ) → X i) → ((i : ℕ) → X(i + n))
itail n α i = α(i + n)

\end{code}

Added 16th July 2018. Corecursion on sequences A : ℕ → .

                    p = (h,t)
             X ------------------> A × X
             |                       |
             |                       |
          f  |                       | A × f
             |                       |
             |                       |
             v                       v
         (ℕ → A) ---------------> A × (ℕ → A)
                  P = (hd, tl)


  head (f x) = h x
  tail (f x) = f(t x)

Or equivalently

  f x = cons (h x) (f (t x))

Todo: replace Σ! ... by is-singleton(Σ ...).

\begin{code}

module _ {U V : Universe}
         {A : U ̇}
         {X : V ̇}
         (h : X → A)
         (t : X → X)
       where

 private f : X → (ℕ → A)
 f x zero = h x
 f x (succ n) = f (t x) n

 seq-corec = f

 seq-corec-hd : hd ∘ f ∼ h
 seq-corec-hd x = refl

 seq-corec-tl : tl ∘ f ∼ f ∘ t
 seq-corec-tl x = dfunext (fe U₀ U) (λ n → refl)

 seq-final : Σ! \(f : X → (ℕ → A)) → (hd ∘ f ∼ h) × (tl ∘ f ∼ f ∘ t)
 seq-final = (seq-corec , seq-corec-hd , seq-corec-tl) , c
  where
   c : (f f' : X → ℕ → A) →
         (hd ∘ f ∼ h) × (tl ∘ f ∼ f ∘ t) →
         (hd ∘ f' ∼ h) × (tl ∘ f' ∼ f' ∘ t) → f ≡ f'
   c f f' (a , b) (c , d) = dfunext (fe V U) (λ x → dfunext (fe U₀ U) (r x))
    where
     r : (x : X) (n : ℕ) → f x n ≡ f' x n
     r x zero = a x ∙ (c x)⁻¹
     r x (succ n) = f x (succ n) ≡⟨ ap (λ - → - n) (b x) ⟩
                    f (t x) n    ≡⟨ r (t x) n ⟩
                    f' (t x) n   ≡⟨ ( ap (λ - → - n) (d x)) ⁻¹ ⟩
                    f' x (succ n) ∎

 \end{code}
