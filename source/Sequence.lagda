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

head : ∀ {U} {X : ℕ → U ̇} → ((n : ℕ) → X n) → X 0
head α = α 0

tail : ∀ {U} {X : ℕ → U ̇} → ((n : ℕ) → X n) → ((n : ℕ) → X(succ n))
tail α n = α(succ n)

head-tail-eta : ∀ {U} {X : ℕ → U ̇} {α : (n : ℕ) → X n} → (head α ∶∶ tail α) ≡ α
head-tail-eta {U} {X} = dfunext (fe U₀ U) lemma
 where
  lemma : {α : (n : ℕ) → X n} → (i : ℕ) → (head α ∶∶ tail α) i ≡ α i
  lemma 0 = refl
  lemma (succ i) = refl

private cons : ∀ {U} {X : ℕ → U ̇} → X 0 × ((n : ℕ) → X(succ n)) → ((n : ℕ) → X n)
cons(x , α) = x ∶∶ α

cons-retraction : ∀ {U} {X : ℕ → U ̇} → retraction(cons {U} {X})
cons-retraction α = (head α , tail α) , head-tail-eta

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
                  P = (head, tail)


  head (f x) = h x
  tail (f x) = f(t x)

Or equivalentaily

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

 seq-corec-head : head ∘ f ∼ h
 seq-corec-head x = refl

 seq-corec-tail : tail ∘ f ∼ f ∘ t
 seq-corec-tail x = dfunext (fe U₀ U) (λ n → refl)

 seq-final : Σ! \(f : X → (ℕ → A)) → (head ∘ f ∼ h) × (tail ∘ f ∼ f ∘ t)
 seq-final = (seq-corec , seq-corec-head , seq-corec-tail) , c
  where
   c : (f f' : X → ℕ → A) →
         (head ∘ f ∼ h) × (tail ∘ f ∼ f ∘ t) →
         (head ∘ f' ∼ h) × (tail ∘ f' ∼ f' ∘ t) → f ≡ f'
   c f f' (a , b) (c , d) = dfunext (fe V U) (λ x → dfunext (fe U₀ U) (r x))
    where
     r : (x : X) (n : ℕ) → f x n ≡ f' x n
     r x zero = a x ∙ (c x)⁻¹
     r x (succ n) = f x (succ n) ≡⟨ ap (λ - → - n) (b x) ⟩
                    f (t x) n    ≡⟨ r (t x) n ⟩
                    f' (t x) n   ≡⟨ ( ap (λ - → - n) (d x)) ⁻¹ ⟩
                    f' x (succ n) ∎

 \end{code}

Added 11th September 2018.

\begin{code}

seq-bisimulation : ∀ {U V} {A : U ̇} → ((ℕ → A) → (ℕ → A) → V ̇) → U ⊔ V ̇
seq-bisimulation {U} {V} {A} R = (α β : ℕ → A) → R α β
                                                 → (head α ≡ head β)
                                                 × R (tail α) (tail β)

seq-coinduction : ∀ {U V} {A : U ̇} (R : (ℕ → A) → (ℕ → A) → V ̇)
                → seq-bisimulation R → (α β : ℕ → A) → R α β → α ≡ β
seq-coinduction {U} {V} {A} R b α β r = dfunext (fe U₀ U) (h α β r)
 where
  h : (α β : ℕ → A) → R α β → α ∼ β
  h α β r zero = pr₁ (b α β r)
  h α β r (succ n) = h (tail α) (tail β) (pr₂ (b α β r)) n

\end{code}
