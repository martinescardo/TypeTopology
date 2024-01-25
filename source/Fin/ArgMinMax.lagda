Martin Escardo and Paulo Oliva, October 2021.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.ArgMinMax where

open import UF.Subsingletons

open import Fin.Embeddings
open import Fin.Order
open import Fin.Properties
open import Fin.Topology
open import Fin.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.SpartanList
open import Naturals.Order
open import Notation.Order
open import NotionsOfDecidability.Complemented
open import TypeTopology.CompactTypes
open import UF.DiscreteAndSeparated
open import UF.Equiv

\end{code}

Every inhabited detachable "subset" of Fin n has a least and a
greatest element.

\begin{code}

Fin-wf : {n : ℕ} (A : Fin n → 𝓤  ̇ ) (r₀ : Fin n)
       → is-complemented A
       → A r₀
       → Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → r ≤ s)
Fin-wf {𝓤} {succ n} A 𝟎 d a = 𝟎 , a , λ s a' → ⟨⟩
Fin-wf {𝓤} {succ n} A (suc r₀) d a = γ
 where
  IH : Σ r ꞉ Fin n , A (suc r) × ((s : Fin n) → A (suc s) → r ≤ s)
  IH = Fin-wf {𝓤} {n} (λ x → A (suc x)) r₀ (λ x → d (suc x)) a

  r : Fin n
  r = pr₁ IH

  b : A (suc r)
  b = pr₁ (pr₂ IH)

  c : (s : Fin n) → A (suc s) → r ≤ s
  c = pr₂ (pr₂ IH)

  l : ¬ A 𝟎 → (s : Fin (succ n)) → A s → suc r ≤ s
  l ν 𝟎 a       = 𝟘-elim (ν a)
  l ν (suc x) a = c x a

  γ : Σ r ꞉ Fin (succ n) , A r × ((s : Fin (succ n)) → A s → r ≤ s)
  γ = Cases (d 𝟎)
       (λ a₀ → 𝟎 , a₀ , λ s a' → ⟨⟩)
       (λ (ν : ¬ A 𝟎) → suc r , b , l ν)

Fin-co-wf : {n : ℕ} (A : Fin n → 𝓤  ̇ ) (r₀ : Fin n)
          → is-complemented A
          → A r₀
          → Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → s ≤ r)
Fin-co-wf {𝓤} {succ n} A 𝟎 d a = γ
 where
  δ : is-decidable (Σ i ꞉ Fin n , A (suc i))
  δ = Fin-Compact (A ∘ suc) (d ∘ suc)

  Γ = Σ r ꞉ Fin (succ n) , A r × ((s : Fin (succ n)) → A s → s ≤ r)

  γ : Γ
  γ = Cases δ f g
   where
    f : Σ i ꞉ Fin n , A (suc i) → Γ
    f (i , b) = suc r' , a' , h
     where
      IH : Σ r' ꞉ Fin n , A (suc r') × ((s' : Fin n) → A (suc s') → s' ≤ r')
      IH = Fin-co-wf {𝓤} {n} (A ∘ suc) i (d ∘ suc) b

      r' : Fin n
      r' = pr₁ IH

      a' : A (suc r')
      a' = pr₁ (pr₂ IH)

      ϕ : (s' : Fin n) → A (suc s') → s' ≤ r'
      ϕ = pr₂ (pr₂ IH)

      h : (s : Fin (succ n)) → A s → s ≤ suc r'
      h 𝟎       c = ⋆
      h (suc x) c = ϕ x c

    g : ¬ (Σ i ꞉ Fin n , A (suc i)) → Γ
    g ν = 𝟎 , a , h
     where
      h : (s : Fin (succ n)) → A s → s ≤ 𝟎
      h (suc x) c = 𝟘-elim (ν (x , c))
      h 𝟎       c = ⋆

Fin-co-wf {𝓤} {succ n} A (suc x) d a = suc (pr₁ IH) , pr₁ (pr₂ IH) , h
 where
  IH : Σ r ꞉ Fin n , A (suc r) × ((s : Fin n) → A (suc s) → s ≤ r)
  IH = Fin-co-wf {𝓤} {n} (A ∘ suc) x  (d ∘ suc) a

  h : (s : Fin (succ n)) → A s → s ≤ suc (pr₁ IH)
  h 𝟎       b = ⋆
  h (suc x) b = pr₂ (pr₂ IH) x b

compact-argmax : {X : 𝓤  ̇ } {n : ℕ } (p : X → Fin n)
               → is-Compact X
               → X
               → Σ x ꞉ X , ((y : X) → p y ≤ p x)
compact-argmax {𝓤} {X} {n} p κ x₀ = II I
 where
  A : Fin n → 𝓤  ̇
  A r = Σ x ꞉ X , p x ＝ r

  a₀ : A (p x₀)
  a₀ = x₀ , refl

  δ : is-complemented A
  δ r = κ (λ x → p x ＝ r) (λ x → Fin-is-discrete (p x) r)

  I : Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → s ≤ r)
  I = Fin-co-wf A (p x₀) δ a₀

  II : type-of I → Σ x ꞉ X , ((y : X) → p y ≤ p x)
  II (.(p y) , ((y , refl) , ϕ)) = y , (λ y → ϕ (p y) (y , refl))

compact-argmin : {X : 𝓤  ̇ } {n : ℕ } (p : X → Fin n)
               → is-Compact X
               → X
               → Σ x ꞉ X , ((y : X) → p x ≤ p y)
compact-argmin {𝓤} {X} {n} p κ x₀ = II I
 where
  A : Fin n → 𝓤  ̇
  A r = Σ x ꞉ X , p x ＝ r

  a₀ : A (p x₀)
  a₀ = x₀ , refl

  δ : is-complemented A
  δ r = κ (λ x → p x ＝ r) (λ x → Fin-is-discrete (p x) r)

  I : Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → r ≤ s)
  I = Fin-wf A (p x₀) δ a₀

  II : type-of I → Σ x ꞉ X , ((y : X) → p x ≤ p y)
  II (.(p y) , ((y , refl) , ϕ)) = y , (λ y → ϕ (p y) (y , refl))

Fin-argmin : {a r : ℕ} (p : Fin (succ a) → Fin r)
           → Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p x ≤ p y)
Fin-argmin {0} p = 𝟎 , α
 where
  α : (y : Fin 1) → p 𝟎 ≤ p y
  α 𝟎 = ≤-refl ⟦ p 𝟎 ⟧
Fin-argmin {succ a} p = γ
 where
  IH : Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p (suc x) ≤ p (suc y))
  IH = Fin-argmin {a} (p ∘ suc)

  x = pr₁ IH
  ϕ = pr₂ IH

  γ : Σ x' ꞉ Fin (succ (succ a)) , ((y : Fin (succ (succ a))) → p x' ≤ p y)
  γ = h (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧)
   where
    h : is-decidable (p 𝟎 ≤ p (suc x)) → type-of γ
    h (inl l) = 𝟎 , α
     where
      α : (y : (Fin (succ (succ a)))) → p 𝟎 ≤ p y
      α 𝟎       = ≤-refl ⟦ p 𝟎 ⟧
      α (suc y) = ≤-trans ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧ ⟦ p (suc y) ⟧ l (ϕ y)
    h (inr ν) = suc x , α
     where
      α : (y : (Fin (succ (succ a)))) → p (suc x) ≤ p y
      α 𝟎       = not-less-bigger-or-equal ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧
                   (contrapositive (<-coarser-than-≤ ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧) ν)
      α (suc y) = ϕ y

argmin : {a r : ℕ} → (Fin (succ a) → Fin r) → Fin (succ a)
argmin p = pr₁ (Fin-argmin p)

argmin-correct : {a r : ℕ} (p : Fin (succ a) → Fin r)
               → (y : Fin (succ a)) → p (argmin p) ≤ p y
argmin-correct p = pr₂ (Fin-argmin p)

Fin-argmax : {a r : ℕ} (p : Fin (succ a) → Fin r)
           → Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p y ≤ p x)
Fin-argmax {0} p = 𝟎 , α
 where
  α : (y : Fin 1) → p y ≤ p 𝟎
  α 𝟎 = ≤-refl ⟦ p 𝟎 ⟧
Fin-argmax {succ a} p = γ
 where
  IH : Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p (suc y) ≤ p (suc x))
  IH = Fin-argmax {a} (p ∘ suc)

  x = pr₁ IH
  ϕ = pr₂ IH

  γ : Σ x' ꞉ Fin (succ (succ a)) , ((y : Fin (succ (succ a))) → p y ≤ p x')
  γ = h (≤-decidable ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧)
   where
    h : is-decidable (p (suc x) ≤ p 𝟎) → type-of γ
    h (inl l) = 𝟎 , α
     where
      α : (y : (Fin (succ (succ a)))) → p y ≤ p 𝟎
      α 𝟎       = ≤-refl ⟦ p 𝟎 ⟧
      α (suc y) = ≤-trans ⟦ p (suc y) ⟧ ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧ (ϕ y) l
    h (inr ν) = suc x , α
     where
      α : (y : (Fin (succ (succ a)))) → p y ≤ p (suc x)
      α 𝟎       = not-less-bigger-or-equal ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧
                   (contrapositive (<-coarser-than-≤ ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧) ν)
      α (suc y) = ϕ y

\end{code}

We could define argmin and argmax independently of their
specification, and then prove their specification:

\begin{code}

argmin' : {a r : ℕ} → (Fin (succ a) → Fin r) → Fin (succ a)
argmin' {0}      p = 𝟎
argmin' {succ a} p = γ
 where
  m : Fin (succ a)
  m = argmin' {a} (p ∘ suc)

  γ : Fin (succ (succ a))
  γ = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
       (λ (l : p 𝟎 ≤ p (suc m)) → 𝟎)
       (λ otherwise → suc m)

argmax' : {a r : ℕ} → (Fin (succ a) → Fin r) → Fin (succ a)
argmax' {0}      p = 𝟎
argmax' {succ a} p = γ
 where
  m : Fin (succ a)
  m = argmax' {a} (p ∘ suc)

  γ : Fin (succ (succ a))
  γ = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
       (λ (l : p 𝟎 ≤ p (suc m)) → suc m)
       (λ otherwise → 𝟎)

{-
argmax'-correct : {a r : ℕ} (p : Fin (succ a) → Fin r)
               → ((y : Fin (succ a)) → p y ≤ p (argmax p))
argmax'-correct {0}      p 𝟎 = ≤-refl ⟦ p 𝟎 ⟧
argmax'-correct {succ a} p y = h y
 where
  m : Fin (succ a)
  m = argmax {a} (p ∘ suc)

  IH : (y : Fin (succ a)) → p (suc y) ≤ p (suc m)
  IH = argmax-correct {a} (p ∘ suc)

  γ : Fin (succ (succ a))
  γ = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
       (λ (l : ⟦ p 𝟎 ⟧ ≤ ⟦ p (suc m) ⟧) → suc m)
       (λ otherwise → 𝟎)

  γ₀ : p 𝟎 ≤ p (suc m) → γ ＝ suc m
  γ₀ = {!!}

  γ₁ : ¬ (p 𝟎 ≤ p (suc m)) → γ ＝ 𝟎
  γ₁ = {!!}


  h : (y : Fin (succ (succ a))) → p y ≤ p γ
  h 𝟎 = l
   where
    l : p 𝟎 ≤ p γ
    l = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
         (λ (l : p 𝟎 ≤ p (suc m)) → transport (λ - → p 𝟎 ≤ p -) ((γ₀ l)⁻¹) l)
         (λ otherwise → {!!})
  h (suc x) = l
   where
    l : p (suc x) ≤ p γ
    l = {!!}
-}
\end{code}
