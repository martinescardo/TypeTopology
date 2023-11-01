Martin Escardo, 10th Dec 2019.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Order where

open import Fin.Embeddings
open import Fin.Topology
open import Fin.Type
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.Complemented
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

We define the natural order of Fin n by reduction to the natural order
of ℕ so that the canonical embedding Fin n → ℕ is order preserving and
reflecting, using the above isomorphic manifestation of the type Fin n.

\begin{code}

module _ {n : ℕ} where
 instance
  Strict-Order-Fin-Fin : Strict-Order (Fin n) (Fin n)
  _<_ {{Strict-Order-Fin-Fin}} i j = ⟦ i ⟧ < ⟦ j ⟧

  Order-Fin-Fin : Order (Fin n) (Fin n)
  _≤_ {{Order-Fin-Fin}} i j = ⟦ i ⟧ ≤ ⟦ j ⟧

_is-lower-bound-of_ : {n : ℕ} → Fin n → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
i is-lower-bound-of A = ∀ j → A j → i ≤ j


lower-bounds-of : {n : ℕ} → (Fin n → 𝓤 ̇ ) → Fin n → 𝓤 ̇
lower-bounds-of A = λ i → i is-lower-bound-of A


_is-upper-bound-of_ : {n : ℕ} → Fin n → (Fin n → 𝓤 ̇ )  → 𝓤 ̇
i is-upper-bound-of A = ∀ j → A j → j ≤ i


_is-inf-of_ : {n : ℕ} → Fin n → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
i is-inf-of A = i is-lower-bound-of A
              × i is-upper-bound-of (lower-bounds-of A)


inf-is-lb : {n : ℕ} (i : Fin n) (A : Fin n → 𝓤 ̇ )
          → i is-inf-of A → i is-lower-bound-of A

inf-is-lb i A = pr₁


inf-is-ub-of-lbs : {n : ℕ} (i : Fin n) (A : Fin n → 𝓤 ̇ )
                 → i is-inf-of A → i is-upper-bound-of (lower-bounds-of A)

inf-is-ub-of-lbs i A = pr₂


inf-construction : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ )
                 → is-complemented A
                 → Σ i ꞉ Fin (succ n) , i is-inf-of A × (Σ A → A i)

inf-construction {𝓤} {zero} A δ = 𝟎 , (l , m) , ε
 where
  l : 𝟎 is-lower-bound-of A
  l 𝟎       _ = ≤-refl 0
  l (suc i) _ = 𝟘-elim i

  m : (j : Fin 1) → j is-lower-bound-of A → j ≤ 𝟎
  m 𝟎       _ = ≤-refl 0
  m (suc i) _ = 𝟘-elim i

  ε : Σ A → A 𝟎
  ε (𝟎 , a)     = a
  ε (suc i , a) = 𝟘-elim i

inf-construction {𝓤} {succ n} A δ = γ (δ 𝟎)
 where
  IH : Σ i ꞉ Fin (succ n) , i is-inf-of (A ∘ suc) × ((Σ j ꞉ Fin (succ n) , A (suc j)) → A (suc i))
  IH = inf-construction {𝓤} {n} (A ∘ suc) (δ ∘ suc)

  i : Fin (succ n)
  i = pr₁ IH

  l : (j : Fin (succ n)) → A (suc j) → i ≤ j
  l = inf-is-lb i (A ∘ suc) (pr₁ (pr₂ IH))

  u : (j : Fin (succ n)) → ((k : Fin (succ n)) → A (suc k) → j ≤ k) → j ≤ i
  u = inf-is-ub-of-lbs i (A ∘ suc) (pr₁ (pr₂ IH))

  γ : is-decidable (A 𝟎) → Σ i' ꞉ Fin (succ (succ n)) , i' is-inf-of A × (Σ A → A i')
  γ (suc a) = 𝟎 , (φ , ψ) , ε
    where
     φ : (j : Fin (succ (succ n))) → A j → 𝟎 ≤ j
     φ j b = zero-least (⟦_⟧ j)

     ψ : (j : Fin (succ (succ n))) → j is-lower-bound-of A → j ≤ 𝟎
     ψ j l = l 𝟎 a

     ε : Σ A → A 𝟎
     ε _ = a

  γ (inr ν) = suc i , (φ , ψ) , ε
    where
     φ : (j : Fin (succ (succ n))) → A j → suc i ≤ j
     φ 𝟎 a = 𝟘-elim (ν a)
     φ (suc j) a = l j a

     ψ : (j : Fin (succ (succ n))) → j is-lower-bound-of A → j ≤ suc i
     ψ 𝟎 l = zero-least (⟦_⟧ i)
     ψ (suc j) l = u j (l ∘ suc)

     ε : Σ A → A (suc i)
     ε (𝟎 , b)     = 𝟘-elim (ν b)
     ε (suc j , b) = pr₂ (pr₂ IH) (j , b)


inf : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ ) → is-complemented A → Fin (succ n)
inf A δ = pr₁ (inf-construction A δ)


inf-property : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ ) (δ : is-complemented A)
             → (inf A δ) is-inf-of A

inf-property A δ = pr₁ (pr₂ (inf-construction A δ))


inf-is-attained : {n : ℕ} (A : Fin (succ n) → 𝓤 ̇ ) (δ : is-complemented A)
                → Σ A → A (inf A δ)

inf-is-attained A δ = pr₂ (pr₂ (inf-construction A δ))


Σ-min : {n : ℕ} → (Fin n → 𝓤 ̇ ) → 𝓤 ̇
Σ-min {𝓤} {n} A = Σ i ꞉ Fin n , A i × (i is-lower-bound-of A)

Σ-min-gives-Σ : {n : ℕ} (A : Fin n → 𝓤 ̇ )
             → Σ-min A → Σ A

Σ-min-gives-Σ A (i , a , _) = (i , a)


Σ-gives-Σ-min : {n : ℕ} (A : Fin n → 𝓤 ̇ )
              → is-complemented A → Σ A → Σ-min A

Σ-gives-Σ-min {𝓤} {0}      A δ (i , a) = 𝟘-elim i
Σ-gives-Σ-min {𝓤} {succ n} A δ σ       = inf A δ ,
                                        inf-is-attained A δ σ ,
                                        inf-is-lb (inf A δ) A (inf-property A δ)


¬¬Σ-gives-Σ-min : {n : ℕ} (A : Fin n → 𝓤 ̇ )
                → is-complemented A → ¬¬ Σ A → Σ-min A

¬¬Σ-gives-Σ-min {𝓤} {n} A δ u = Σ-gives-Σ-min A δ (¬¬-elim (Fin-Compact A δ) u)

Σ-min-is-prop : FunExt
              → {n : ℕ} (A : Fin n → 𝓤 ̇ )
              → is-prop-valued-family A → is-prop (Σ-min A)

Σ-min-is-prop {𝓤} fe {n} A h (i , a , l) (i' , a' , l') = γ
 where
  p : i ＝ i'
  p = ⟦_⟧-lc n (≤-anti (⟦_⟧ i) (⟦_⟧ i') u v)
   where
    u : i ≤ i'
    u = l i' a'

    v : i' ≤ i
    v = l' i a

  H : ∀ j → is-prop (A j × (j is-lower-bound-of A))
  H j = ×-is-prop
         (h j)
         (Π-is-prop (fe 𝓤₀ 𝓤)
           (λ k → Π-is-prop (fe 𝓤 𝓤₀)
                   (λ b → ≤-is-prop-valued (⟦_⟧ j) (⟦_⟧ k))))

  γ : i , a , l ＝ i' , a' , l'
  γ = to-Σ-＝ (p , H _ _ _)

\end{code}
