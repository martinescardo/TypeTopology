Martin Escardo, early 2013, typed 5th May 2018

We show that the type of roots of a function α : ℕ → Z has a
propositional truncation, in pure spartan Martin-Löf theory (without
using function extensionality). We also show that if we already have
truncations, we can "exit" the truncation of the set of roots.

The following can be specialized to any type Z with an isolated point
z taken as an abstract zero, including ℕ and 𝟚 with any of its
points. Recall that a point of a type is called isolated if its
equality with any other point of the type is decidable.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.DiscreteAndSeparated
open import UF.Base

module Naturals.RootsTruncation where

open import MLTT.Plus-Properties
open import Naturals.Order
open import Notation.Order
open import UF.Hedberg
open import UF.KrausLemma
open import UF.KrausLemma
open import UF.PropTrunc
open import UF.Subsingletons

module Roots-truncation
        {𝓤 : Universe}
        (Z : 𝓤 ̇ )
        (z : Z)
        (z-is-isolated : is-isolated' z)
       where

\end{code}

We now consider whether there is or there isn't a minimal root
(strictly) bounded by a number k, where a root of α is an n : ℕ with
α n ＝ z.

\begin{code}

 _has-no-root<_ : (ℕ → Z) → ℕ → 𝓤 ̇
 α has-no-root< k = (n : ℕ) → n < k → α n ≠ z

 _has-a-minimal-root<_ : (ℕ → Z) → ℕ → 𝓤 ̇
 α has-a-minimal-root< k = Σ m ꞉ ℕ , (α m ＝ z)
                                      × (m < k)
                                      × α has-no-root< m

 FPO : ℕ → (ℕ → Z) → 𝓤 ̇
 FPO k α = α has-a-minimal-root< k
         + α has-no-root< k

\end{code}

The above "finite principle of omniscience" is a univalent proposition
using functional extensionality. However, we want to avoid function
extensionality here.

\begin{code}

 fpo : ∀ k α → FPO k α
 fpo 0 α = inr (λ n p → 𝟘-elim p)
 fpo (succ k) α = cases f g (fpo k α)
  where
   f : α has-a-minimal-root< k → FPO (succ k) α
   f (m , p , l , φ) = inl (m , p , ≤-trans (succ m) k (succ k) l (≤-succ k) , φ)

   g : α has-no-root< k → FPO (succ k) α
   g φ = cases g₀ g₁ (z-is-isolated (α k))
    where
     g₀ : α k ＝ z → FPO (succ k) α
     g₀ p = inl (k , p , ≤-refl k , φ)

     g₁ : α k ≠ z → FPO (succ k) α
     g₁ u = inr (bounded-∀-next (λ n → α n ≠ z) k u φ)

\end{code}

Given any root, we can find a minimal root.

\begin{code}

 minimal-root : ∀ α n → α n ＝ z → α has-a-minimal-root< (succ n)
 minimal-root α n p = Right-fails-gives-left-holds (fpo (succ n) α) g
  where
   g : ¬ (α has-no-root< (succ n))
   g φ = φ n (≤-refl n) p

\end{code}

With this we can define a constant endomap on the type of roots, that
given any root finds a minimal root. Notice that the type of roots may
be empty, and still the function is well defined.

\begin{code}

 Root : (ℕ → Z) → 𝓤 ̇
 Root α = Σ n ꞉ ℕ , α n ＝ z

 μρ : (α : ℕ → Z) → Root α → Root α
 μρ α (n , p) = pr₁ (minimal-root α n p) , pr₁ (pr₂ (minimal-root α n p))

 μ-root : (α : ℕ → Z) → Root α → ℕ
 μ-root α r = pr₁ (μρ α r)

 μ-root-is-root : (α : ℕ → Z) (r : Root α) → α (μ-root α r) ＝ z
 μ-root-is-root α r = pr₂ (μρ α r)

 μ-root-is-minimal : (α : ℕ → Z) (m : ℕ) (p : α m ＝ z)
                   → (n : ℕ) → α n ＝ z → μ-root α (m , p) ≤ n
 μ-root-is-minimal α m p n q = not-less-bigger-or-equal k n g
  where
   k : ℕ
   k = μ-root α (m , p)

   f : n < k → α n ≠ z
   f = pr₂ (pr₂ (pr₂ (minimal-root α m p))) n

   g : ¬ (n < k)
   g l = f l q

 μρ-constant : (α : ℕ → Z) → wconstant (μρ α)
 μρ-constant α (n , p) (n' , p') = r
  where
   m m' : ℕ
   m  = μ-root α (n , p)
   m' = μ-root α (n' , p')

   l : m ≤ m'
   l = μ-root-is-minimal α n p m' (μ-root-is-root α (n' , p'))

   l' : m' ≤ m
   l' = μ-root-is-minimal α n' p' m (μ-root-is-root α (n , p))

   q : m ＝ m'
   q = ≤-anti _ _ l l'

   r : μρ α (n , p) ＝ μρ α (n' , p')
   r = to-Σ-＝ (q , isolated-Id-is-prop z z-is-isolated _ _ _)

 Root-has-prop-truncation : (α : ℕ → Z) → ∀ 𝓥 → has-prop-truncation 𝓥 (Root α)
 Root-has-prop-truncation α = collapsible-has-prop-truncation
                               (μρ α , μρ-constant α)

\end{code}

Explicitly (and repeating the construction of Root-has-prop-truncation):

\begin{code}

 Root-truncation : (ℕ → Z) → 𝓤 ̇
 Root-truncation α = Σ r ꞉ Root α , r ＝ μρ α r

 Root-truncation-is-prop : (α : ℕ → Z) → is-prop (Root-truncation α)
 Root-truncation-is-prop α = fix-is-prop (μρ α) (μρ-constant α)

 η-Root : (α : ℕ → Z) → Root α → Root-truncation α
 η-Root α = to-fix (μρ α) (μρ-constant α)

 Root-truncation-universal : (α : ℕ → Z) (P : 𝓥 ̇ )
                           → is-prop P → (Root α → P) → Root-truncation α → P
 Root-truncation-universal α P _ f t = f (from-fix (μρ α) t)

\end{code}

We can't normally "exit a truncation", but in this special case we can:

\begin{code}

 Root-exit-truncation : (α : ℕ → Z) → Root-truncation α → Root α
 Root-exit-truncation α = from-fix (μρ α)

\end{code}

Of course, if we already have propositional truncations, we can exit
root truncations using the above technique.

\begin{code}

 module exit-Roots-truncation (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt
  open split-support-and-collapsibility pt

  exit-Root-truncation : (α : ℕ → Z) → (∃ n ꞉ ℕ , α n ＝ z) → Σ n ꞉ ℕ , α n ＝ z
  exit-Root-truncation α = collapsible-gives-split-support (μρ α , μρ-constant α)

\end{code}

This says that if there is a root, then we can find one.

Added 17th August 2024.

\begin{code}

open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable

minimal-witness : (A : ℕ → 𝓤 ̇ )
                → is-complemented A
                → (Σ n ꞉ ℕ , A n)
                → Σ m ꞉ ℕ , (A m × ((k : ℕ) → A k → m ≤ k))
minimal-witness A A-is-complemented (n , aₙ) = m , aₘ , m-is-minimal-witness
 where
  open Roots-truncation 𝟚 ₀ (λ b → 𝟚-is-discrete b ₀)

  α : ℕ → 𝟚
  α = characteristic-map A A-is-complemented

  n-is-root : α n ＝ ₀
  n-is-root = characteristic-map-property₀-back A A-is-complemented n aₙ

  r : Root α
  r = n , n-is-root

  m : ℕ
  m = μ-root α r

  m-is-root : α m ＝ ₀
  m-is-root = μ-root-is-root α r

  aₘ : A m
  aₘ = characteristic-map-property₀ A A-is-complemented m m-is-root

  m-is-minimal-root : (k : ℕ) → α k ＝ ₀ → m ≤ k
  m-is-minimal-root = μ-root-is-minimal α n n-is-root

  m-is-minimal-witness : (k : ℕ) → A k → m ≤ k
  m-is-minimal-witness k aₖ = m-is-minimal-root k k-is-root
   where
    k-is-root : α k ＝ ₀
    k-is-root = characteristic-map-property₀-back A A-is-complemented k aₖ

module exit-truncations (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 exit-truncation : (A : ℕ → 𝓤 ̇ )
                 → is-complemented A
                 → (∃ n ꞉ ℕ , A n)
                 → Σ n ꞉ ℕ , A n
 exit-truncation A A-is-complemented e = IV
  where
   open Roots-truncation 𝟚 ₀ (λ b → 𝟚-is-discrete b ₀)
   open exit-Roots-truncation pt

   α : ℕ → 𝟚
   α = characteristic-map A A-is-complemented

   I : (Σ n ꞉ ℕ , A n) → Σ n ꞉ ℕ , α n ＝ ₀
   I (n , a) = n , characteristic-map-property₀-back A A-is-complemented n a

   e' : ∃ n ꞉ ℕ , α n ＝ ₀
   e' = ∥∥-functor I e

   II : Σ n ꞉ ℕ , α n ＝ ₀
   II = exit-Root-truncation α e'

   III : (Σ n ꞉ ℕ , α n ＝ ₀) → Σ n ꞉ ℕ , A n
   III (n , e) = n , characteristic-map-property₀ A A-is-complemented n e

   IV : Σ n ꞉ ℕ , A n
   IV = III II

\end{code}

Added 18th September 2024. The following "exit-truncation lemma"
generalizes the above development with a simpler proof. But this
result was already known in

   Martín H. Escardó and Chuangjie Xu. The inconsistency of a
   Brouwerian continuity principle with the Curry-Howard
   interpretation. 13th International Conference on Typed Lambda
   Calculi and Applications (TLCA 2015).

   https://drops.dagstuhl.de/opus/portals/lipics/index.php?semnr=15006
   https://doi.org/10.4230/LIPIcs.TLCA.2015.153

although it was presented with a different proof that assumes function
extensionlity.

\begin{code}

private
 abstract
  minimal-pair' : (A : ℕ → 𝓤 ̇ )
                → ((n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k))
                → (n : ℕ)
                → A n
                → Σ (k , aₖ) ꞉ Σ A , ((i : ℕ) → A i → k ≤ i)
  minimal-pair' A δ 0        a₀   = (0 , a₀) , (λ i aᵢ → zero-least i)
  minimal-pair' A δ (succ n) aₙ₊₁ = II
   where
    IH : Σ (j , aⱼ₊₁) ꞉ Σ (A ∘ succ) , ((i : ℕ) → A (succ i) → j ≤ i)
    IH = minimal-pair' (A ∘ succ) (λ n aₙ₊₁ j → δ (succ n) aₙ₊₁ (succ j)) n aₙ₊₁

    I : type-of IH
      → Σ (k , aₖ) ꞉ Σ A , ((i : ℕ) → A i → k ≤ i)
    I ((j , aⱼ₊₁) , b) =
     Cases (δ (succ n) aₙ₊₁ 0 (zero-least j))
      (λ (a₀ :    A 0) → (0 , a₀)        , (λ i aᵢ → zero-least i))
      (λ (ν₀  : ¬ A 0) → (succ j , aⱼ₊₁) , I₀ ν₀)
       where
        I₀ : ¬ A 0 → (i : ℕ) (aᵢ : A i) → j < i
        I₀ ν₀ 0        a₀   = 𝟘-elim (ν₀ a₀)
        I₀ ν₀ (succ i) aᵢ₊₁ = b i aᵢ₊₁

    II : Σ (k , aⱼ) ꞉ Σ A , ((i : ℕ) → A i → k ≤ i)
    II = I IH

module _ (A : ℕ → 𝓤 ̇ )
         (δ : (n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k))
       where

 minimal-pair : Σ A → Σ A
 minimal-pair (n , aₙ) = pr₁ (minimal-pair' A δ n aₙ)

 minimal-number : Σ A → ℕ
 minimal-number = pr₁ ∘ minimal-pair

 minimal-number-requirement : (σ : Σ A) → A (minimal-number σ)
 minimal-number-requirement = pr₂ ∘ minimal-pair

 minimality : (σ : Σ A) → (i : ℕ) → A i → minimal-number σ ≤ i
 minimality (n , aₙ) = pr₂ (minimal-pair' A δ n aₙ)

 minimal-pair-wconstant : is-prop-valued-family A → wconstant minimal-pair
 minimal-pair-wconstant A-prop-valued σ σ' =
  to-subtype-＝ A-prop-valued
   (need
     minimal-number σ ＝ minimal-number σ'
    which-is-given-by
     ≤-anti _ _
      (minimality σ  (minimal-number σ') (minimal-number-requirement σ'))
      (minimality σ' (minimal-number σ)  (minimal-number-requirement σ)))

module exit-truncations' (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open split-support-and-collapsibility pt

 exit-truncation⁺ : (A : ℕ → 𝓤 ̇ )
                  → is-prop-valued-family A
                  → ((n : ℕ) → A n → (k : ℕ) → k < n → is-decidable (A k))
                  → ∥ Σ A ∥ → Σ A
 exit-truncation⁺ A A-prop-valued δ =
  collapsible-gives-split-support
   (minimal-pair A δ , minimal-pair-wconstant A δ A-prop-valued)

\end{code}

This is not quite a generalization of the previous result, because the
previous result doesn't have the assumption that A is prop-valued.

TODO. Can we remove the prop-valuedness assumption?
