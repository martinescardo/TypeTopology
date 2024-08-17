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

module Naturals.RootsTruncation
        (𝓤 : Universe)
        (Z : 𝓤 ̇ )
        (z : Z)
        (z-is-isolated : is-isolated' z)
       where

open import MLTT.Plus-Properties
open import Naturals.Order
open import Notation.Order
open import UF.Subsingletons
open import UF.KrausLemma
open import UF.Hedberg

\end{code}

We now consider whether there is or there isn't a minimal root
(strictly) bounded by a number k, where a root of α is an n : ℕ with α
n ＝ z.

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
fpo zero α = inr (λ n p → 𝟘-elim p)
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
Root-has-prop-truncation α = collapsible-has-prop-truncation (μρ α , μρ-constant α)

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

open import UF.PropTrunc

module ExitRootTruncations (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 exit-Root-truncation : (α : ℕ → Z) → (∃ n ꞉ ℕ , α n ＝ z) → Σ n ꞉ ℕ , α n ＝ z
 exit-Root-truncation α = h ∘ g
  where
   f : (Σ n ꞉ ℕ , α n ＝ z) → fix (μρ α)
   f = to-fix (μρ α) (μρ-constant α)

   g : ∥(Σ n ꞉ ℕ , α n ＝ z)∥ → fix (μρ α)
   g = ∥∥-rec (fix-is-prop (μρ α) (μρ-constant α)) f

   h : fix (μρ α) → Σ n ꞉ ℕ , α n ＝ z
   h = from-fix (μρ α)

\end{code}

This says that if there is a root, then we can find one.
