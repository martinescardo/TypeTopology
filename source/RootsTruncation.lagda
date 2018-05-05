Martin Escardo, early 2013, typed 5th May 2018

We show that the type of roots of a function α : ℕ → 𝟚 has a
propositional truncation, in pure spartan Martin-Löf theory (without
using function extensionality).

\begin{code}

module  RootsTruncation where

open import NaturalsOrder
open import UF-Base hiding (_≤_) hiding (≤-anti)
open import UF-Subsingletons
open import DiscreteAndSeparated
open import UF-SetExamples
open import UF-KrausLemma

β∀-next : ∀ {U} (A : ℕ → U ̇) (k : ℕ)
        → A k
        → ((n : ℕ) → n < k → A n)
        → (n : ℕ) → n < succ k → A n
β∀-next A k a φ n l = cases f g s
 where
  s : (n < k) + (succ n ≡ succ k)
  s = ≤-split (succ n) k l
  f : n < k → A n
  f = φ n
  g : succ n ≡ succ k → A n
  g p = back-transport A (succ-injective p) a
  
FPO : ℕ → (ℕ → 𝟚) → U₀ ̇
FPO k α = (Σ \(m : ℕ) → (α m ≡ ₀) × (m < k) × (Π \(n : ℕ) → n < m → α n ≢ ₀))
        + (Π \(n : ℕ) → n < k → α n ≢ ₀)

\end{code}

The above "finite principle of omniscience" is a proposition using
functional extensionality. However, here we want to avoid function
extensionality.

\begin{code}

fpo : (k : ℕ) (α : ℕ → 𝟚) → FPO k α
fpo zero α = inr (λ n ())
fpo (succ k) α = cases f g (fpo k α)
 where
  f : (Σ \(m : ℕ) → (α m ≡ ₀) × (m < k) × ((n : ℕ) → n < m → α n ≢ ₀)) → FPO (succ k) α
  f (m , p , l , φ) = inl (m , p , ≤-trans (succ m) k (succ k) l (≤-succ k) , φ)
  
  g : ((n : ℕ) → n < k → α n ≢ ₀) → FPO (succ k) α
  g φ = cases f₀ f₁ (𝟚-discrete (α k) ₀)
   where
    f₀ : α k ≡ ₀ → FPO (succ k) α
    f₀ p = inl (k , p , ≤-refl k , φ)
    
    f₁ : α k ≢ ₀ → FPO (succ k) α
    f₁ u = inr (β∀-next (λ n → α n ≢ ₀) k u φ)

\end{code}

Given any root, we can find a minimal root.

\begin{code}

minimal-root : (α : ℕ → 𝟚) → (n : ℕ) → α n ≡ ₀
            → Σ \(m : ℕ) → (α m ≡ ₀) × (m ≤ n) × ((n : ℕ) → n < m → α n ≢ ₀)
minimal-root α n p = Right-fails-then-left-holds (fpo (succ n) α) (λ φ → φ n (≤-refl n) p)

\end{code}

With this we can define a constant endomap on the type of roots:

\begin{code}

roots : (ℕ → 𝟚) → U₀ ̇
roots α = Σ \(n : ℕ) → α n ≡ ₀

μρ : (α : ℕ → 𝟚) → roots α → roots α
μρ α (n , p) = pr₁ (minimal-root α  n p) , pr₁ (pr₂ (minimal-root α n p))

μρ-root : (α : ℕ → 𝟚) → roots α → ℕ
μρ-root α r = pr₁ (μρ α r)

μρ-root-is-root : (α : ℕ → 𝟚) (r : roots α) → α (μρ-root α r) ≡ ₀
μρ-root-is-root α r = pr₂ (μρ α r)

μρ-root-bound : (α : ℕ → 𝟚) (m : ℕ) (p : α m ≡ ₀)
              → μρ-root α (m , p) ≤ m
μρ-root-bound α m p = pr₁(pr₂(pr₂ (minimal-root α m p))) 

μρ-root-minimal : (α : ℕ → 𝟚) (m : ℕ) (p : α m ≡ ₀)
                → (n : ℕ) → α n ≡ ₀ → μρ-root α (m , p) ≤ n
μρ-root-minimal α m p n q = not-less-bigger-or-equal (μρ-root α (m , p)) n (a (double-negation-intro q))
 where
  a : ¬(α n ≢ ₀) → ¬(n < μρ-root α (m , p))
  a = contrapositive (pr₂(pr₂(pr₂ (minimal-root α m p))) n)

μρ-constant : (α : ℕ → 𝟚) → constant (μρ α)
μρ-constant α (n , p) (n' , p') = to-Σ-≡'' (q , 𝟚-isSet _ _)
 where
  u : μρ-root α (n , p) ≤ μρ-root α (n' , p')
  u = μρ-root-minimal α n p (μρ-root α (n' , p')) (μρ-root-is-root α (n' , p'))
  v : μρ-root α (n' , p') ≤ μρ-root α (n , p)
  v = μρ-root-minimal α n' p' (μρ-root α (n , p)) (μρ-root-is-root α (n , p))
  q : μρ-root α (n , p) ≡ μρ-root α (n' , p')
  q = ≤-anti _ _ u v
 
roots-collapsible : (α : ℕ → 𝟚) → collapsible (roots α)
roots-collapsible α = μρ α , μρ-constant α
 
roots-hasPropTruncation : (α : ℕ → 𝟚) → ∀ U → hasPropTruncation U (roots α)
roots-hasPropTruncation α = collapsible-hasPropTruncation (roots-collapsible α)

\end{code}

Explicitly (and repeating the construction of roots-hasPropTruncation):

\begin{code}

roots-truncation : (ℕ → 𝟚) → U₀ ̇
roots-truncation α = Σ \(r : roots α) → r ≡ μρ α r

roots-truncation-isProp : (α : ℕ → 𝟚) → isProp (roots-truncation α)
roots-truncation-isProp α = Kraus-Lemma (μρ α) (μρ-constant α)

roots-η : (α : ℕ → 𝟚) → roots α → roots-truncation α
roots-η α = to-fix (μρ α) (μρ-constant α)

roots-universal : (α : ℕ → 𝟚) → ∀ {U} (P : U ̇)
                  → isProp P → (roots α → P) → roots-truncation α → P
roots-universal α {U} P _ f t = f (from-fix (μρ α) t)

\end{code}

We can't normally "exit a truncation", but in this special case we can:

\begin{code}

roots-exit-truncation : (α : ℕ → 𝟚) → roots-truncation α → roots α
roots-exit-truncation α = from-fix (μρ α)

\end{code}
