Martin Escardo, early 2013, typed 5th May 2018

We show that the type of roots of a function α : ℕ → 𝟚 has a
propositional truncation, in pure spartan Martin-Löf theory (without
using function extensionality). We also show that if we already have
truncations, we can "exit" the truncation of the set of roots.

\begin{code}

module  RootsTruncation where

open import NaturalsOrder
open import UF-Base hiding (_≤_) hiding (≤-anti)
open import UF-Subsingletons
open import DiscreteAndSeparated
open import UF-SetExamples
open import UF-KrausLemma

\end{code}

We now consider whether there is or there isn't a minimal root
(strictly) bounded by a number k:

\begin{code}

there-is-a-minimal-root : ℕ → (ℕ → 𝟚) → U₀ ̇
there-is-a-minimal-root k α = Σ \(m : ℕ) → (α m ≡ ₀) × (m < k) × ((n : ℕ) → n < m → α n ≢ ₀)

there-is-no-root : ℕ → (ℕ → 𝟚) → U₀ ̇
there-is-no-root k α = (n : ℕ) → n < k → α n ≢ ₀

FPO : ℕ → (ℕ → 𝟚) → U₀ ̇
FPO k α = there-is-a-minimal-root k α + there-is-no-root k α

\end{code}

The above "finite principle of omniscience" is a proposition using
functional extensionality. However, we want to avoid function
extensionality here.

\begin{code}

fpo : (k : ℕ) (α : ℕ → 𝟚) → FPO k α
fpo zero α = inr (λ n ())
fpo (succ k) α = cases f g (fpo k α)
 where
  f : there-is-a-minimal-root k α → FPO (succ k) α
  f (m , p , l , φ) = inl (m , p , ≤-trans (succ m) k (succ k) l (≤-succ k) , φ)
  
  g : there-is-no-root k α → FPO (succ k) α
  g φ = cases g₀ g₁ (𝟚-discrete (α k) ₀)
   where
    g₀ : α k ≡ ₀ → FPO (succ k) α
    g₀ p = inl (k , p , ≤-refl k , φ)
    
    g₁ : α k ≢ ₀ → FPO (succ k) α
    g₁ u = inr (bounded-∀-next (λ n → α n ≢ ₀) k u φ)

\end{code}

Given any root, we can find a minimal root.

\begin{code}

minimal-root : (α : ℕ → 𝟚) → (n : ℕ) → α n ≡ ₀ → there-is-a-minimal-root (succ n) α
minimal-root α n p = Right-fails-then-left-holds (fpo (succ n) α) g
 where
  g : ¬(there-is-no-root (succ n) α)
  g φ = φ n (≤-refl n) p

\end{code}

With this we can define a constant endomap on the type of roots:

\begin{code}

roots : (ℕ → 𝟚) → U₀ ̇
roots α = Σ \(n : ℕ) → α n ≡ ₀

μρ : (α : ℕ → 𝟚) → roots α → roots α
μρ α (n , p) = pr₁ (minimal-root α n p) , pr₁ (pr₂ (minimal-root α n p))

μρ-root : (α : ℕ → 𝟚) → roots α → ℕ
μρ-root α r = pr₁ (μρ α r)

μρ-root-is-root : (α : ℕ → 𝟚) (r : roots α) → α (μρ-root α r) ≡ ₀
μρ-root-is-root α r = pr₂ (μρ α r)

μρ-root-minimal : (α : ℕ → 𝟚) (m : ℕ) (p : α m ≡ ₀)
                → (n : ℕ) → α n ≡ ₀ → μρ-root α (m , p) ≤ n
μρ-root-minimal α m p n q = not-less-bigger-or-equal (μρ-root α (m , p)) n (f (double-negation-intro q))
 where
  f : ¬(α n ≢ ₀) → ¬(n < μρ-root α (m , p))
  f = contrapositive (pr₂(pr₂(pr₂ (minimal-root α m p))) n)

μρ-constant : (α : ℕ → 𝟚) → constant (μρ α)
μρ-constant α (n , p) (n' , p') = r
 where
  u : μρ-root α (n , p) ≤ μρ-root α (n' , p')
  u = μρ-root-minimal α n p (μρ-root α (n' , p')) (μρ-root-is-root α (n' , p'))
  
  v : μρ-root α (n' , p') ≤ μρ-root α (n , p)
  v = μρ-root-minimal α n' p' (μρ-root α (n , p)) (μρ-root-is-root α (n , p))
  
  q : μρ-root α (n , p) ≡ μρ-root α (n' , p')
  q = ≤-anti _ _ u v

  r : μρ α (n , p) ≡ μρ α (n' , p')
  r = to-Σ-≡'' (q , 𝟚-isSet _ _)
 
roots-hasPropTruncation : (α : ℕ → 𝟚) → ∀ U → hasPropTruncation U (roots α)
roots-hasPropTruncation α = collapsible-hasPropTruncation (μρ α , μρ-constant α)

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

Of course, if we already have propositional truncations, we can exit
root truncations using the above technique.

\begin{code}

open import UF-PropTrunc

module ExitRootTruncations (pt : PropTrunc) where

 open PropositionalTruncation pt

 exit-roots-truncation : (α : ℕ → 𝟚) → ∥(Σ \(n : ℕ) → α n ≡ ₀)∥ → Σ \(n : ℕ) → α n ≡ ₀
 exit-roots-truncation α = h ∘ g
  where
   f : (Σ \(n : ℕ) → α n ≡ ₀) → fix (μρ α)
   f = to-fix (μρ α) (μρ-constant α)
   
   g : ∥(Σ \(n : ℕ) → α n ≡ ₀)∥ → fix (μρ α)
   g = ptrec (Kraus-Lemma (μρ α) (μρ-constant α)) f
   
   h : fix (μρ α) → Σ \(n : ℕ) → α n ≡ ₀
   h = from-fix (μρ α)

\end{code}

This says that if there is a root, then we can find one.
