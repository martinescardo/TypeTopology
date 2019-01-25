Martin Escardo, 11th September 2018

We begin by defining a "codistance" or "closeness" function

  c : X → X → ℕ∞

such that

  c x y ≡ ∞ ⇔ x ≡ y

for some examples of types X, including Baire, Cantor and ℕ∞.

That is, two points are equal iff they are infinitely close.  If we
have c x y ≡ under n for n : ℕ, the intuition is that x and y can be
distinguished by a finite amount of information of size n.

(An application is to show that WLPO holds iff ℕ∞ is discrete.)

We then discuss further codistance axioms.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module Codistance (fe : FunExt) where

open import Two
open import Sequence fe
open import CoNaturals fe
open import GenericConvergentSequence
open import DiscreteAndSeparated
open import UF-Miscelanea

module sequences
        {𝓤 : Universe}
        (D : 𝓤 ̇)
        (δ : is-discrete D)
       where

\end{code}

We denote the type of sequences over D by $, and define a codistance
function $ → $ → ℕ∞ using the fact that ℕ∞ is the final coalgebra of
the functor 𝟙 + (-), which we refer to as corecursion.

\begin{code}

 private
  𝓢 : 𝓤 ̇
  𝓢 = ℕ → D
  X : 𝓤 ̇
  X = 𝓢 × 𝓢
  f : (α β : 𝓢) → head α ≡ head β → 𝟙 {𝓤₀} + X
  f α β q = inr (tail α , tail β)
  g : (α β : 𝓢) → head α ≢ head β → 𝟙 {𝓤₀} + X
  g α β n = inl *
  p : X → 𝟙 {𝓤₀} + X
  p (α , β) = cases (f α β) (g α β) (δ (head α) (head β))
  c : 𝓢 → 𝓢 → ℕ∞
  c = curry (ℕ∞-corec p)

\end{code}

We use the private name "c" in this submodule, which is exported as
"codistance":

\begin{code}

 codistance : 𝓢 → 𝓢 → ℕ∞
 codistance = c

\end{code}

The two defining properties of the function c are the following:

\begin{code}

 codistance-eq₀ : (α β : 𝓢) → head α ≢ head β → c α β ≡ Zero
 codistance-eq₁ : (α β : 𝓢) → head α ≡ head β → c α β ≡ Succ (c (tail α) (tail β))

 codistance-eq₀ α β n = γ r
  where
   t : δ (head α) (head β) ≡ inr n
   t = discrete-inr (fe 𝓤 𝓤₀) δ (head α) (head β) n
   r : p (α , β) ≡ inl *
   r = ap (cases (f α β) (g α β)) t
   γ : p (α , β) ≡ inl * → c α β ≡ Zero
   γ = Coalg-morphism-Zero p (α , β) *

 codistance-eq₁ α β q = γ r
  where
   t : δ (head α) (head β) ≡ inl q
   t = discrete-inl δ (head α) (head β) q
   r : p (α , β) ≡ inr (tail α , tail β)
   r = ap (cases (f α β) (g α β)) t
   γ : p (α , β) ≡ inr (tail α , tail β) → c α β ≡ Succ (c (tail α) (tail β))
   γ = Coalg-morphism-Succ p (α , β) (tail α , tail β)

\end{code}

That any sequence is infinitely close to itself is proved by
coinduction on ℕ∞ using codistance-eq₁:

\begin{code}

 infinitely-close-to-itself : (α : 𝓢) → c α α ≡ ∞
 infinitely-close-to-itself α = ℕ∞-coinduction R b (c α α) ∞ γ
  where
   l : ∀ α → c α α ≡ Succ (c (tail α) (tail α))
   l α = codistance-eq₁ α α refl
   R : ℕ∞ → ℕ∞ → 𝓤 ̇
   R u v = (Σ \(α : 𝓢) → u ≡ c α α) × (v ≡ ∞)
   b : ℕ∞-bisimulation R
   b .(c α α) .∞ ((α , refl) , refl) = s , t , Pred-∞-is-∞
    where
     s : positivity (c α α) ≡ positivity ∞
     s = successors-same-positivity (l α) ((Succ-∞-is-∞ (fe 𝓤₀ 𝓤₀))⁻¹)
     t : Σ (\(α' : 𝓢) → Pred (c α α) ≡ c α' α')
     t = tail α , (ap Pred (l α) ∙ Pred-Succ)
   γ : R (c α α) ∞
   γ = (α , refl) , refl

\end{code}

That any two infinitely close sequences are equal is proved by
coinduction on sequences, using both codistance-eq₀ (to rule out an
impossible case) and codistance-eq₁ (to establish the result):

\begin{code}

 infinitely-close-are-equal : (α β : 𝓢) → c α β ≡ ∞ → α ≡ β
 infinitely-close-are-equal = seq-coinduction (λ α β → c α β ≡ ∞) b
  where
   b : (α β : 𝓢) → c α β ≡ ∞
                 → (head α ≡ head β) × (c (tail α) (tail β) ≡ ∞)
   b α β q = d , e
    where
     l : head α ≢ head β → c α β ≡ Zero
     l = codistance-eq₀ α β
     d : head α ≡ head β
     d = Cases (δ (head α) (head β))
          (λ (p : head α ≡ head β)
                → p)
          (λ (n : head α ≢ head β)
                → 𝟘-elim (Zero-not-Succ (Zero    ≡⟨ (l n)⁻¹ ⟩
                                         c α β   ≡⟨ q ⟩
                                         ∞       ≡⟨ (Succ-∞-is-∞ (fe 𝓤₀ 𝓤₀))⁻¹ ⟩
                                         Succ ∞  ∎)))
     e : c (tail α) (tail β) ≡ ∞
     e = ap Pred (Succ (c (tail α) (tail β)) ≡⟨ (codistance-eq₁ α β d)⁻¹ ⟩
                  c α β                      ≡⟨ q ⟩
                  ∞                          ∎)

\end{code}

We now consider the following two special cases for the Baire and
Cantor types:

\begin{code}

open sequences ℕ ℕ-is-discrete
 renaming
  (codistance                 to Baire-codistance ;
   infinitely-close-to-itself to Baire-infinitely-close-to-itself ;
   infinitely-close-are-equal to Baire-infinitely-close-are-equal)

open sequences 𝟚 𝟚-is-discrete
 renaming
  (codistance                 to Cantor-codistance ;
   infinitely-close-to-itself to Cantor-infinitely-close-to-itself ;
   infinitely-close-are-equal to Cantor-infinitely-close-are-equal)

\end{code}

And now we reduce the codistance of the Cantor type to the generic
convergent sequence:

\begin{code}

ℕ∞-codistance : ℕ∞ → ℕ∞ → ℕ∞
ℕ∞-codistance u v = Cantor-codistance (incl u) (incl v)

ℕ∞-infinitely-close-to-itself : (u : ℕ∞) → ℕ∞-codistance u u ≡ ∞
ℕ∞-infinitely-close-to-itself u = Cantor-infinitely-close-to-itself (incl u)

ℕ∞-equal-are-infinitely-close : (u v : ℕ∞) → u ≡ v → ℕ∞-codistance u v ≡ ∞
ℕ∞-equal-are-infinitely-close u .u refl = ℕ∞-infinitely-close-to-itself u

ℕ∞-infinitely-close-are-equal : (u v : ℕ∞) → ℕ∞-codistance u v ≡ ∞ → u ≡ v
ℕ∞-infinitely-close-are-equal u v r = incl-lc (fe 𝓤₀ 𝓤₀) γ
 where
  γ : incl u ≡ incl v
  γ = Cantor-infinitely-close-are-equal (incl u) (incl v) r

\end{code}

Axioms for codistance:

\begin{code}

open import CoNaturalsArithmetic fe

is-codistance
 indistinguishable-are-equal
 self-indistinguishable
 is-symmetric
 is-ultra
  : {X : 𝓤 ̇} → (X → X → ℕ∞) → 𝓤 ̇

indistinguishable-are-equal c = ∀ x y → c x y ≡ ∞ → x ≡ y
self-indistinguishable      c = ∀ x → c x x ≡ ∞
is-symmetric                c = ∀ x y → c x y ≡ c y x
is-ultra                    c = ∀ x y z → min (c x y , c y z) ≼ c x z
is-codistance               c = indistinguishable-are-equal c
                              × self-indistinguishable c
                              × is-symmetric c
                              × is-ultra c
\end{code}

TODO. Show that the above codistances are indeed codistances according
to this definition.
