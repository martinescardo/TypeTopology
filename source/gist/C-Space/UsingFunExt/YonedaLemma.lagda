Chuangjie Xu 2012 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module gist.C-Space.UsingFunExt.YonedaLemma (fe : DN-funext 𝓤₀ 𝓤₀) where

open import gist.C-Space.Preliminaries.Sequence
open import gist.C-Space.Preliminaries.Naturals.Order
open import gist.C-Space.UniformContinuity
open import gist.C-Space.Coverage
open import gist.C-Space.UsingFunExt.Space
open import gist.C-Space.UsingFunExt.CartesianClosedness fe
open import gist.C-Space.UsingFunExt.DiscreteSpace fe

\end{code}

Because our site is a one-object category, there is only one representable
sheaf, which is concrete and hence can be regarded as a C-space.  This concrete
sheaf, seen as a C-space, is the set ₂ℕ equipped with all uniformly continuous
maps ₂ℕ → ₂ℕ as probes.  Moreover, it is (isomorphic to) the exponential of the
discrete spaces 𝟚Space and ℕSpace in the category of C-spaces.  The following
lemma is one direction of this fact, which assigns each probe on ₂ℕ, i.e. a
uniformly continuous map, to a probe on the exponential ℕSpace ⇒ 𝟚Space.

\begin{code}

Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] : (r : ₂ℕ → ₂ℕ) → r ∈ C →
     Σ \(φ : ₂ℕ → U (ℕSpace ⇒ 𝟚Space)) → φ ∈ Probe (ℕSpace ⇒ 𝟚Space)
Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] r ucr = φ , prf
 where
  φ : ₂ℕ → U (ℕSpace ⇒ 𝟚Space)
  φ α = r α , Lemma[discrete-ℕSpace] 𝟚Space (r α)
  prf : ∀(p : ₂ℕ → ℕ) → p ∈ LC → ∀(t : ₂ℕ → ₂ℕ) → t ∈ C →
         (λ α → (pr₁ ∘ φ)(t α)(p α)) ∈ LC
  prf p ucp t uct = Lemma[LM-₂-least-modulus] q l pr
   where
    q : ₂ℕ → 𝟚
    q α = (pr₁ ∘ φ)(t α)(p α)
    m : ℕ
    m = pr₁ ucp
    f : ₂Fin m → ℕ
    f s = p (cons s 0̄)
    eq : ∀(α : ₂ℕ) → p α ＝ f (take m α)
    eq α = pr₁ (pr₂ ucp) α (cons (take m α) 0̄) (Lemma[cons-take-＝⟦⟧] m α 0̄)
    k' : ℕ
    k' = pr₁ (max-fin f)
    k'-max : ∀(α : ₂ℕ) → p α ≤ k'
    k'-max α = transport (λ i → i ≤ k') ((eq α) ⁻¹) (pr₂ (max-fin f) (take m α))
    k : ℕ
    k = succ k'
    k-max : ∀(α : ₂ℕ) → p α < k
    k-max α = ≤-succ (k'-max α)
    ucrt : uniformly-continuous-₂ℕ (r ∘ t)
    ucrt = Lemma[∘-UC] r ucr t uct
    n : ℕ
    n = pr₁ (ucrt k)
    l : ℕ
    l = max m n
    m≤l : m ≤ l
    m≤l = max-spec₀ m n
    n≤l : n ≤ l
    n≤l = max-spec₁ m n
    pr : ∀(α β : ₂ℕ) → α ＝⟦ l ⟧ β → r(t α)(p α) ＝ r(t β)(p β)
    pr α β awl = transport (λ i → r(t α)(p α) ＝ r(t β) i) eqp subgoal
     where
      awm : α ＝⟦ m ⟧ β
      awm = Lemma[＝⟦⟧-≤] awl m≤l
      eqp : p α ＝ p β
      eqp = pr₁ (pr₂ ucp) α β awm
      awn : α ＝⟦ n ⟧ β
      awn = Lemma[＝⟦⟧-≤] awl n≤l
      awk : r (t α) ＝⟦ k ⟧ r (t β)
      awk = pr₁ (pr₂ (ucrt k)) α β awn
      subgoal : r(t α)(p α) ＝ r(t β)(p α)
      subgoal = Lemma[＝⟦⟧-<] awk (p α) (k-max α)

\end{code}

In particular, the "identity" map ₂ℕ → U(ℕSpace ⇒ 𝟚Space) is a probe on the
exponential ℕSpace ⇒ 𝟚Space.

\begin{code}

ID : ₂ℕ → U(ℕSpace ⇒ 𝟚Space)
ID = pr₁ (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] id Lemma[id-UC])

Lemma[ID-＝] : ∀(α : U (ℕSpace ⇒ 𝟚Space)) → α ＝ ID (pr₁ α)
Lemma[ID-＝] α = Lemma[Map-₂-＝] ℕSpace α (ID (pr₁ α)) (λ _ → refl)

ID-is-a-probe : ID ∈ Probe(ℕSpace ⇒ 𝟚Space)
ID-is-a-probe = pr₂ (Lemma[₂ℕ→₂ℕ-to-₂ℕ→ℕ⇒₂] id Lemma[id-UC])

\end{code}

Using the above facts, we conclude that the Yoneda Lemma amounts to saying that
the set of continuous maps from the exponential ℕSpace ⇒ 𝟚Space to any C-space X
is isomorphic to the C-topology of X.  The following gives one direction of the
Yoneda Lemma, which is sufficient to construct a fan functional.

\begin{code}

Lemma[Yoneda] : ∀(X : Space) → Map (ℕSpace ⇒ 𝟚Space) X →
                 Σ \(p : ₂ℕ → U X) → p ∈ Probe X
Lemma[Yoneda] X (f , cts) = (f ∘ ID) , (cts ID ID-is-a-probe)

\end{code}
