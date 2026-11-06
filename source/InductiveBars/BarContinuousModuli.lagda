Chuangjie Xu, November 2026

A function from Baire space to natural numbers is bar continuous iff
it has a bar-continuous modulus of pointwise continuity.

Using the logical equivalence between bar continuity and eloquence,
the above characterization transfers to eloquent functions.

This result is motivated by, and analogous to, the characterization
of tree-function continuity by continuous moduli discussed by Baillon,
Forster, Mahboubi, Pédrot and Piquerez in "A Zoo of Continuity Properties
in Constructive Type Theory" (2025, Section 5.3, Lemmas 26-28).

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import UF.FunExt using (Fun-Ext)

module InductiveBars.BarContinuousModuli (fe : Fun-Ext) where

open import MLTT.Spartan
open import MLTT.List
open import UF.Powerset

open import EffectfulForcing.MFPSAndVariations.Dialogue
 using (eloquent)

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.Continuity fe
open import InductiveBars.BrouwersThesis fe

\end{code}

A witness that V is an inductive bar is a well-founded tree.  Each
sequence α tells us how to navigate the tree: choose child `α 0` at
the root, then child `α 1` at the next node, and so on, until reaching
a leaf.

We can count the entries of α consumed, or equivalently, the depth of
the leaf selected by α.  If the depth is k, then the choices made form
the finite sequence `prefix k α`, and the leaf supplies evidence that
it belongs to V.

\begin{code}

bar-depth : (V : 𝓟 (List ℕ))
          → is-inductive-bar V
          → (ℕ → ℕ) → ℕ
bar-depth V (base v) α = 0
bar-depth V (step φ) α = succ (bar-depth _ (φ (α 0)) (α ∘ succ))

bar-depth-spec : (V : 𝓟 (List ℕ)) (b : is-inductive-bar V)
               → (α : ℕ → ℕ)
               → prefix (bar-depth V b α) α ∈ V
bar-depth-spec V (base v) α = v
bar-depth-spec V (step φ) α = bar-depth-spec _ (φ (α 0)) (α ∘ succ)

\end{code}

For every witness b that V is an inductive bar, the function `bar-depth V b`
is bar continuous.

\begin{code}

bar-depth-is-bar-continuous
 : (V : 𝓟 (List ℕ)) (b : is-inductive-bar V)
 → is-bar-continuous (bar-depth V b)
bar-depth-is-bar-continuous V (base v) = base (λ _ _ _ _ → refl)
bar-depth-is-bar-continuous V (step φ) = step ψ
 where
  μ : ℕ → (ℕ → ℕ) → ℕ
  μ n = bar-depth (section₁ V n) (φ n)
  W : 𝓟 (List ℕ)
  W = determining-prefixes (bar-depth V (step φ))
  ih : (n : ℕ) → is-inductive-bar (determining-prefixes (μ n))
  ih n = bar-depth-is-bar-continuous (section₁ V n) (φ n)
  θ : (n : ℕ) → determining-prefixes (μ n) ⊆ section₁ W n
  θ n s d α β (pα , eα) (pβ , eβ) = goal
   where
    e₀ : μ (α 0) (α ∘ succ) ＝ μ n (α ∘ succ)
    e₀ = ap (λ i → μ i (α ∘ succ)) pα
    e₁ : μ n (α ∘ succ) ＝ μ n (β ∘ succ)
    e₁ = d (α ∘ succ) (β ∘ succ) eα eβ
    e₂ : μ (β 0) (β ∘ succ) ＝ μ n (β ∘ succ)
    e₂ = ap (λ i → μ i (β ∘ succ)) pβ
    goal : succ (μ (α 0) (α ∘ succ)) ＝ succ (μ (β 0) (β ∘ succ))
    goal = ap succ (e₀ ∙ e₁ ∙ e₂ ⁻¹)
  ψ : (n : ℕ) → is-inductive-bar (section₁ W n)
  ψ n = inductive-bar-respects-inclusion _ _ (θ n) (ih n)

\end{code}

The bar-depth function of the inductive bar of determining prefixes of f
is a bar-continuous modulus of pointwise continuity of f.

\begin{code}

_is-a-modulus-of-continuity-of_ : ((ℕ → ℕ) → ℕ) → ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
M is-a-modulus-of-continuity-of f = (α β : ℕ → ℕ) → α ＝⦅ M α ⦆ β → f α ＝ f β

bar-continuity-gives-bar-continuous-modulus
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous f
 → Σ M ꞉ ((ℕ → ℕ) → ℕ) ,
     is-bar-continuous M × M is-a-modulus-of-continuity-of f
bar-continuity-gives-bar-continuous-modulus f bcf = M , bcM , mod
 where
  M : (ℕ → ℕ) → ℕ
  M = bar-depth (determining-prefixes f) bcf
  bcM : is-bar-continuous M
  bcM = bar-depth-is-bar-continuous (determining-prefixes f) bcf
  mod : M is-a-modulus-of-continuity-of f
  mod α β eM = bar-depth-spec _ bcf α α β eα eβ
   where
    eα : α extends (prefix (M α) α)
    eα = extends-prefix α (M α)
    eβ : β extends (prefix (M α) α)
    eβ = agreement-implies-extends-prefix α β (M α) eM

\end{code}

Conversely, if M is a modulus of continuity of f, then prefix (M α) α
determines f for every α.  If M is bar continuous, then Brouwer's thesis for
bar-continuous witnesses makes the determining prefixes of f an inductive bar.

\begin{code}

bar-continuous-modulus-gives-bar-continuity
 : (f : (ℕ → ℕ) → ℕ)
 → (Σ M ꞉ ((ℕ → ℕ) → ℕ) ,
      is-bar-continuous M × M is-a-modulus-of-continuity-of f)
 → is-bar-continuous f
bar-continuous-modulus-gives-bar-continuity f (M , bcM , mod)
 = brouwers-thesis-for-bar-continuous-witnesses _ m M bcM wit
 where
  m : is-monotone (determining-prefixes f)
  m = determining-prefixes-is-monotone f
  wit : (α : ℕ → ℕ) → prefix (M α) α determines f
  wit α β γ eβ eγ = e₀ ⁻¹ ∙ e₁
   where
    e₀ : f α ＝ f β
    e₀ = mod α β (extends-prefix-implies-agreement α β (M α) eβ)
    e₁ : f α ＝ f γ
    e₁ = mod α γ (extends-prefix-implies-agreement α γ (M α) eγ)

\end{code}

Therefore, a function is bar continuous iff it has a bar-continuous
modulus of continuity.

\begin{code}

bar-continuity-iff-bar-continuous-modulus
 : (f : (ℕ → ℕ) → ℕ)
 →  is-bar-continuous f ↔
   (Σ M ꞉ ((ℕ → ℕ) → ℕ) ,
      is-bar-continuous M × M is-a-modulus-of-continuity-of f)
bar-continuity-iff-bar-continuous-modulus f
 = bar-continuity-gives-bar-continuous-modulus f
 , bar-continuous-modulus-gives-bar-continuity f

\end{code}

Because bar continuity is logically equivalent to eloquence, we have the
corresponding characterization of eloquence: a function is eloquent iff
it has an eloquent modulus of continuity.

\begin{code}

eloquence-gives-eloquent-modulus
 : (f : (ℕ → ℕ) → ℕ)
 → eloquent f
 → Σ M ꞉ ((ℕ → ℕ) → ℕ) ,
     eloquent M × M is-a-modulus-of-continuity-of f
eloquence-gives-eloquent-modulus f ef
 using (M , bcM , mod) ←
   bar-continuity-gives-bar-continuous-modulus f
     (eloquence-implies-bar-continuity f ef)
 = M , bar-continuity-implies-eloquence M bcM , mod

eloquent-modulus-gives-eloquence
 : (f : (ℕ → ℕ) → ℕ)
 → (Σ M ꞉ ((ℕ → ℕ) → ℕ) ,
      eloquent M × M is-a-modulus-of-continuity-of f)
 → eloquent f
eloquent-modulus-gives-eloquence f (M , eM , mod)
 = bar-continuity-implies-eloquence f
    (bar-continuous-modulus-gives-bar-continuity f
      (M , eloquence-implies-bar-continuity M eM , mod))

eloquence-iff-eloquent-modulus
 : (f : (ℕ → ℕ) → ℕ)
 →  eloquent f ↔
   (Σ M ꞉ ((ℕ → ℕ) → ℕ) ,
      eloquent M × M is-a-modulus-of-continuity-of f)
eloquence-iff-eloquent-modulus f
 = eloquence-gives-eloquent-modulus f
 , eloquent-modulus-gives-eloquence f

\end{code}
