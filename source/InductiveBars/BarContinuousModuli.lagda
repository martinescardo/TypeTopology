Chuangjie Xu, November 2026

A function of type (ℕ → A) → R is bar continuous iff it has a
self-modulating, bar-continuous modulus of pointwise continuity.

Using the logical equivalence between bar continuity and eloquence,
the above characterization transfers to eloquent functions.

This result is motivated by, and analogous to, the characterization
of tree-function continuity by continuous moduli discussed by Baillon,
Forster, Mahboubi, Pédrot and Piquerez in "A Zoo of Continuity Properties
in Constructive Type Theory" (2025, Section 5.3, Lemmas 26-28).

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan hiding (𝓤)
open import UF.FunExt using (Fun-Ext)

module InductiveBars.BarContinuousModuli
 (fe : Fun-Ext)
 {𝓤 : Universe}
 (A : 𝓤 ̇)
 where

open import MLTT.List
open import UF.DiscreteAndSeparated using (ℕ-is-set)
open import UF.Powerset-MultiUniverse
open import UF.Sets using (is-set)

open import EffectfulForcing.MFPSAndVariations.Dialogue
 using (eloquent)

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.BrouwersThesis fe A

import InductiveBars.Continuity
open InductiveBars.Continuity fe A ℕ ℕ-is-set

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

bar-depth : (V : 𝓟 {𝓥} (List A))
          → is-inductive-bar V
          → (ℕ → A) → ℕ
bar-depth V (base v) α = 0
bar-depth V (step φ) α = succ (bar-depth _ (φ (α 0)) (α ∘ succ))

bar-depth-spec : (V : 𝓟 {𝓥} (List A)) (b : is-inductive-bar V)
               → (α : ℕ → A)
               → prefix (bar-depth V b α) α ∈ V
bar-depth-spec V (base v) α = v
bar-depth-spec V (step φ) α = bar-depth-spec _ (φ (α 0)) (α ∘ succ)

\end{code}

For every witness b that V is an inductive bar, the function `bar-depth V b`
is bar continuous.

\begin{code}

bar-depth-is-bar-continuous
 : (V : 𝓟 {𝓥} (List A)) (b : is-inductive-bar V)
 → is-bar-continuous (bar-depth V b)
bar-depth-is-bar-continuous V (base v) = base (λ _ _ _ _ → refl)
bar-depth-is-bar-continuous V (step φ) = step ψ
 where
  μ : A → (ℕ → A) → ℕ
  μ a = bar-depth (section₁ V a) (φ a)
  W : 𝓟 (List A)
  W = determining-prefixes (bar-depth V (step φ))
  ihs : (a : A) → is-inductive-bar (determining-prefixes (μ a))
  ihs a = bar-depth-is-bar-continuous (section₁ V a) (φ a)
  θ : (a : A) → determining-prefixes (μ a) ⊆ section₁ W a
  θ a s d α β (pα , eα) (pβ , eβ) = goal
   where
    e₀ : μ (α 0) (α ∘ succ) ＝ μ a (α ∘ succ)
    e₀ = ap (λ i → μ i (α ∘ succ)) pα
    e₁ : μ a (α ∘ succ) ＝ μ a (β ∘ succ)
    e₁ = d (α ∘ succ) (β ∘ succ) eα eβ
    e₂ : μ (β 0) (β ∘ succ) ＝ μ a (β ∘ succ)
    e₂ = ap (λ i → μ i (β ∘ succ)) pβ
    goal : succ (μ (α 0) (α ∘ succ)) ＝ succ (μ (β 0) (β ∘ succ))
    goal = ap succ (e₀ ∙ e₁ ∙ e₂ ⁻¹)
  ψ : (a : A) → is-inductive-bar (section₁ W a)
  ψ a = inductive-bar-respects-inclusion _ _ (θ a) (ihs a)

\end{code}

Moreover, the function `bar-depth V b` is a modulus of itself.

\begin{code}

_is-a-modulus-of-continuity-of_
 : {𝓦 : Universe} {B : 𝓦 ̇}
 → ((ℕ → A) → ℕ)
 → ((ℕ → A) → B)
 → 𝓤 ⊔ 𝓦 ̇
M is-a-modulus-of-continuity-of f = (α β : ℕ → A) → α ＝⦅ M α ⦆ β → f α ＝ f β

bar-depth-is-self-modulating
 : (V : 𝓟 {𝓥} (List A)) (b : is-inductive-bar V)
 → (bar-depth V b) is-a-modulus-of-continuity-of (bar-depth V b)
bar-depth-is-self-modulating V (base v) α β em = refl
bar-depth-is-self-modulating V (step φ) α β (e₀ , em) = ap succ e
 where
  ih : bar-depth (section₁ V (α 0)) (φ (α 0)) (α ∘ succ) ＝
       bar-depth (section₁ V (α 0)) (φ (α 0)) (β ∘ succ)
  ih = bar-depth-is-self-modulating _ (φ (α 0)) (α ∘ succ) (β ∘ succ) em
  e : bar-depth (section₁ V (α 0)) (φ (α 0)) (α ∘ succ) ＝
      bar-depth (section₁ V (β 0)) (φ (β 0)) (β ∘ succ)
  e = ih ∙ ap (λ n → bar-depth (section₁ V n) (φ n) (β ∘ succ)) e₀

\end{code}

The bar-depth function of the inductive bar of determining prefixes of f
is a self-modulating, bar-continuous modulus of pointwise continuity of f.

\begin{code}

module _ {𝓦 : Universe}
         (R : 𝓦 ̇)
         (R-is-set : is-set R)
 where

 module 𝐑 = InductiveBars.Continuity fe A R R-is-set
 open 𝐑 using ()
  renaming
   ( is-bar-continuous to is-bar-continuousᴿ
   ; determining-prefixes to determining-prefixesᴿ
   ; _determines_ to _determinesᴿ_
   )

 modulus-gives-bar-witness
  : (f : (ℕ → A) → R) (M : (ℕ → A) → ℕ)
  → M is-a-modulus-of-continuity-of f
  → (α : ℕ → A) → (prefix (M α) α) determinesᴿ f
 modulus-gives-bar-witness f M mod α β γ eβ eγ = e₀ ⁻¹ ∙ e₁
  where
   e₀ : f α ＝ f β
   e₀ = mod α β (extends-prefix-implies-agreement α β (M α) eβ)
   e₁ : f α ＝ f γ
   e₁ = mod α γ (extends-prefix-implies-agreement α γ (M α) eγ)

 bar-witness-gives-modulus
  : (f : (ℕ → A) → R) (M : (ℕ → A) → ℕ)
  → ((α : ℕ → A) → (prefix (M α) α) determinesᴿ f)
  → M is-a-modulus-of-continuity-of f
 bar-witness-gives-modulus f M det α β eM = det α α β eα eβ
  where
   eα : α extends (prefix (M α) α)
   eα = extends-prefix α (M α)
   eβ : β extends (prefix (M α) α)
   eβ = agreement-implies-extends-prefix α β (M α) eM

 modulus-iff-bar-witness
  : (f : (ℕ → A) → R) (M : (ℕ → A) → ℕ)
  → (M is-a-modulus-of-continuity-of f) ↔
    ((α : ℕ → A) → prefix (M α) α determinesᴿ f)
 modulus-iff-bar-witness f M
  = modulus-gives-bar-witness f M , bar-witness-gives-modulus f M

 bar-continuity-gives-self-modulating-bar-continuous-modulus
  : (f : (ℕ → A) → R)
  → is-bar-continuousᴿ f
  → Σ M ꞉ ((ℕ → A) → ℕ) ,
        is-bar-continuous M
      × M is-a-modulus-of-continuity-of M
      × M is-a-modulus-of-continuity-of f
 bar-continuity-gives-self-modulating-bar-continuous-modulus f bcf
  = M , bcM , mM , mf
  where
   M : (ℕ → A) → ℕ
   M = bar-depth (determining-prefixesᴿ f) bcf
   bcM : is-bar-continuous M
   bcM = bar-depth-is-bar-continuous (determining-prefixesᴿ f) bcf
   mM : M is-a-modulus-of-continuity-of M
   mM = bar-depth-is-self-modulating (determining-prefixesᴿ f) bcf
   mf : M is-a-modulus-of-continuity-of f
   mf = bar-witness-gives-modulus f M det
    where
     det : (α : ℕ → A) → prefix (M α) α determinesᴿ f
     det = bar-depth-spec (determining-prefixesᴿ f) bcf

\end{code}

Conversely, if M is a modulus of continuity of f, then prefix (M α) α
determines f for every α.  If M is bar continuous, then Brouwer's thesis for
bar-continuous witnesses makes the determining prefixes of f an inductive bar.

\begin{code}

 bar-continuous-modulus-gives-bar-continuity
  : (f : (ℕ → A) → R)
  → (M : (ℕ → A) → ℕ)
  → is-bar-continuous M
  → M is-a-modulus-of-continuity-of f
  → is-bar-continuousᴿ f
 bar-continuous-modulus-gives-bar-continuity f M bcM mod
  = brouwers-thesis-for-bar-continuous-witnesses _ m M bcM wit
  where
   m : is-monotone (determining-prefixesᴿ f)
   m = 𝐑.determining-prefixes-is-monotone f
   wit : (α : ℕ → A) → prefix (M α) α determinesᴿ f
   wit = modulus-gives-bar-witness f M mod

\end{code}

Therefore, a function is bar continuous iff it has a self-modulating,
bar-continuous modulus of continuity.

\begin{code}

 bar-continuity-iff-self-modulating-bar-continuous-modulus
  : (f : (ℕ → A) → R)
  →  is-bar-continuousᴿ f ↔
    (Σ M ꞉ ((ℕ → A) → ℕ) ,
         is-bar-continuous M
       × M is-a-modulus-of-continuity-of M
       × M is-a-modulus-of-continuity-of f)
 bar-continuity-iff-self-modulating-bar-continuous-modulus f
  = bar-continuity-gives-self-modulating-bar-continuous-modulus f
  , λ { (M , bcM , _ , mf) →
           bar-continuous-modulus-gives-bar-continuity f M bcM mf }

\end{code}

Because bar continuity is logically equivalent to eloquence, we have the
corresponding characterization of eloquence: a function is eloquent iff
it has a self-modulating, eloquent modulus of continuity.

\begin{code}

 eloquence-gives-self-modulating-eloquent-modulus
  : (f : (ℕ → A) → R)
  → eloquent f
  → Σ M ꞉ ((ℕ → A) → ℕ) ,
        eloquent M
      × M is-a-modulus-of-continuity-of M
      × M is-a-modulus-of-continuity-of f
 eloquence-gives-self-modulating-eloquent-modulus f ef
  using (M , bcM , mM , mf) ←
    bar-continuity-gives-self-modulating-bar-continuous-modulus f
      (𝐑.eloquence-implies-bar-continuity f ef)
  = M , bar-continuity-implies-eloquence M bcM , mM , mf

 eloquent-modulus-gives-eloquence
  : (f : (ℕ → A) → R)
  → (M : (ℕ → A) → ℕ)
  → eloquent M
  → M is-a-modulus-of-continuity-of f
  → eloquent f
 eloquent-modulus-gives-eloquence f M eM mod
  = 𝐑.bar-continuity-implies-eloquence f
     (bar-continuous-modulus-gives-bar-continuity f
       M (eloquence-implies-bar-continuity M eM) mod)

 eloquence-iff-self-modulating-eloquent-modulus
  : (f : (ℕ → A) → R)
  →  eloquent f ↔
    (Σ M ꞉ ((ℕ → A) → ℕ) ,
         eloquent M
       × M is-a-modulus-of-continuity-of M
       × M is-a-modulus-of-continuity-of f)
 eloquence-iff-self-modulating-eloquent-modulus f
  = eloquence-gives-self-modulating-eloquent-modulus f
  , λ { (M , eM , _ , mf) → eloquent-modulus-gives-eloquence f M eM mf }

\end{code}
