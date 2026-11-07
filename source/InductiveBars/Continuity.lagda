Chuangjie Xu, November 2026

We say a function from Baire space to natural numbers is bar continuous
if the finite sequences determining its values form an inductive bar.

In this module, we prove:
(1) Bar continuity implies pointwise continuity.
(2) Bar continuity implies uniform continuity on every pointwise bounded
    subset of Baire space.
(3) Bar continuity is logically equivalent to eloquence.

As a corollary of (3), all System T-definable functions (ℕ → ℕ) → ℕ are
bar continuous.

TODO: Relate bar continuity to formal continuity as studied by Kawai.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import UF.FunExt using (Fun-Ext)

module InductiveBars.Continuity (fe : Fun-Ext) where

open import MLTT.Spartan
open import MLTT.List
open import UF.Powerset
open import UF.Subsingletons using (is-prop)
open import UF.Subsingletons-FunExt using (Π₄-is-prop)
open import UF.DiscreteAndSeparated using (ℕ-is-set)
open import Naturals.Order

open import InductiveBars.Sequences
open import InductiveBars.Basics

open import EffectfulForcing.MFPSAndVariations.SystemT
 using (T-definable)
open import EffectfulForcing.MFPSAndVariations.LambdaCalculusVersionOfMFPS
 using (eloquence-theorem)

\end{code}

A finite sequence determines f : (ℕ → ℕ) → ℕ if f has the same value on
all inputs extending that sequence.

We define `determining-prefixes f` to denote the set of finite sequences
that determine f.

\begin{code}

_determines_ : (List ℕ) → ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
s determines f = (α β : ℕ → ℕ) → α extends s → β extends s → f α ＝ f β

determines-is-prop : (s : List ℕ) (f : (ℕ → ℕ) → ℕ)
                   → is-prop (s determines f)
determines-is-prop s f = Π₄-is-prop fe (λ _ _ _ _ → ℕ-is-set)

determining-prefixes : ((ℕ → ℕ) → ℕ) → 𝓟 (List ℕ)
determining-prefixes f s = (s determines f) , determines-is-prop s f

determining-prefixes-is-monotone
 : (f : (ℕ → ℕ) → ℕ) → is-monotone (determining-prefixes f)
determining-prefixes-is-monotone f s t ds α β eα eβ
 = ds α β (extends-++ α s t eα) (extends-++ β s t eβ)

\end{code}

A function f : (ℕ → ℕ) → ℕ is bar continuous if its determining prefixes
form an inductive bar.

Because we have logically equivalent formulations of inductive bars, we have
the following logically equivalent notions of bar continuity.

\begin{code}

is-bar-continuous : ((ℕ → ℕ) → ℕ) → 𝓤₁ ̇
is-bar-continuous f = is-inductive-bar (determining-prefixes f)

is-bar-continuous′ : ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
is-bar-continuous′ f = (determining-prefixes f) bars []

is-bar-continuous″ : ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
is-bar-continuous″ f = (s : List ℕ) → (determining-prefixes f) bars s

bar-continuity″-implies-bar-continuity′
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous″ f → is-bar-continuous′ f
bar-continuity″-implies-bar-continuity′ f bc = bc []

bar-continuity′-implies-bar-continuity
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous′ f → is-bar-continuous f
bar-continuity′-implies-bar-continuity f
 = bars-root-implies-inductive-bar (determining-prefixes f)

bar-continuity-implies-bar-continuity″
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous f → is-bar-continuous″ f
bar-continuity-implies-bar-continuity″ f
 = monotone-inductive-bar-bars-all
    (determining-prefixes f)
    (determining-prefixes-is-monotone f)

bar-continuity-extensional
 : (f g : (ℕ → ℕ) → ℕ)
 → f ∼ g
 → is-bar-continuous f
 → is-bar-continuous g
bar-continuity-extensional f g e =
 inductive-bar-respects-inclusion
  (determining-prefixes f)
  (determining-prefixes g)
  θ
 where
  θ : determining-prefixes f ⊆ determining-prefixes g
  θ s p α β αs βs = (e α) ⁻¹ ∙ p α β αs βs ∙ e β

\end{code}

Bar continuity implies pointwise continuity.

\begin{code}

is-pointwise-continuous : ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
is-pointwise-continuous f
 = (α : ℕ → ℕ) → Σ m ꞉ ℕ , ((β : ℕ → ℕ) → α ＝⦅ m ⦆ β → f α ＝ f β)

bar-continuity-implies-pointwise-continuity
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous f → is-pointwise-continuous f
bar-continuity-implies-pointwise-continuity f bc α
 using (s , eαs , det) ←
   inductive-bar-meets-every-sequence (determining-prefixes f) bc α
 = n , correct
 where
  n : ℕ
  n = length s
  correct : (β : ℕ → ℕ) → α ＝⦅ n ⦆ β → f α ＝ f β
  correct β en = det α β eαs (agreement-preserves-extension α β s eαs en)

\end{code}

Bar continuity implies uniform continuity on every pointwise bounded subset
of the Baire space.

\begin{code}

is-uniformly-continuous : ((ℕ → ℕ) → ℕ) → 𝓤₀ ̇
is-uniformly-continuous f
 = (δ : ℕ → ℕ)
 → Σ m ꞉ ℕ , ((α β : ℕ → ℕ) → α ≤¹ δ → β ≤¹ δ → α ＝⦅ m ⦆ β → f α ＝ f β)

bar-continuity-implies-uniform-continuity
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous f → is-uniformly-continuous f
bar-continuity-implies-uniform-continuity f bc δ = m , correct
 where
  fact : Σ m ꞉ ℕ ,
          ((α : ℕ → ℕ) → α ≤¹ δ
           → Σ s ꞉ List ℕ , (length s ≤ℕ m) × (α extends s) × (s determines f))
  fact = inductive-bar-meets-bounded-sequences-uniformly
          (determining-prefixes f) bc δ
  m : ℕ
  m = pr₁ fact
  correct : (α β : ℕ → ℕ) → α ≤¹ δ → β ≤¹ δ → α ＝⦅ m ⦆ β → f α ＝ f β
  correct α β rα _ em
   using (s , rs , eαs , det) ← pr₂ fact α rα
   = det α β eαs eβs
   where
    es : α ＝⦅ length s ⦆ β
    es = ＝⦅⦆-≤ α β rs em
    eβs : β extends s
    eβs = agreement-preserves-extension α β s eαs es

\end{code}

Bar continuity implies eloquence.

\begin{code}

open import EffectfulForcing.MFPSAndVariations.Dialogue

bar-continuity-implies-eloquence
 : (f : (ℕ → ℕ) → ℕ)
 → is-bar-continuous f → eloquent f
bar-continuity-implies-eloquence f bc = d' , correct
 where
  value : List ℕ → ℕ
  value s = f (pad s)
  fact : Σ d ꞉ B (List ℕ) ,
          ((α : ℕ → ℕ)
           → (α extends (dialogue d α)) × (dialogue d α) determines f)
  fact = inductive-bar-gives-dialogue (determining-prefixes f) bc
  d : B (List ℕ)
  d = pr₁ fact
  d' : B ℕ
  d' = B-functor value d
  correct : (α : ℕ → ℕ) → dialogue d' α ＝ f α
  correct α
   using (eαs , det) ← pr₂ fact α
   = e₀ ⁻¹ ∙ e₁
   where
    s : List ℕ
    s = dialogue d α
    e₀ : value s ＝ dialogue d' α
    e₀ = decode-α-is-natural value d α
    e₁ : value s ＝ f α
    e₁ = det (pad s) α (pad-extends s) eαs

\end{code}

Eloquence implies bar continuity.

\begin{code}

dialogue-gives-inductive-bar
 : (d : B ℕ)
 → is-inductive-bar (determining-prefixes (dialogue d))
dialogue-gives-inductive-bar (η n) = base (λ _ _ _ _ → refl)
dialogue-gives-inductive-bar (β φ i) = fact
 where
  V : 𝓟 (List ℕ)
  V = determining-prefixes (dialogue (β φ i))
  claim : (s : List ℕ) → length s ＝ succ i → is-inductive-bar (section V s)
  claim s e = inductive-bar-respects-inclusion (section W s) (section V s) θ b
   where
    r : i <ℕ length s
    r = transport (i <ℕ_) (e ⁻¹) (≤-refl i)
    n : ℕ
    n = lookup s r
    W : 𝓟 (List ℕ)
    W = determining-prefixes (dialogue (φ n))
    mW : is-monotone W
    mW = determining-prefixes-is-monotone (dialogue (φ n))
    ih : is-inductive-bar W
    ih = dialogue-gives-inductive-bar (φ n)
    b : is-inductive-bar (section W s)
    b = monotone-inductive-bar-sections W mW ih s
    θ : section W s ⊆ section V s
    θ t p α α' eα eα' = e₀ ∙ e₁ ∙ e₂ ⁻¹
     where
      e₀ : dialogue (β φ i) α ＝ dialogue (φ n) α
      e₀ = ap (λ j → dialogue (φ j) α)
              (extends-lookup s i r α (extends-++ α s t eα))
      e₁ : dialogue (φ n) α ＝ dialogue (φ n) α'
      e₁ = p α α' eα eα'
      e₂ : dialogue (β φ i) α' ＝ dialogue (φ n) α'
      e₂ = ap (λ j → dialogue (φ j) α')
              (extends-lookup s i r α' (extends-++ α' s t eα'))
  fact : is-inductive-bar V
  fact = inductive-bar-from-sections V (succ i) claim

eloquence-implies-bar-continuity
 : (f : (ℕ → ℕ) → ℕ)
 → eloquent f → is-bar-continuous f
eloquence-implies-bar-continuity f (d , spec) = goal
 where
  fact : is-bar-continuous (dialogue d)
  fact = dialogue-gives-inductive-bar d
  goal : is-inductive-bar (determining-prefixes f)
  goal = bar-continuity-extensional (dialogue d) f spec fact

\end{code}

Every System T-definable function of type (ℕ → ℕ) → ℕ is eloquent and
thus bar continuous.

\begin{code}

T-definable-functions-are-bar-continuous
 : (f : (ℕ → ℕ) → ℕ)
 → T-definable f
 → is-bar-continuous f
T-definable-functions-are-bar-continuous f t
 = eloquence-implies-bar-continuity f (eloquence-theorem f t)

\end{code}
