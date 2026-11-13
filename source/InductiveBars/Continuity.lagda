Chuangjie Xu, November 2026

We say a function of type (ℕ → A) → R is bar continuous if the
finite sequences determining its values form an inductive bar.
We prove that bar continuity is logically equivalent to eloquence.

TODO. Relate bar continuity to formal continuity as studied by
Tatsuji Kawai in "Formally continuous functions on Baire space"
(Mathematical Logic Quarterly 64(3):192-200, 2018).

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan hiding (𝓤 ; 𝓥)

module InductiveBars.Continuity
 {𝓤 𝓥 : Universe}
 (A : 𝓤 ̇)
 (R : 𝓥 ̇)
 where

open import MLTT.List
open import Naturals.Order

open import InductiveBars.Sequences
open import InductiveBars.Basics

\end{code}

A finite sequence determines f : (ℕ → A) → R if f has the same value on
all inputs extending that sequence.

\begin{code}

_determines_ : (List A) → ((ℕ → A) → R) → 𝓤 ⊔ 𝓥 ̇
s determines f = (α β : ℕ → A) → α extends s → β extends s → f α ＝ f β

determining-prefixes : ((ℕ → A) → R) → List A → 𝓤 ⊔ 𝓥 ̇
determining-prefixes f s = s determines f

determining-prefixes-is-monotone
 : (f : (ℕ → A) → R) → is-monotone (determining-prefixes f)
determining-prefixes-is-monotone f s t ds α β eα eβ
 = ds α β (extends-++ α s t eα) (extends-++ β s t eβ)

\end{code}

A function f : (ℕ → A) → R is bar continuous if its determining prefixes
form an inductive bar.

Because we have logically equivalent formulations of inductive bars, we have
the following logically equivalent notions of bar continuity.

\begin{code}

is-bar-continuous : ((ℕ → A) → R) → (𝓤 ⊔ 𝓥) ⁺ ̇
is-bar-continuous f = is-inductive-bar (determining-prefixes f)

is-bar-continuous′ : ((ℕ → A) → R) → 𝓤 ⊔ 𝓥 ̇
is-bar-continuous′ f = (determining-prefixes f) bars []

is-bar-continuous″ : ((ℕ → A) → R) → 𝓤 ⊔ 𝓥 ̇
is-bar-continuous″ f = (s : List A) → (determining-prefixes f) bars s

bar-continuity″-implies-bar-continuity′
 : (f : (ℕ → A) → R)
 → is-bar-continuous″ f → is-bar-continuous′ f
bar-continuity″-implies-bar-continuity′ f bc = bc []

bar-continuity′-implies-bar-continuity
 : (f : (ℕ → A) → R)
 → is-bar-continuous′ f → is-bar-continuous f
bar-continuity′-implies-bar-continuity f
 = bars-root-implies-inductive-bar (determining-prefixes f)

bar-continuity-implies-bar-continuity″
 : (f : (ℕ → A) → R)
 → is-bar-continuous f → is-bar-continuous″ f
bar-continuity-implies-bar-continuity″ f
 = monotone-inductive-bar-bars-all
    (determining-prefixes f)
    (determining-prefixes-is-monotone f)

bar-continuity-extensional
 : (f g : (ℕ → A) → R)
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

Bar continuity implies eloquence.

\begin{code}

open import EffectfulForcing.MFPSAndVariations.Dialogue

determining-prefix-bar-gives-dialogue
 : (f : (ℕ → A) → R) (s : List A)
 → (determining-prefixes f) bars s
 → Σ d ꞉ D ℕ A R , ((α : ℕ → A) → α extends s → f α ＝ dialogue d α)
determining-prefix-bar-gives-dialogue f s (hit v) = d , correct
 where
  d : D ℕ A R
  d = β (λ a → η (f (pad-with a s))) 0
  correct : (α : ℕ → A) → α extends s → f α ＝ dialogue d α
  correct α e = v α (pad-with (α 0) s) e (pad-extends s)
determining-prefix-bar-gives-dialogue f s (step φ) = d , correct
 where
  ihs : (a : A)
      → Σ d ꞉ D ℕ A R , (∀ α → α extends (s ++ [ a ]) → f α ＝ dialogue d α)
  ihs a = determining-prefix-bar-gives-dialogue f (s ++ [ a ]) (φ a)
  d : D ℕ A R
  d = β (λ a → pr₁ (ihs a)) (length s)
  correct : (α : ℕ → A) → α extends s → f α ＝ dialogue d α
  correct α e = pr₂ (ihs (α (length s))) α (extends-next α s e)

bar-continuity-implies-eloquence
 : (f : (ℕ → A) → R)
 → is-bar-continuous f → eloquent f
bar-continuity-implies-eloquence f bc
 using b ← inductive-bar-implies-bars-root (determining-prefixes f) bc
     | (d , spec) ← determining-prefix-bar-gives-dialogue f [] b
 = d , λ α → (spec α ⋆) ⁻¹

\end{code}

Eloquence implies bar continuity.

\begin{code}

dialogue-gives-inductive-bar
 : (d : D ℕ A R)
 → is-inductive-bar (determining-prefixes (dialogue d))
dialogue-gives-inductive-bar (η a) = base (λ _ _ _ _ → refl)
dialogue-gives-inductive-bar (β φ i) = fact
 where
  V : List A → 𝓤 ⊔ 𝓥 ̇
  V = determining-prefixes (dialogue (β φ i))
  claim : (s : List A) → length s ＝ succ i → is-inductive-bar (section V s)
  claim s e = inductive-bar-respects-inclusion (section W s) (section V s) θ b
   where
    r : i <ℕ length s
    r = transport (i <ℕ_) (e ⁻¹) (≤-refl i)
    a : A
    a = lookup s r
    W : List A → 𝓤 ⊔ 𝓥 ̇
    W = determining-prefixes (dialogue (φ a))
    mW : is-monotone W
    mW = determining-prefixes-is-monotone (dialogue (φ a))
    ih : is-inductive-bar W
    ih = dialogue-gives-inductive-bar (φ a)
    b : is-inductive-bar (section W s)
    b = monotone-inductive-bar-sections W mW ih s
    θ : section W s ⊆ section V s
    θ t p α α' eα eα' = e₀ ∙ e₁ ∙ e₂ ⁻¹
     where
      e₀ : dialogue (β φ i) α ＝ dialogue (φ a) α
      e₀ = ap (λ j → dialogue (φ j) α)
              (extends-lookup s i r α (extends-++ α s t eα))
      e₁ : dialogue (φ a) α ＝ dialogue (φ a) α'
      e₁ = p α α' eα eα'
      e₂ : dialogue (β φ i) α' ＝ dialogue (φ a) α'
      e₂ = ap (λ j → dialogue (φ j) α')
              (extends-lookup s i r α' (extends-++ α' s t eα'))
  fact : is-inductive-bar V
  fact = inductive-bar-from-sections V (succ i) claim

eloquence-implies-bar-continuity
 : (f : (ℕ → A) → R)
 → eloquent f → is-bar-continuous f
eloquence-implies-bar-continuity f (d , spec) = goal
 where
  fact : is-bar-continuous (dialogue d)
  fact = dialogue-gives-inductive-bar d
  goal : is-inductive-bar (determining-prefixes f)
  goal = bar-continuity-extensional (dialogue d) f spec fact

\end{code}

Therefore, bar continuity is logically equivalent to eloquence.

\begin{code}

bar-continuity-iff-eloquence
 : (f : (ℕ → A) → R)
 → is-bar-continuous f ↔ eloquent f
bar-continuity-iff-eloquence f
 = bar-continuity-implies-eloquence f
 , eloquence-implies-bar-continuity f

\end{code}
