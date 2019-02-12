By Martin Escardo, 2 September 2011.

Modified in December 2011 assuming the axiom of extensionality (which
is not used directly in this module, but instead in
GenericConvergentSequence).

We prove that the generic convergent sequence ℕ∞ is compact, which
amounts to Theorem-3·6 of the paper

   http://www.cs.bham.ac.uk/~mhe/papers/omniscient.pdf,
   http://www.cs.bham.ac.uk/~mhe/.talks/dagstuhl2011/omniscient.pdf

(Continuity axioms and the fan principle are not assumed.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module ConvergentSequenceCompact (fe : funext 𝓤₀ 𝓤₀) where

open import Negation
open import Two-Properties
open import UF-PropTrunc
open import GenericConvergentSequence
open import CompactTypes
open import DiscreteAndSeparated

\end{code}

This is the main theorem proved in this module:

\begin{code}

ℕ∞-compact∙ : compact∙ ℕ∞
ℕ∞-compact∙ p = a , Lemma
 where
  α : ℕ → 𝟚
  α 0       = p(under 0)
  α(succ n) = min𝟚 (α n) (p(under(succ n)))

  a : ℕ∞
  a = (α , λ i → Lemma[minab≤₂a])

  Dagger₀ : (n : ℕ) → a ≡ under n → p(under n) ≡ ₀
  Dagger₀ 0 r =  ap (λ - → incl - 0) r
  Dagger₀ (succ n) r = w ⁻¹ ∙ t ∙ under-diagonal₀ n
   where
    s : α n ≡ incl (under (succ n)) n
    s = ap (λ - → incl - n) r

    t : α(succ n) ≡ incl (under (succ n)) (succ n)
    t = ap (λ - → incl - (succ n)) r

    w : α(succ n) ≡ p(under(succ n))
    w = ap (λ - → min𝟚 - (p(under(succ n)))) (s  ∙ under-diagonal₁ n)

  Dagger₁ : a ≡ ∞ → (n : ℕ) → p(under n) ≡ ₁
  Dagger₁ r 0 = ap (λ - → incl - 0) r
  Dagger₁ r (succ n) = w ⁻¹ ∙ t
   where
    s : α n ≡ ₁
    s = ap (λ - → incl - n) r

    t : α(succ n) ≡ ₁
    t = ap (λ - → incl - (succ n)) r

    w : α(succ n) ≡ p(under(succ n))
    w = ap (λ - → min𝟚 - (p(under(succ n)))) s

  Claim₀ : p a ≡ ₁ → (n : ℕ) → a ≢ under n
  Claim₀ r n s = Lemma[b≡₁→b≢₀] r (Lemma s)
   where
    Lemma : a ≡ under n → p a ≡ ₀
    Lemma t = ap p t ∙ Dagger₀ n t

  Claim₁ : p a ≡ ₁ → a ≡ ∞
  Claim₁ r = not-finite-is-∞ fe (Claim₀ r)

  Claim₂ : p a ≡ ₁ → (n : ℕ) → p(under n) ≡ ₁
  Claim₂ r = Dagger₁(Claim₁ r)

  Claim₃ : p a ≡ ₁ → p ∞ ≡ ₁
  Claim₃ r = (ap p (Claim₁ r))⁻¹ ∙ r

  Lemma : p a ≡ ₁ → (v : ℕ∞) → p v ≡ ₁
  Lemma r = ℕ∞-𝟚-density fe (Claim₂ r) (Claim₃ r)

\end{code}

Corollaries:

\begin{code}

ℕ∞-compact : compact ℕ∞
ℕ∞-compact = compact∙-gives-compact (ℕ∞-compact∙)

ℕ∞→ℕ-is-discrete : is-discrete(ℕ∞ → ℕ)
ℕ∞→ℕ-is-discrete = compact-discrete-discrete fe ℕ∞-compact (λ u → ℕ-is-discrete)

ℕ∞→𝟚-is-discrete : is-discrete(ℕ∞ → 𝟚)
ℕ∞→𝟚-is-discrete = compact-discrete-discrete fe ℕ∞-compact (λ u → 𝟚-is-discrete)

module _ (fe' : FunExt) (pt : propositional-truncations-exist) where

 open import WeaklyCompactTypes fe' pt

 ℕ∞-is-∃-compact : ∃-compact ℕ∞
 ℕ∞-is-∃-compact = compact-gives-∃-compact ℕ∞-compact

 ℕ∞-is-Π-compact : Π-compact ℕ∞
 ℕ∞-is-Π-compact = ∃-compact-gives-Π-compact ℕ∞-is-∃-compact

\end{code}
