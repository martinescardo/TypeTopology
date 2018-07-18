By Martin Escardo, 2 September 2011.

Modified in December 2011 assuming the axiom of extensionality (which
is not used directly in this module, but instead in
GenericConvergentSequence).

We prove that the generic convergent sequence ℕ∞ is searchable, which
amounts to Theorem-3·6 of the paper

   http://www.cs.bham.ac.uk/~mhe/papers/omniscient.pdf,
   http://www.cs.bham.ac.uk/~mhe/.talks/dagstuhl2011/omniscient.pdf

and conclude as a corollary that it is searchable and satisfies the
principle of omniscience.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}


(Continuity axioms and the fan principle are not assumed.)

\begin{code}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc
open import GenericConvergentSequence
open import SearchableTypes

module ConvergentSequenceSearchable (fe : funext U₀ U₀) where

\end{code}

This is the main theorem proved in this module:

\begin{code}

ℕ∞-searchable : searchable ℕ∞
ℕ∞-searchable p = a , Lemma
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
  Claim₁ r = not-ℕ-is-∞ fe (Claim₀ r)

  Claim₂ : p a ≡ ₁ → (n : ℕ) → p(under n) ≡ ₁
  Claim₂ r = Dagger₁(Claim₁ r)

  Claim₃ : p a ≡ ₁ → p ∞ ≡ ₁
  Claim₃ r = (ap p (Claim₁ r))⁻¹ ∙ r

  Lemma : p a ≡ ₁ → (v : ℕ∞) → p v ≡ ₁
  Lemma r = ℕ∞-𝟚-density fe (Claim₂ r) (Claim₃ r)

\end{code}

Corollaries:

\begin{code}

open import OmniscientTypes
open import DiscreteAndSeparated

ℕ∞-omniscient : omniscient ℕ∞
ℕ∞-omniscient = searchable-implies-omniscient (ℕ∞-searchable)

ℕ∞→ℕ-discrete : discrete(ℕ∞ → ℕ)
ℕ∞→ℕ-discrete = omniscient-discrete-discrete fe ℕ∞-omniscient (λ u → ℕ-discrete)

ℕ∞→𝟚-discrete : discrete(ℕ∞ → 𝟚)
ℕ∞→𝟚-discrete = omniscient-discrete-discrete fe ℕ∞-omniscient (λ u → 𝟚-discrete)

module _ (fe' : ∀ U V → funext U V) (pt : PropTrunc) where

 open import 2CompactTypes (fe') (pt)

 ℕ∞-is-strongly-𝟚-overt : strongly-𝟚-overt ℕ∞
 ℕ∞-is-strongly-𝟚-overt = omniscient-Compact ℕ∞-omniscient

 ℕ∞-is-𝟚-compact : 𝟚-compact ℕ∞
 ℕ∞-is-𝟚-compact = 𝟚-so-c ℕ∞-is-strongly-𝟚-overt

\end{code}
