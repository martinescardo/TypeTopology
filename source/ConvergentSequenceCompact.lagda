By Martin Escardo, 2 September 2011.

Modified in December 2011 assuming function extensionality (which is
not used directly in this module, but instead in
GenericConvergentSequence).

We prove that the generic convergent sequence ℕ∞ is compact, which
amounts to Theorem-3·6 of the paper

   https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf
   http://www.cs.bham.ac.uk/~mhe/.talks/dagstuhl2011/omniscient.pdf

(Continuity axioms and the fan principle are not assumed.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module ConvergentSequenceCompact (fe : funext 𝓤₀ 𝓤₀) where

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
  α 0       = p (under 0)
  α(succ n) = min𝟚 (α n) (p (under(succ n)))

  d' : (n : ℕ) → min𝟚 (α n) (p (under(succ n))) ≡ ₁ → α n ≡ ₁
  d' n = Lemma[minab≤₂a] {α n}

  d : is-decreasing α
  d = d'

  a : ℕ∞
  a = (α , d)

  Dagger₀ : (n : ℕ) → a ≡ under n → p (under n) ≡ ₀
  Dagger₀ 0 r =  p (under 0)      ≡⟨ refl ⟩
                 α 0              ≡⟨ ap (λ - → incl - 0) r ⟩
                 incl (under 0) 0 ≡⟨ refl ⟩
                 ₀                ∎

  Dagger₀ (succ n) r = p (under (succ n))             ≡⟨ w ⁻¹ ⟩
                       α (succ n)                     ≡⟨ ap (λ - → incl - (succ n)) r ⟩
                       incl (under (succ n)) (succ n) ≡⟨ under-diagonal₀ n ⟩
                       ₀                              ∎
   where
    t : α n ≡ ₁
    t = α n                     ≡⟨ ap (λ - → incl - n) r  ⟩
        incl (under (succ n)) n ≡⟨ under-diagonal₁ n ⟩
        ₁                       ∎

    w : α(succ n) ≡ p (under(succ n))
    w = α (succ n)                  ≡⟨ ap (λ - → min𝟚 - (p (under(succ n)))) t ⟩
        min𝟚 ₁ (p (under (succ n))) ≡⟨ refl ⟩
        p (under(succ n))           ∎

  Dagger₁ : a ≡ ∞ → (n : ℕ) → p (under n) ≡ ₁
  Dagger₁ r 0 = p (under 0) ≡⟨ refl ⟩
                α 0         ≡⟨ ap (λ - → incl - 0) r ⟩
                incl ∞ 0    ≡⟨ refl ⟩
                ₁           ∎
  Dagger₁ r (succ n) = p (under (succ n)) ≡⟨ w ⁻¹ ⟩
                       α (succ n)         ≡⟨ ap (λ - → incl - (succ n)) r ⟩
                       incl ∞ (succ n)    ≡⟨ refl ⟩
                       ₁                  ∎
   where
    s : α n ≡ ₁
    s = ap (λ - → incl - n) r

    w : α(succ n) ≡ p (under(succ n))
    w = α (succ n)                  ≡⟨ ap (λ - → min𝟚 - (p (under(succ n)))) s ⟩
        min𝟚 ₁ (p (under (succ n))) ≡⟨ refl ⟩
        p (under (succ n))          ∎

  Claim₀ : p a ≡ ₁ → (n : ℕ) → a ≢ under n
  Claim₀ r n s = equal-₁-different-from-₀ r (Lemma s)
   where
    Lemma : a ≡ under n → p a ≡ ₀
    Lemma t = p a         ≡⟨ ap p t ⟩
              p (under n) ≡⟨ Dagger₀ n t ⟩
              ₀           ∎

  Claim₁ : p a ≡ ₁ → a ≡ ∞
  Claim₁ r = not-finite-is-∞ fe (Claim₀ r)

  Claim₂ : p a ≡ ₁ → (n : ℕ) → p (under n) ≡ ₁
  Claim₂ r = Dagger₁(Claim₁ r)

  Claim₃ : p a ≡ ₁ → p ∞ ≡ ₁
  Claim₃ r = p ∞ ≡⟨ (ap p (Claim₁ r))⁻¹ ⟩
             p a ≡⟨ r ⟩
             ₁   ∎

  Lemma : p a ≡ ₁ → (v : ℕ∞) → p v ≡ ₁
  Lemma r = ℕ∞-𝟚-density fe (Claim₂ r) (Claim₃ r)

\end{code}

Corollaries:

\begin{code}

ℕ∞-compact : compact ℕ∞
ℕ∞-compact = compact∙-gives-compact ℕ∞-compact∙

ℕ∞-Compact : Compact ℕ∞ {𝓤}
ℕ∞-Compact = compact-gives-Compact ℕ∞ ℕ∞-compact

ℕ∞→ℕ-is-discrete : is-discrete(ℕ∞ → ℕ)
ℕ∞→ℕ-is-discrete = compact-discrete-discrete fe ℕ∞-compact (λ u → ℕ-is-discrete)

ℕ∞→𝟚-is-discrete : is-discrete(ℕ∞ → 𝟚)
ℕ∞→𝟚-is-discrete = compact-discrete-discrete fe ℕ∞-compact (λ u → 𝟚-is-discrete)

module _ (fe' : FunExt) (pt : propositional-truncations-exist) where

 open import WeaklyCompactTypes fe' pt

 ℕ∞-is-∃-compact : ∃-compact ℕ∞
 ℕ∞-is-∃-compact = compact-types-are-∃-compact ℕ∞-compact

 ℕ∞-is-Π-compact : Π-compact ℕ∞
 ℕ∞-is-Π-compact = ∃-compact-gives-Π-compact ℕ∞-is-∃-compact

\end{code}
