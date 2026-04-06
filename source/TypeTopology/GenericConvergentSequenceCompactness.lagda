By Martin Escardo, 2 September 2011.

Modified in December 2011 assuming function extensionality (which is
not used directly in this module, but instead in
GenericConvergentSequence).

We prove that the generic convergent sequence ℕ∞ is compact, or
searchable, which amounts to Theorem-3·6 of the paper

   https://www.cs.bham.ac.uk/~mhe/papers/omniscient-journal-revised.pdf
   http://www.cs.bham.ac.uk/~mhe/.talks/dagstuhl2011/omniscient.pdf

(Continuity axioms and the fan principle are not assumed.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.GenericConvergentSequenceCompactness (fe : funext 𝓤₀ 𝓤₀) where

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import TypeTopology.CompactTypes
open import UF.DiscreteAndSeparated
open import UF.PropTrunc

\end{code}

We recall the main notions defined in the above imported modules:

\begin{code}

private
 module recall {X : 𝓤 ̇ } where

  recall₀ : is-compact∙ X
          ＝ (Π p ꞉ (X → 𝟚) , Σ x₀ ꞉ X , (p x₀ ＝ ₁ → Π x ꞉ X , p x ＝ ₁))

  recall₁ : is-compact  X
          ＝ (Π p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ＝ ₀) + (Π x ꞉ X , p x ＝ ₁))

  recall₂ : is-discrete X
          ＝ ((x y : X) → (x ＝ y) + (x ≠ y))

  recall₀ = by-definition
  recall₁ = by-definition
  recall₂ = by-definition

\end{code}

This is the main theorem proved in this module.

\begin{code}

ℕ∞-compact∙ : is-compact∙ ℕ∞
ℕ∞-compact∙ p = a , Lemma
 where
  α : ℕ → 𝟚
  α 0       = p (ι 0)
  α (succ n) = min𝟚 (α n) (p (ι (succ n)))

  d : is-decreasing α
  d n = Lemma[minab≤₂a] {α n}

  a : ℕ∞
  a = (α , d)

  Dagger₀ : (n : ℕ) → a ＝ ι n → p (ι n) ＝ ₀
  Dagger₀ 0 r =  p (ι 0)   ＝⟨refl⟩
                 α 0       ＝⟨ ap (λ - → ι - 0) r ⟩
                 ι (ι 0) 0 ＝⟨refl⟩
                 ₀         ∎
  Dagger₀ (succ n) r = p (ι (succ n))          ＝⟨ w ⁻¹ ⟩
                       α (succ n)              ＝⟨ ap (λ - → ι - (succ n)) r ⟩
                       ι (ι (succ n)) (succ n) ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
                       ₀                       ∎
   where
    t = α n              ＝⟨ ap (λ - → ι - n) r  ⟩
        ι (ι (succ n)) n ＝⟨ ℕ-to-ℕ∞-diagonal₁ n ⟩
        ₁                ∎

    w = α (succ n)              ＝⟨ ap (λ - → min𝟚 - (p (ι (succ n)))) t ⟩
        min𝟚 ₁ (p (ι (succ n))) ＝⟨refl⟩
        p (ι (succ n))          ∎

  Dagger₁ : a ＝ ∞ → (n : ℕ) → p (ι n) ＝ ₁
  Dagger₁ r 0 = p (ι 0) ＝⟨refl⟩
                α 0     ＝⟨ ap (λ - → ι - 0) r ⟩
                ι ∞ 0   ＝⟨refl⟩
                ₁       ∎
  Dagger₁ r (succ n) = p (ι (succ n)) ＝⟨ w ⁻¹ ⟩
                       α (succ n)     ＝⟨ ap (λ - → ι - (succ n)) r ⟩
                       ι ∞ (succ n)   ＝⟨refl⟩
                       ₁              ∎
   where
    s : α n ＝ ₁
    s = ap (λ - → ι - n) r

    w = α (succ n)              ＝⟨ ap (λ - → min𝟚 - (p (ι (succ n)))) s ⟩
        min𝟚 ₁ (p (ι (succ n))) ＝⟨refl⟩
        p (ι (succ n))          ∎

  Lemma₀ : (n : ℕ) → a ＝ ι n → p a ＝ ₀
  Lemma₀ n t = p a     ＝⟨ ap p t ⟩
               p (ι n) ＝⟨ Dagger₀ n t ⟩
               ₀       ∎

  Claim₀ : p a ＝ ₁ → (n : ℕ) → a ≠ ι n
  Claim₀ r n s = equal-₁-different-from-₀ r (Lemma₀ n s)

  Claim₁ : p a ＝ ₁ → a ＝ ∞
  Claim₁ r = not-finite-is-∞ fe (Claim₀ r)

  Claim₂ : p a ＝ ₁ → (n : ℕ) → p (ι n) ＝ ₁
  Claim₂ r = Dagger₁ (Claim₁ r)

  Claim₃ : p a ＝ ₁ → p ∞ ＝ ₁
  Claim₃ r = p ∞ ＝⟨ (ap p (Claim₁ r))⁻¹ ⟩
             p a ＝⟨ r ⟩
             ₁   ∎

  Lemma : p a ＝ ₁ → (v : ℕ∞) → p v ＝ ₁
  Lemma r = ℕ∞-𝟚-density fe (Claim₂ r) (Claim₃ r)

\end{code}

Corollaries:

\begin{code}

ℕ∞-compact : is-compact ℕ∞
ℕ∞-compact = compact∙-types-are-compact ℕ∞-compact∙

ℕ∞-Compact : is-Compact ℕ∞ {𝓤}
ℕ∞-Compact = compact-types-are-Compact ℕ∞-compact

ℕ∞-Π-Compact : is-Π-Compact ℕ∞ {𝓤}
ℕ∞-Π-Compact = Σ-Compact-types-are-Π-Compact ℕ∞ ℕ∞-Compact

ℕ∞-Compact∙ : is-Compact∙ ℕ∞ {𝓤}
ℕ∞-Compact∙ = Compact-pointed-gives-Compact∙ ℕ∞-Compact ∞

ℕ∞→ℕ-is-discrete : is-discrete (ℕ∞ → ℕ)
ℕ∞→ℕ-is-discrete = discrete-to-power-compact-is-discrete
                    fe ℕ∞-compact (λ u → ℕ-is-discrete)

ℕ∞→𝟚-is-discrete : is-discrete (ℕ∞ → 𝟚)
ℕ∞→𝟚-is-discrete = discrete-to-power-compact-is-discrete
                    fe ℕ∞-compact (λ u → 𝟚-is-discrete)

module _ (fe' : FunExt) (pt : propositional-truncations-exist) where

 open import TypeTopology.WeaklyCompactTypes fe' pt

 ℕ∞-is-∃-compact : is-∃-compact ℕ∞
 ℕ∞-is-∃-compact = compact-types-are-∃-compact ℕ∞-compact

 ℕ∞-is-Π-compact : is-Π-compact ℕ∞
 ℕ∞-is-Π-compact = ∃-compact-types-are-Π-compact ℕ∞-is-∃-compact

\end{code}
