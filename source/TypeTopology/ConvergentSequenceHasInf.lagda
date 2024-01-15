Martin Escardo 20-21 December 2012

Development adapted from the module ConvergentSequenceCompact:

Not only is ℕ∞ compact (or searchable), but, moreover, minimal
witnesses can be found.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import MLTT.Spartan

module TypeTopology.ConvergentSequenceHasInf (fe₀ : funext 𝓤₀ 𝓤₀) where


open import MLTT.Two-Properties
open import TypeTopology.InfProperty
open import CoNaturals.GenericConvergentSequence
open import Notation.Order
open import Notation.CanonicalMap

ℕ∞-has-inf : has-inf _≼_
ℕ∞-has-inf p = a , putative-root-lemma , lower-bound-lemma , uborlb-lemma
 where
  α : ℕ → 𝟚
  α 0       = p (ι 0)
  α (succ n) = min𝟚 (α n) (p (ι (succ n)))

  a : ℕ∞
  a = (α , λ i → Lemma[minab≤₂a])

  Dagger₀ : (n : ℕ) → a ＝ ι n → p (ι n) ＝ ₀
  Dagger₀ 0        r = ap (λ - → ι - 0) r
  Dagger₀ (succ n) r = p (ι (succ n)) ＝⟨ w ⟩
                       α (succ n)     ＝⟨ t ⟩
                       ₀              ∎
   where
    s : α n ＝ ₁
    s = ap (λ - → ι - n) r ∙ ℕ-to-ℕ∞-diagonal₁ n

    t = α (succ n)              ＝⟨ ap (λ - → ι - (succ n)) r ⟩
        ι (ι (succ n)) (succ n) ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
        ₀                       ∎

    w : p (ι (succ n)) ＝ α (succ n)
    w = (ap (λ - → min𝟚 - (p (ι (succ n)))) s)⁻¹

  Dagger₁ : a ＝ ∞ → (n : ℕ) → p (ι n) ＝ ₁
  Dagger₁ r 0 = ap (λ - → ι - 0) r
  Dagger₁ r (succ n) = p (ι (succ n)) ＝⟨ w ⟩
                       α (succ n)     ＝⟨ t ⟩
                       ₁              ∎
   where
    s : α n ＝ ₁
    s = ap (λ - → ι - n) r

    t : α (succ n) ＝ ₁
    t = ap (λ - → ι - (succ n)) r

    w : p (ι (succ n)) ＝ α (succ n)
    w = (ap (λ - → min𝟚 - (p (ι (succ n)))) s)⁻¹

  Claim₀ : p a ＝ ₁ → (n : ℕ) → a ≠ ι n
  Claim₀ r n s = equal-₁-different-from-₀ r (Lemma s)
   where
    Lemma : a ＝ ι n → p a ＝ ₀
    Lemma t = p a     ＝⟨ ap p t ⟩
              p (ι n) ＝⟨ Dagger₀ n t ⟩
              ₀       ∎

  Claim₁ : p a ＝ ₁ → a ＝ ∞
  Claim₁ r = not-finite-is-∞ fe₀ (Claim₀ r)

  Claim₂ : p a ＝ ₁ → (n : ℕ) → p (ι n) ＝ ₁
  Claim₂ r = Dagger₁ (Claim₁ r)

  Claim₃ : p a ＝ ₁ → p ∞ ＝ ₁
  Claim₃ r = p ∞ ＝⟨ (ap p (Claim₁ r))⁻¹ ⟩
             p a ＝⟨ r ⟩
             ₁   ∎

  Lemma : p a ＝ ₁ → (v : ℕ∞) → p v ＝ ₁
  Lemma r = ℕ∞-𝟚-density fe₀ (Claim₂ r) (Claim₃ r)

  putative-root-lemma : (Σ u ꞉ ℕ∞ , p u ＝ ₀) → p a ＝ ₀
  putative-root-lemma (x , r) = lemma claim
   where
    lemma : ¬ ((x : ℕ∞) → p x ＝ ₁) → p a ＝ ₀
    lemma = different-from-₁-equal-₀ ∘ (contrapositive Lemma)

    claim : ¬ ((x : ℕ∞) → p x ＝ ₁)
    claim f = equal-₁-different-from-₀ (f x) r

  lower-bound-lemma : (u : ℕ∞)→ p u ＝ ₀ → a ≼ u
  lower-bound-lemma u r 0 s = lemma
    where
     claim₀ : ι u 0 ＝ ₀ → p u ＝ α 0
     claim₀ t = ap p (is-Zero-equal-Zero fe₀ t)

     claim₁ : ι u 0 ＝ ₀ → ₀ ＝ ₁
     claim₁ t = ₀   ＝⟨ r ⁻¹ ⟩
                p u ＝⟨ claim₀ t ⟩
                α 0 ＝⟨ s ⟩
                ₁   ∎

     lemma : ι u 0 ＝ ₁
     lemma = different-from-₀-equal-₁ (contrapositive claim₁ zero-is-not-one)

  lower-bound-lemma u r (succ n) s = lemma
   where
    remark : min𝟚 (ι a n) (p (ι (succ n))) ＝ ₁
    remark = s

    IH : ι a n ＝ ₁ → ι u n ＝ ₁
    IH = lower-bound-lemma u r n

    claim₀ : ι u n ＝ ₁
    claim₀ = IH (Lemma[min𝟚ab＝₁→a＝₁] s)

    claim₁ : p (ι (succ n)) ＝ ₁
    claim₁ = Lemma[min𝟚ab＝₁→b＝₁]{(ι a n)} s

    claim₂ : ι u (succ n) ＝ ₀ → u ＝ ι (succ n)
    claim₂ = Succ-criterion fe₀ claim₀

    claim₃ : ι u (succ n) ＝ ₀ → p u ＝ p (ι (succ n))
    claim₃ t = ap p (claim₂ t)

    claim₄ : ι u (succ n) ＝ ₀ → p u ＝ ₁
    claim₄ t = p u            ＝⟨ claim₃ t ⟩
               p (ι (succ n)) ＝⟨ claim₁ ⟩
               ₁              ∎

    claim₅ : ι u (succ n) ≠ ₀
    claim₅ t = equal-₁-different-from-₀ (claim₄ t) r

    lemma : ι u (succ n) ＝ ₁
    lemma = different-from-₀-equal-₁ claim₅

  uborlb-lemma : (l : ℕ∞) → ((x : ℕ∞) → p x ＝ ₀ → l ≼ x) → l ≼ a
  uborlb-lemma l lower-bounder = 𝟚-equality-cases lemma₀ lemma₁
   where
    lemma₀ : p a ＝ ₀ → l ≼ a
    lemma₀ = lower-bounder a

    lemma₁ : p a ＝ ₁ → l ≼ a
    lemma₁ r n x = ap (λ - → ι - n) (Claim₁ r)

\end{code}
