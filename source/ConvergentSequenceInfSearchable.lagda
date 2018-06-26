Martin Escardo 20-21 December 2012

Development adapted from the module ConvergentSequenceSearchable:

Not only is ℕ∞ searchable, but, moreover, minimal witnesses can be
found.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module ConvergentSequenceInfSearchable (fe : ∀ {U V} → funext U V) where

open import SpartanMLTT
open import InfSearchable
open import GenericConvergentSequence

ℕ∞-is-inf-searchable : inf-searchable _≼_
ℕ∞-is-inf-searchable p = a , (putative-root-lemma , (lower-bound-lemma , uborlb-lemma))
 where 
  α : ℕ → 𝟚
  α 0       = p(under 0)
  α(succ n) = min𝟚 (α n) (p(under(succ n)))

  a : ℕ∞
  a = (α , λ i → Lemma[minab≤₂a])

  Dagger₀ : (n : ℕ) → a ≡ under n → p(under n) ≡ ₀
  Dagger₀ 0 r =  ap (λ w → incl w 0) r
  Dagger₀ (succ n) r = w ∙ t
   where 
    s : α n ≡ ₁
    s = ap (λ w → incl w n) r ∙ under-diagonal₁ n
    t : α(succ n) ≡ ₀
    t = ap (λ w → incl w(succ n)) r ∙ under-diagonal₀ n
    w : p(under(succ n)) ≡ α(succ n)
    w = (ap(λ b → min𝟚 b (p(under(succ n)))) s)⁻¹

  Dagger₁ : a ≡ ∞ → (n : ℕ) → p(under n) ≡ ₁
  Dagger₁ r 0 = ap (λ w → incl w 0) r
  Dagger₁ r (succ n) = w ∙ t
   where 
    s : α n ≡ ₁
    s = ap (λ w → incl w n) r
    t : α(succ n) ≡ ₁
    t = ap (λ w → incl w (succ n)) r
    w : p(under(succ n)) ≡ α(succ n)
    w = (ap(λ b → min𝟚 b (p(under(succ n)))) s)⁻¹

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
  Lemma r = ℕ∞-density fe (Claim₂ r) (Claim₃ r)

  putative-root-lemma : (Σ \u → p u ≡ ₀) → p a ≡ ₀
  putative-root-lemma (x , r) = lemma claim
   where   
    lemma : ¬((x : ℕ∞) → p x ≡ ₁) → p a ≡ ₀
    lemma = Lemma[b≢₁→b≡₀] ∘ (contrapositive Lemma)
    claim : ¬((x : ℕ∞) → p x ≡ ₁)
    claim f = Lemma[b≡₁→b≢₀] (f x) r

  lower-bound-lemma : (u : ℕ∞)→ p u ≡ ₀ → a ≼ u
  lower-bound-lemma u r 0 s = lemma
    where
     claim₀ : incl u 0 ≡ ₀ → p u ≡ α 0
     claim₀ t = ap p (is-Zero-equal-Zero fe t)
     claim₁ : incl u 0 ≡ ₀ → ₀ ≡ ₁
     claim₁ t = r ⁻¹ ∙ claim₀ t ∙ s
     lemma : incl u 0 ≡ ₁
     lemma = Lemma[b≢₀→b≡₁] (contrapositive claim₁ zero-is-not-one)

  lower-bound-lemma u r (succ n) s = lemma
   where
    -- s : min𝟚 (incl a n) (p(under(succ n))) ≡ ₁
    IH : incl a n ≡ ₁ → incl u n ≡ ₁
    IH = lower-bound-lemma u r n
    claim₀ : incl u n ≡ ₁
    claim₀ = IH(Lemma[min𝟚ab≡₁→a≡₁] s)
    claim₁ : p(under(succ n)) ≡ ₁
    claim₁ = Lemma[min𝟚ab≡₁→b≡₁]{(incl a n)} s
    claim₂ : incl u (succ n) ≡ ₀ → u ≡ under(succ n)
    claim₂ = Succ-criterion fe claim₀
    claim₃ : incl u (succ n) ≡ ₀ → p u ≡ p(under(succ n))
    claim₃ t = ap p (claim₂ t)
    claim₄ : incl u (succ n) ≡ ₀ → p u ≡ ₁
    claim₄ t = claim₃ t ∙ claim₁
    claim₅ : incl u (succ n) ≢ ₀
    claim₅ t = Lemma[b≡₁→b≢₀] (claim₄ t) r 
    lemma : incl u (succ n) ≡ ₁
    lemma = Lemma[b≢₀→b≡₁] claim₅

  uborlb-lemma : (l : ℕ∞) → ((x : ℕ∞) → p x ≡ ₀ → l ≼ x) → l ≼ a
  uborlb-lemma l lower-bounder = two-equality-cases lemma₀ lemma₁
   where
    lemma₀ : p a ≡ ₀ → l ≼ a
    lemma₀ = lower-bounder a
    lemma₁ : p a ≡ ₁ → l ≼ a
    lemma₁ r n x = ap (λ a → incl a n) (Claim₁ r)
\end{code}
