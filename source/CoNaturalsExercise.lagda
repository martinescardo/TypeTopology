Martin Escardo, Chuangjie Xu, 2012.

As a simple application of coinduction and corecursion on ℕ∞, one can
show that the the inclusion map incl : ℕ∞ → ₂ℕ is part of a
retraction.

This exercise is artificial: a direct construction and proof of the
retraction would be shorter and perhaps clearer. However, it does
illustrate how co-recursion and co-induction can be used.

Recall that a retraction is a pair of maps r : X → Y and s : Y → X
such that r ∘ s : Y → Y is the identity, where r is called the
retraction and s the section. In this case, it follows that
s ∘ r : X → X is idempotent, and s is an injection and r is a
surjection. When such maps exists one says that Y is a retract of X.

The idea of the construction of the retraction is that we "read"
digits from α until we find a zero or forever, and count how long
this took.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module CoNaturalsExercise (fe : FunExt) where

open import SpartanMLTT
open import Two-Properties
open import CoNaturals fe
open import GenericConvergentSequence
open import Sequence fe
open import CanonicalMapNotation

ℕ∞-to-ℕ→𝟚-is-a-section : Σ ρ ꞉ ((ℕ → 𝟚) → ℕ∞) , ρ ∘ ι ≡ id
ℕ∞-to-ℕ→𝟚-is-a-section  = ρ , dfunext (fe 𝓤₀ 𝓤₀) lemma
 where
  f-ρ : 𝟚 → (ℕ → 𝟚) → 𝟙 + (ℕ → 𝟚)
  f-ρ ₀ α = inl ⋆
  f-ρ ₁ α = inr α

  p-ρ : (ℕ → 𝟚) → 𝟙 + (ℕ → 𝟚)
  p-ρ α = f-ρ (head α) (tail α)

  ρ : (ℕ → 𝟚) → ℕ∞
  ρ = ℕ∞-corec p-ρ

  ρ-spec : PRED ∘ ρ ≡ (𝟙+ ρ) ∘ p-ρ
  ρ-spec = ℕ∞-corec-homomorphism p-ρ

  ρ-spec₀ : (α : ℕ → 𝟚) → head α ≡ ₀ → ρ α ≡ Zero
  ρ-spec₀ α r = coalg-morphism-Zero p-ρ ρ ρ-spec α ⋆ lemma
   where
    lemma : p-ρ α ≡ inl ⋆
    lemma = ap (λ - → f-ρ - (tail α)) r

  ρ-spec₁ : (α : ℕ → 𝟚) → head α ≡ ₁ → ρ α ≡ Succ (ρ (tail α))
  ρ-spec₁ α r = coalg-morphism-Succ p-ρ ρ ρ-spec α (tail α) lemma
   where
    lemma : p-ρ α ≡ inr (tail α)
    lemma = ap (λ - → f-ρ - (tail α)) r

  R : ℕ∞ → ℕ∞ → 𝓤₀ ̇
  R u v = Σ w ꞉ ℕ∞ , (ρ (ι w) ≡ u) × (w ≡ v)

  r : (u : ℕ∞) → R (ρ (ι u)) u
  r u = (u , refl , refl)

  R-positivity : (u v : ℕ∞) → R u v → positivity u ≡ positivity v
  R-positivity u v (w , c , d) = 𝟚-equality-cases lemma₀ lemma₁
   where
    lemma₀ : positivity w ≡ ₀ → positivity u ≡ positivity v
    lemma₀ r = ap positivity claim₃
     where
      claim₀ : ρ (ι w) ≡ Zero
      claim₀ = ρ-spec₀ (ι w) r
      claim₁ : v ≡ Zero
      claim₁ = d ⁻¹ ∙ is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀) r
      claim₂ : ρ (ι w) ≡ v
      claim₂ = claim₀ ∙ claim₁ ⁻¹
      claim₃ : u ≡ v
      claim₃ = c ⁻¹ ∙ claim₂

    lemma₁ : positivity w ≡ ₁ → positivity u ≡ positivity v
    lemma₁ r = claim₂ ∙ claim₄ ⁻¹
     where
      claim₀ : positivity (ρ (ι w)) ≡ ₁
      claim₀ = ap positivity (ρ-spec₁ (ι w) r)

      claim₁ : positivity (ρ (ι w)) ≡ positivity u
      claim₁ = ap positivity c

      claim₂ : positivity u ≡ ₁
      claim₂ = claim₁ ⁻¹ ∙ claim₀
      claim₃ : positivity w ≡ positivity v
      claim₃ = ap positivity d

      claim₄ : positivity v ≡ ₁
      claim₄ = claim₃ ⁻¹ ∙ r

  R-Pred : (u v : ℕ∞) → R u v → R (Pred u) (Pred v)
  R-Pred u v (w , c , d) = (Pred w , lemma₀ , lemma₁)
   where
    lemma₀ : ρ (ι (Pred w)) ≡ Pred u
    lemma₀ = claim ∙ claim₀
     where
     claim₀ : Pred (ρ (ι w)) ≡ Pred u
     claim₀ = ap Pred c

     claim :  ρ (ι (Pred w)) ≡ Pred (ρ (ι w))
     claim = 𝟚-equality-cases claim₁ claim₂
      where
       claim₁ : is-Zero w → ρ (ι (Pred w)) ≡ Pred (ρ (ι w))
       claim₁ r = c₃ ∙ c₅ ⁻¹
        where
         c₀ : w ≡ Zero
         c₀ = is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀) r
         c₁ : Pred w ≡ Zero
         c₁ = ap Pred c₀

         c₂ : ι (Pred w) 0 ≡ ₀
         c₂ = ap (head ∘ ι) c₁

         c₃ : ρ (ι (Pred w)) ≡ Zero
         c₃ = ρ-spec₀ (ι (Pred w)) c₂

         c₄ : ρ (ι w) ≡ Zero
         c₄ = ρ-spec₀ (ι w) r

         c₅ : Pred (ρ (ι w)) ≡ Zero
         c₅ = ap Pred c₄
       claim₂ : is-positive w → ρ (ι (Pred w)) ≡ Pred (ρ (ι w))
       claim₂ r = c₃ ∙ c₁ ⁻¹
        where
         c₀ : ρ (ι w) ≡ Succ (ρ (tail (ι w)))
         c₀ = ρ-spec₁ (ι w) r

         c₁ : Pred (ρ (ι w)) ≡ ρ (tail (ι w))
         c₁ = ap Pred c₀ ∙ Pred-Succ

         c₃ : ρ (ι (Pred w)) ≡ ρ (tail (ι w))
         c₃ = refl

    lemma₁ : Pred w ≡ Pred v
    lemma₁ = ap Pred d

  R-bisimulation : ℕ∞-bisimulation R
  R-bisimulation u v r = (R-positivity u v r , R-Pred u v r)

  lemma : (u : ℕ∞) → ρ (ι u) ≡ u
  lemma u = ℕ∞-coinduction R R-bisimulation (ρ (ι u)) u (r u)

\end{code}
