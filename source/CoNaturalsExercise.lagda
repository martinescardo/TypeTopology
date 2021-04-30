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

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module CoNaturalsExercise (fe : FunExt) where

open import SpartanMLTT
open import Two-Properties
open import CoNaturals fe
open import GenericConvergentSequence
open import Sequence fe

incl-is-a-section : Σ retr ꞉ ((ℕ → 𝟚) → ℕ∞) , retr ∘ incl ≡ id
incl-is-a-section  = retr , dfunext (fe 𝓤₀ 𝓤₀) lemma
 where
  f-retr : 𝟚 → (ℕ → 𝟚) → 𝟙 + (ℕ → 𝟚)
  f-retr ₀ α = inl *
  f-retr ₁ α = inr α

  p-retr : (ℕ → 𝟚) → 𝟙 + (ℕ → 𝟚)
  p-retr α = f-retr (head α) (tail α)

  retr : (ℕ → 𝟚) → ℕ∞
  retr = ℕ∞-corec p-retr

  retr-spec : PRED ∘ retr ≡ (𝟙+ retr) ∘ p-retr
  retr-spec = ℕ∞-corec-homomorphism p-retr

  retr-spec₀ : (α : ℕ → 𝟚) → head α ≡ ₀ → retr α ≡ Zero
  retr-spec₀ α r = coalg-morphism-Zero p-retr retr retr-spec α * lemma
   where
    lemma : p-retr α ≡ inl *
    lemma = ap (λ - → f-retr - (tail α)) r

  retr-spec₁ : (α : ℕ → 𝟚) → head α ≡ ₁ → retr α ≡ Succ (retr (tail α))
  retr-spec₁ α r = coalg-morphism-Succ p-retr retr retr-spec α (tail α) lemma
   where
    lemma : p-retr α ≡ inr (tail α)
    lemma = ap (λ - → f-retr - (tail α)) r

  R : ℕ∞ → ℕ∞ → 𝓤₀ ̇
  R u v = Σ w ꞉ ℕ∞ , (retr (incl w) ≡ u) × (w ≡ v)

  r : (u : ℕ∞) → R (retr (incl u)) u
  r u = (u , refl , refl)

  R-positivity : (u v : ℕ∞) → R u v → positivity u ≡ positivity v
  R-positivity u v (w , c , d) = 𝟚-equality-cases lemma₀ lemma₁
   where
    lemma₀ : positivity w ≡ ₀ → positivity u ≡ positivity v
    lemma₀ r = ap positivity claim₃
     where
      claim₀ : retr (incl w) ≡ Zero
      claim₀ = retr-spec₀ (incl w) r
      claim₁ : v ≡ Zero
      claim₁ = d ⁻¹ ∙ is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀) r
      claim₂ : retr (incl w) ≡ v
      claim₂ = claim₀ ∙ claim₁ ⁻¹
      claim₃ : u ≡ v
      claim₃ = c ⁻¹ ∙ claim₂

    lemma₁ : positivity w ≡ ₁ → positivity u ≡ positivity v
    lemma₁ r = claim₂ ∙ claim₄ ⁻¹
     where
      claim₀ : positivity (retr (incl w)) ≡ ₁
      claim₀ = ap positivity (retr-spec₁ (incl w) r)

      claim₁ : positivity (retr (incl w)) ≡ positivity u
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
    lemma₀ : retr (incl (Pred w)) ≡ Pred u
    lemma₀ = claim ∙ claim₀
     where
     claim₀ : Pred (retr (incl w)) ≡ Pred u
     claim₀ = ap Pred c

     claim :  retr (incl (Pred w)) ≡ Pred (retr (incl w))
     claim = 𝟚-equality-cases claim₁ claim₂
      where
       claim₁ : is-Zero w → retr (incl (Pred w)) ≡ Pred (retr (incl w))
       claim₁ r = c₃ ∙ c₅ ⁻¹
        where
         c₀ : w ≡ Zero
         c₀ = is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀) r
         c₁ : Pred w ≡ Zero
         c₁ = ap Pred c₀

         c₂ : incl (Pred w) 0 ≡ ₀
         c₂ = ap (head ∘ incl) c₁

         c₃ : retr (incl (Pred w)) ≡ Zero
         c₃ = retr-spec₀ (incl (Pred w)) c₂

         c₄ : retr (incl w) ≡ Zero
         c₄ = retr-spec₀ (incl w) r

         c₅ : Pred (retr (incl w)) ≡ Zero
         c₅ = ap Pred c₄
       claim₂ : is-positive w → retr (incl (Pred w)) ≡ Pred (retr (incl w))
       claim₂ r = c₃ ∙ c₁ ⁻¹
        where
         c₀ : retr (incl w) ≡ Succ (retr (tail (incl w)))
         c₀ = retr-spec₁ (incl w) r

         c₁ : Pred (retr (incl w)) ≡ retr (tail (incl w))
         c₁ = ap Pred c₀ ∙ Pred-Succ

         c₃ : retr (incl (Pred w)) ≡ retr (tail (incl w))
         c₃ = refl

    lemma₁ : Pred w ≡ Pred v
    lemma₁ = ap Pred d

  R-bisimulation : ℕ∞-bisimulation R
  R-bisimulation u v r = (R-positivity u v r , R-Pred u v r)

  lemma : (u : ℕ∞) → retr (incl u) ≡ u
  lemma u = ℕ∞-coinduction R R-bisimulation (retr (incl u)) u (r u)

\end{code}
