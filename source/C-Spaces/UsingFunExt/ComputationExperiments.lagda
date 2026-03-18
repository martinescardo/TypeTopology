Chuangjie Xu and Martin Escardo 2014 (updated in February 2015)
(Revised and ported to TypeTopology in 2026 by Chuangjie Xu)

Experiments in computing moduli of uniform continuity

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module C-Spaces.UsingFunExt.ComputationExperiments (fe : DN-funext 𝓤₀ 𝓤₀) where

open import C-Spaces.Preliminaries.Booleans.Functions using (if)
open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.Syntax.SystemTWithFan
open import C-Spaces.UsingFunExt.DiscreteSpace fe
open import C-Spaces.UsingFunExt.YonedaLemma fe
open import C-Spaces.UsingFunExt.Fan fe
open import C-Spaces.UsingFunExt.UCinT fe

\end{code}

This module records a small computational experiment with the Fan functional in
the presence of full function extensionality.

Because function extensionality is used as an outright assumption, the
computational content of the model is lost. In particular, even when the least
modulus is mathematically `0`, the corresponding closed Agda term computed by
the model need not normalize to `0`. The example below illustrates this
phenomenon.

We write `⟦ t ⟧` for the interpretation of a closed System-T-with-Fan term
`t : ((Ⓝ ⇨ ②) ⇨ Ⓝ)` as an ordinary function `₂ℕ → ℕ`, and `modu t` for the
modulus computed for `t` by the Fan functional:

\begin{code}

⟦_⟧ : Tm ε ( ((Ⓝ ⇨ ②) ⇨ Ⓝ)) → ₂ℕ → ℕ
⟦ t ⟧ α = pr₁ (pr₁ ⟦ t ⟧ᵐ ⋆) (ID α)

modu : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ) → ℕ
modu F = pr₁ fan (pr₁ ⟦ F ⟧ᵐ ⋆)

\end{code}

`F₀` is constant, even though it inspects the first input bit.

\begin{code}

F₀ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₀ = LAM (IF · (VAR zero · ZERO) · ZERO · ZERO)

F₀-interpretation : ⟦ F₀ ⟧ ＝ λ α → if (α 0) 0 0
F₀-interpretation = refl

\end{code}

Although the least modulus of `F₀` is mathematically `0`, the closed Agda term
`modu F₀` does not normalize to a numeral under the assumption of function
extensionality. Its unreduced form is the following:

C-Spaces.UniformContinuity.LM _＝_
UF.DiscreteAndSeparated.ℕ-is-discrete (λ α → 𝟚-induction 0 0 (α 0))
(1 Naturals.Addition.+
 C-Spaces.Preliminaries.Naturals.Order.max
 (pr₁
  (transport
   (λ x →
      Σ
      (λ n →
         Σ
         (λ x₁ →
            (n' : ℕ) →
            ((α β : ℕ → 𝟚) →
             α ＝⟦ n' ⟧ β → 𝟚-induction 0 0 (x α 0) ＝ 𝟚-induction 0 0 (x β 0)) →
            n C-Spaces.Preliminaries.Naturals.Order.≤ n')))
   (transport (_＝ (λ x → cons (₀ ∷ ⟨⟩) x))
    (fe
     (λ α →
        fe
        (λ i →
           transport (_＝ cons (₀ ∷ ⟨⟩) (λ x → α x) i)
           (Lemma[cons-take-drop] 1 (cons (₀ ∷ ⟨⟩) α) i) refl)))
    refl)
   (transport
    (λ x →
       (p : (ℕ → 𝟚) → ℕ) →
       Σ
       (λ n →
          Σ
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p α ＝ p β) →
             n C-Spaces.Preliminaries.Naturals.Order.≤ n')) →
       (t : (ℕ → 𝟚) → ℕ → 𝟚) →
       ((m : ℕ) →
        Σ
        (λ n →
           Σ
           (λ x₁ →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n'))) →
       Σ
       (λ n →
          Σ
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → 𝟚) →
              α ＝⟦ n' ⟧ β →
              𝟚-induction 0 (p α) (x (t α) 0) ＝
              𝟚-induction 0 (p β) (x (t β) 0)) →
             n C-Spaces.Preliminaries.Naturals.Order.≤ n')))
    (transport (_＝ (λ x → cons (₀ ∷ ⟨⟩) x))
     (fe
      (λ α →
         fe
         (λ i →
            transport (_＝ cons (₀ ∷ ⟨⟩) (λ x → α x) i)
            (Lemma[cons-take-drop] 1 (cons (₀ ∷ ⟨⟩) α) i) refl)))
     refl)
    (transport
     (λ r →
        (p : (ℕ → 𝟚) → ℕ) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p α ＝ p β) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n')) →
        (t : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
               n C-Spaces.Preliminaries.Naturals.Order.≤ n'))) →
        (p₁ : (ℕ → 𝟚) → ℕ) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p₁ α ＝ p₁ β) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n')) →
        (t₁ : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t₁ α ＝⟦ m ⟧ t₁ β) →
               n C-Spaces.Preliminaries.Naturals.Order.≤ n'))) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) →
               α ＝⟦ n' ⟧ β →
               pr₁ (pr₁ (r (t (t₁ α))) (p (t₁ α))) (p₁ α) ＝
               pr₁ (pr₁ (r (t (t₁ β))) (p (t₁ β))) (p₁ β)) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n')))
     (fe (λ α → refl))
     (λ p pP t uc q qA t₁ tC →
        C-Spaces.UniformContinuity.LM _＝_
        UF.DiscreteAndSeparated.ℕ-is-discrete (λ x → p (t₁ x))
        (pr₁ (tC (pr₁ pP)))
        ,
        C-Spaces.UniformContinuity.Lemma[LM-modulus] _＝_
        UF.DiscreteAndSeparated.ℕ-is-discrete
        (λ p₁ → transport (_＝ z) p₁ refl)
        (λ p₁ q₁ → transport (_＝_ z) q₁ p₁) (λ x → p (t₁ x))
        (pr₁ (tC (pr₁ pP)))
        (λ α β en →
           pr₁ (pr₂ pP) (t₁ α) (t₁ β) (pr₁ (pr₂ (tC (pr₁ pP))) α β en))
        ,
        C-Spaces.UniformContinuity.Lemma[LM-least] _＝_
        UF.DiscreteAndSeparated.ℕ-is-discrete
        (λ p₁ → transport (_＝ z) p₁ refl)
        (λ p₁ q₁ → transport (_＝_ z) q₁ p₁) (λ x → p (t₁ x))
        (pr₁ (tC (pr₁ pP)))
        (λ α β en →
           pr₁ (pr₂ pP) (t₁ α) (t₁ β) (pr₁ (pr₂ (tC (pr₁ pP))) α β en)))
     (λ x → 0)
     (0 ,
      (λ α β e → refl) ,
      (λ k prk → C-Spaces.Preliminaries.Naturals.Order._≤_.≤-zero))
     (λ α x → α x)
     (λ k →
        C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] (λ α x → α x)
        (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
         (λ α β →
            dep-cases
            (λ em →
               dep-cases (λ e → inl (＝⟦succ⟧ em e))
               (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
               (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
            (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
            (Lemma[＝⟦⟧-decidable] α β))
         (λ x → cons (₀ ∷ ⟨⟩) x) k)
        ,
        C-Spaces.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
         (λ α β →
            dep-cases
            (λ em →
               dep-cases (λ e → inl (＝⟦succ⟧ em e))
               (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
               (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
            (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
            (Lemma[＝⟦⟧-decidable] α β))
         (λ x → cons (₀ ∷ ⟨⟩) x) k)
        (λ α β el →
           Lemma[<-＝⟦⟧]
           (λ i i<k →
              transport (_＝_ (α i))
              (Lemma[＝⟦⟧-<]
               (Lemma[＝⟦⟧-succ]
                (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                 (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                 (λ α₁ β₁ →
                    dep-cases
                    (λ em →
                       dep-cases (λ e → inl (＝⟦succ⟧ em e))
                       (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                       (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                    (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                    (Lemma[＝⟦⟧-decidable] α₁ β₁))
                 ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₀ ∷ ⟨⟩) x) k
                 (λ α₁ β₁ e →
                    ＝⟦succ⟧
                    (Lemma[<-＝⟦⟧]
                     (λ i₁ r →
                        C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                        (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                         (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                     (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                      C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))
        ,
        C-Spaces.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
         (λ α β →
            dep-cases
            (λ em →
               dep-cases (λ e → inl (＝⟦succ⟧ em e))
               (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
               (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
            (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
            (Lemma[＝⟦⟧-decidable] α β))
         (λ x → cons (₀ ∷ ⟨⟩) x) k)
        (λ α β el →
           Lemma[<-＝⟦⟧]
           (λ i i<k →
              transport (_＝_ (α i))
              (Lemma[＝⟦⟧-<]
               (Lemma[＝⟦⟧-succ]
                (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                 (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                 (λ α₁ β₁ →
                    dep-cases
                    (λ em →
                       dep-cases (λ e → inl (＝⟦succ⟧ em e))
                       (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                       (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                    (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                    (Lemma[＝⟦⟧-decidable] α₁ β₁))
                 ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₀ ∷ ⟨⟩) x) k
                 (λ α₁ β₁ e →
                    ＝⟦succ⟧
                    (Lemma[<-＝⟦⟧]
                     (λ i₁ r →
                        C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                        (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                         (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                     (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                      C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))))
    (λ x → 0)
    (0 ,
     (λ α β e → refl) ,
     (λ k prk → C-Spaces.Preliminaries.Naturals.Order._≤_.≤-zero))
    (λ α x → α x)
    (λ k →
       C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] (λ α x → α x)
       (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
        (λ α β →
           dep-cases
           (λ em →
              dep-cases (λ e → inl (＝⟦succ⟧ em e))
              (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
              (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
           (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
           (Lemma[＝⟦⟧-decidable] α β))
        (λ x → cons (₀ ∷ ⟨⟩) x) k)
       ,
       C-Spaces.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
        (λ α β →
           dep-cases
           (λ em →
              dep-cases (λ e → inl (＝⟦succ⟧ em e))
              (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
              (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
           (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
           (Lemma[＝⟦⟧-decidable] α β))
        (λ x → cons (₀ ∷ ⟨⟩) x) k)
       (λ α β el →
          Lemma[<-＝⟦⟧]
          (λ i i<k →
             transport (_＝_ (α i))
             (Lemma[＝⟦⟧-<]
              (Lemma[＝⟦⟧-succ]
               (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                (λ α₁ β₁ →
                   dep-cases
                   (λ em →
                      dep-cases (λ e → inl (＝⟦succ⟧ em e))
                      (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                      (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                   (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                   (Lemma[＝⟦⟧-decidable] α₁ β₁))
                ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₀ ∷ ⟨⟩) x) k
                (λ α₁ β₁ e →
                   ＝⟦succ⟧
                   (Lemma[<-＝⟦⟧]
                    (λ i₁ r →
                       C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                       (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                        (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                    (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                     C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl))
       ,
       C-Spaces.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
        (λ α β →
           dep-cases
           (λ em →
              dep-cases (λ e → inl (＝⟦succ⟧ em e))
              (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
              (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
           (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
           (Lemma[＝⟦⟧-decidable] α β))
        (λ x → cons (₀ ∷ ⟨⟩) x) k)
       (λ α β el →
          Lemma[<-＝⟦⟧]
          (λ i i<k →
             transport (_＝_ (α i))
             (Lemma[＝⟦⟧-<]
              (Lemma[＝⟦⟧-succ]
               (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                (λ α₁ β₁ →
                   dep-cases
                   (λ em →
                      dep-cases (λ e → inl (＝⟦succ⟧ em e))
                      (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                      (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                   (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                   (Lemma[＝⟦⟧-decidable] α₁ β₁))
                ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₀ ∷ ⟨⟩) x) k
                (λ α₁ β₁ e →
                   ＝⟦succ⟧
                   (Lemma[<-＝⟦⟧]
                    (λ i₁ r →
                       C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                       (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                        (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (C-Spaces.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                    (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                     C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl))))))
 (pr₁
  (transport
   (λ x →
      Σ
      (λ n →
         Σ
         (λ x₁ →
            (n' : ℕ) →
            ((α β : ℕ → 𝟚) →
             α ＝⟦ n' ⟧ β → 𝟚-induction 0 0 (x α 0) ＝ 𝟚-induction 0 0 (x β 0)) →
            n C-Spaces.Preliminaries.Naturals.Order.≤ n')))
   (transport (_＝ (λ x → cons (₁ ∷ ⟨⟩) x))
    (fe
     (λ α →
        fe
        (λ i →
           transport (_＝ cons (₁ ∷ ⟨⟩) (λ x → α x) i)
           (Lemma[cons-take-drop] 1 (cons (₁ ∷ ⟨⟩) α) i) refl)))
    refl)
   (transport
    (λ x →
       (p : (ℕ → 𝟚) → ℕ) →
       Σ
       (λ n →
          Σ
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p α ＝ p β) →
             n C-Spaces.Preliminaries.Naturals.Order.≤ n')) →
       (t : (ℕ → 𝟚) → ℕ → 𝟚) →
       ((m : ℕ) →
        Σ
        (λ n →
           Σ
           (λ x₁ →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n'))) →
       Σ
       (λ n →
          Σ
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → 𝟚) →
              α ＝⟦ n' ⟧ β →
              𝟚-induction 0 (p α) (x (t α) 0) ＝
              𝟚-induction 0 (p β) (x (t β) 0)) →
             n C-Spaces.Preliminaries.Naturals.Order.≤ n')))
    (transport (_＝ (λ x → cons (₁ ∷ ⟨⟩) x))
     (fe
      (λ α →
         fe
         (λ i →
            transport (_＝ cons (₁ ∷ ⟨⟩) (λ x → α x) i)
            (Lemma[cons-take-drop] 1 (cons (₁ ∷ ⟨⟩) α) i) refl)))
     refl)
    (transport
     (λ r →
        (p : (ℕ → 𝟚) → ℕ) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p α ＝ p β) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n')) →
        (t : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
               n C-Spaces.Preliminaries.Naturals.Order.≤ n'))) →
        (p₁ : (ℕ → 𝟚) → ℕ) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p₁ α ＝ p₁ β) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n')) →
        (t₁ : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t₁ α ＝⟦ m ⟧ t₁ β) →
               n C-Spaces.Preliminaries.Naturals.Order.≤ n'))) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) →
               α ＝⟦ n' ⟧ β →
               pr₁ (pr₁ (r (t (t₁ α))) (p (t₁ α))) (p₁ α) ＝
               pr₁ (pr₁ (r (t (t₁ β))) (p (t₁ β))) (p₁ β)) →
              n C-Spaces.Preliminaries.Naturals.Order.≤ n')))
     (fe (λ α → refl)) (λ p pP t uc q qA t₁ tC → qA) (λ x → 0)
     (0 ,
      (λ α β e → refl) ,
      (λ k prk → C-Spaces.Preliminaries.Naturals.Order._≤_.≤-zero))
     (λ α x → α x)
     (λ k →
        C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] (λ α x → α x)
        (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
         (λ α β →
            dep-cases
            (λ em →
               dep-cases (λ e → inl (＝⟦succ⟧ em e))
               (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
               (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
            (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
            (Lemma[＝⟦⟧-decidable] α β))
         (λ x → cons (₁ ∷ ⟨⟩) x) k)
        ,
        C-Spaces.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
         (λ α β →
            dep-cases
            (λ em →
               dep-cases (λ e → inl (＝⟦succ⟧ em e))
               (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
               (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
            (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
            (Lemma[＝⟦⟧-decidable] α β))
         (λ x → cons (₁ ∷ ⟨⟩) x) k)
        (λ α β el →
           Lemma[<-＝⟦⟧]
           (λ i i<k →
              transport (_＝_ (α i))
              (Lemma[＝⟦⟧-<]
               (Lemma[＝⟦⟧-succ]
                (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                 (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                 (λ α₁ β₁ →
                    dep-cases
                    (λ em →
                       dep-cases (λ e → inl (＝⟦succ⟧ em e))
                       (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                       (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                    (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                    (Lemma[＝⟦⟧-decidable] α₁ β₁))
                 ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₁ ∷ ⟨⟩) x) k
                 (λ α₁ β₁ e →
                    ＝⟦succ⟧
                    (Lemma[<-＝⟦⟧]
                     (λ i₁ r →
                        C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                        (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                         (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                     (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                      C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))
        ,
        C-Spaces.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
         (λ α β →
            dep-cases
            (λ em →
               dep-cases (λ e → inl (＝⟦succ⟧ em e))
               (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
               (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
            (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
            (Lemma[＝⟦⟧-decidable] α β))
         (λ x → cons (₁ ∷ ⟨⟩) x) k)
        (λ α β el →
           Lemma[<-＝⟦⟧]
           (λ i i<k →
              transport (_＝_ (α i))
              (Lemma[＝⟦⟧-<]
               (Lemma[＝⟦⟧-succ]
                (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                 (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                 (λ α₁ β₁ →
                    dep-cases
                    (λ em →
                       dep-cases (λ e → inl (＝⟦succ⟧ em e))
                       (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                       (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                    (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                    (Lemma[＝⟦⟧-decidable] α₁ β₁))
                 ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₁ ∷ ⟨⟩) x) k
                 (λ α₁ β₁ e →
                    ＝⟦succ⟧
                    (Lemma[<-＝⟦⟧]
                     (λ i₁ r →
                        C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                        (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                         (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                     (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                      C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))))
    (λ x → 0)
    (0 ,
     (λ α β e → refl) ,
     (λ k prk → C-Spaces.Preliminaries.Naturals.Order._≤_.≤-zero))
    (λ α x → α x)
    (λ k →
       C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] (λ α x → α x)
       (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
        (λ α β →
           dep-cases
           (λ em →
              dep-cases (λ e → inl (＝⟦succ⟧ em e))
              (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
              (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
           (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
           (Lemma[＝⟦⟧-decidable] α β))
        (λ x → cons (₁ ∷ ⟨⟩) x) k)
       ,
       C-Spaces.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
        (λ α β →
           dep-cases
           (λ em →
              dep-cases (λ e → inl (＝⟦succ⟧ em e))
              (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
              (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
           (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
           (Lemma[＝⟦⟧-decidable] α β))
        (λ x → cons (₁ ∷ ⟨⟩) x) k)
       (λ α β el →
          Lemma[<-＝⟦⟧]
          (λ i i<k →
             transport (_＝_ (α i))
             (Lemma[＝⟦⟧-<]
              (Lemma[＝⟦⟧-succ]
               (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                (λ α₁ β₁ →
                   dep-cases
                   (λ em →
                      dep-cases (λ e → inl (＝⟦succ⟧ em e))
                      (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                      (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                   (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                   (Lemma[＝⟦⟧-decidable] α₁ β₁))
                ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₁ ∷ ⟨⟩) x) k
                (λ α₁ β₁ e →
                   ＝⟦succ⟧
                   (Lemma[<-＝⟦⟧]
                    (λ i₁ r →
                       C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                       (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                        (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                    (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                     C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl))
       ,
       C-Spaces.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (C-Spaces.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
        (λ α β →
           dep-cases
           (λ em →
              dep-cases (λ e → inl (＝⟦succ⟧ em e))
              (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
              (UF.DiscreteAndSeparated.𝟚-is-discrete (α k) (β k)))
           (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
           (Lemma[＝⟦⟧-decidable] α β))
        (λ x → cons (₁ ∷ ⟨⟩) x) k)
       (λ α β el →
          Lemma[<-＝⟦⟧]
          (λ i i<k →
             transport (_＝_ (α i))
             (Lemma[＝⟦⟧-<]
              (Lemma[＝⟦⟧-succ]
               (C-Spaces.UniformContinuity.Lemma[LM-modulus]
                (λ α₁ → _＝⟦_⟧_ α₁ (succ k))
                (λ α₁ β₁ →
                   dep-cases
                   (λ em →
                      dep-cases (λ e → inl (＝⟦succ⟧ em e))
                      (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₁ e)))
                      (UF.DiscreteAndSeparated.𝟚-is-discrete (α₁ k) (β₁ k)))
                   (λ f → inr (λ e → f (Lemma[＝⟦succ⟧]₀ e)))
                   (Lemma[＝⟦⟧-decidable] α₁ β₁))
                ＝⟦⟧-sym ＝⟦⟧-trans (λ x → cons (₁ ∷ ⟨⟩) x) k
                (λ α₁ β₁ e →
                   ＝⟦succ⟧
                   (Lemma[<-＝⟦⟧]
                    (λ i₁ r →
                       C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                       (C-Spaces.Preliminaries.Naturals.Order.≤-trans r
                        (C-Spaces.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (C-Spaces.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                    (C-Spaces.Preliminaries.Naturals.Order._≤_.≤-succ
                     C-Spaces.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl)))))))
