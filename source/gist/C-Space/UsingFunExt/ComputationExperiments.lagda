Chuangjie Xu and Martin Escardo 2014 (updated in February 2015)
(Revised and ported to TypeTopology in 2025)

Experiment of computing moduli of uniform continuity

\begin{code}

{-# OPTIONS --without-K #-}

module gist.C-Space.UsingFunExt.ComputationExperiments where

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

\end{code}

The development of C-spaces in this module depends on function extensionality.
Simply postulating it would destroy the computational content of the model.

We postulate function extensionality.

\begin{code}

postulate fe : DN-funext 𝓤₀ 𝓤₀
-------------------------------

open import gist.C-Space.Preliminaries.Booleans.Functions using (if)
open import gist.C-Space.Preliminaries.Sequence
open import gist.C-Space.Syntax.SystemTWithFan
open import gist.C-Space.UsingFunExt.DiscreteSpace fe
open import gist.C-Space.UsingFunExt.YonedaLemma fe
open import gist.C-Space.UsingFunExt.Fan fe
open import gist.C-Space.UsingFunExt.UCinT fe

\end{code}

We define an abbreviation of the interpretation of closed terms with
meaning in the function space ₂ℕ → ℕ:

\begin{code}

⟦_⟧ : Tm ε ( ((Ⓝ ⇨ ②) ⇨ Ⓝ)) → ₂ℕ → ℕ
⟦ t ⟧ α = pr₁ (pr₁ ⟦ t ⟧ᵐ ⋆) (ID α)

modu : Tm ε ((Ⓝ ⇨ ②) ⇨ Ⓝ) → ℕ
modu F = pr₁ fan (pr₁ ⟦ F ⟧ᵐ ⋆)

\end{code}

F₀ is constant, though it looks at the 1st bit of input.

\begin{code}

F₀ : {Γ : Cxt} → Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F₀ = LAM (IF · (VAR zero · ZERO) · ZERO · ZERO)

F₀-interpretation : ⟦ F₀ ⟧ ＝ λ α → if (α 0) 0 0
F₀-interpretation = refl

\end{code}

We expect `modu F₀` to normalize to 0. However, the postulated instance `fe` of
function extensionality stops its normalization, resulting in the following term:

gist.C-Space.UniformContinuity.LM _＝_
UF.DiscreteAndSeparated.ℕ-is-discrete (λ α → 𝟚-induction 0 0 (α 0))
(1 Naturals.Addition.+
 gist.C-Space.Preliminaries.Naturals.Order.max
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
            n gist.C-Space.Preliminaries.Naturals.Order.≤ n')))
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
             n gist.C-Space.Preliminaries.Naturals.Order.≤ n')) →
       (t : (ℕ → 𝟚) → ℕ → 𝟚) →
       ((m : ℕ) →
        Σ
        (λ n →
           Σ
           (λ x₁ →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n'))) →
       Σ
       (λ n →
          Σ
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → 𝟚) →
              α ＝⟦ n' ⟧ β →
              𝟚-induction 0 (p α) (x (t α) 0) ＝
              𝟚-induction 0 (p β) (x (t β) 0)) →
             n gist.C-Space.Preliminaries.Naturals.Order.≤ n')))
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
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n')) →
        (t : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
               n gist.C-Space.Preliminaries.Naturals.Order.≤ n'))) →
        (p₁ : (ℕ → 𝟚) → ℕ) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p₁ α ＝ p₁ β) →
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n')) →
        (t₁ : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t₁ α ＝⟦ m ⟧ t₁ β) →
               n gist.C-Space.Preliminaries.Naturals.Order.≤ n'))) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) →
               α ＝⟦ n' ⟧ β →
               pr₁ (pr₁ (r (t (t₁ α))) (p (t₁ α))) (p₁ α) ＝
               pr₁ (pr₁ (r (t (t₁ β))) (p (t₁ β))) (p₁ β)) →
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n')))
     (fe (λ α → refl))
     (λ p pP t uc q qA t₁ tC →
        gist.C-Space.UniformContinuity.LM _＝_
        UF.DiscreteAndSeparated.ℕ-is-discrete (λ x → p (t₁ x))
        (pr₁ (tC (pr₁ pP)))
        ,
        gist.C-Space.UniformContinuity.Lemma[LM-modulus] _＝_
        UF.DiscreteAndSeparated.ℕ-is-discrete
        (λ p₁ → transport (_＝ z) p₁ refl)
        (λ p₁ q₁ → transport (_＝_ z) q₁ p₁) (λ x → p (t₁ x))
        (pr₁ (tC (pr₁ pP)))
        (λ α β en →
           pr₁ (pr₂ pP) (t₁ α) (t₁ β) (pr₁ (pr₂ (tC (pr₁ pP))) α β en))
        ,
        gist.C-Space.UniformContinuity.Lemma[LM-least] _＝_
        UF.DiscreteAndSeparated.ℕ-is-discrete
        (λ p₁ → transport (_＝ z) p₁ refl)
        (λ p₁ q₁ → transport (_＝_ z) q₁ p₁) (λ x → p (t₁ x))
        (pr₁ (tC (pr₁ pP)))
        (λ α β en →
           pr₁ (pr₂ pP) (t₁ α) (t₁ β) (pr₁ (pr₂ (tC (pr₁ pP))) α β en)))
     (λ x → 0)
     (0 ,
      (λ α β e → refl) ,
      (λ k prk → gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-zero))
     (λ α x → α x)
     (λ k →
        gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] (λ α x → α x)
        (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
        gist.C-Space.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
                (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                        gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                        (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                         (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                     (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                      gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))
        ,
        gist.C-Space.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
                (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                        gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                        (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                         (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                     (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                      gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))))
    (λ x → 0)
    (0 ,
     (λ α β e → refl) ,
     (λ k prk → gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-zero))
    (λ α x → α x)
    (λ k →
       gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] (λ α x → α x)
       (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
       gist.C-Space.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
               (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                       gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                       (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                        (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                    (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                     gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl))
       ,
       gist.C-Space.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
               (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                       gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e i₁
                       (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                        (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (gist.C-Space.UniformContinuity.claim₀ ₀ ⟨⟩ k α₁ β₁ e e k
                    (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                     gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
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
            n gist.C-Space.Preliminaries.Naturals.Order.≤ n')))
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
             n gist.C-Space.Preliminaries.Naturals.Order.≤ n')) →
       (t : (ℕ → 𝟚) → ℕ → 𝟚) →
       ((m : ℕ) →
        Σ
        (λ n →
           Σ
           (λ x₁ →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n'))) →
       Σ
       (λ n →
          Σ
          (λ x₁ →
             (n' : ℕ) →
             ((α β : ℕ → 𝟚) →
              α ＝⟦ n' ⟧ β →
              𝟚-induction 0 (p α) (x (t α) 0) ＝
              𝟚-induction 0 (p β) (x (t β) 0)) →
             n gist.C-Space.Preliminaries.Naturals.Order.≤ n')))
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
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n')) →
        (t : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t α ＝⟦ m ⟧ t β) →
               n gist.C-Space.Preliminaries.Naturals.Order.≤ n'))) →
        (p₁ : (ℕ → 𝟚) → ℕ) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → p₁ α ＝ p₁ β) →
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n')) →
        (t₁ : (ℕ → 𝟚) → ℕ → 𝟚) →
        ((m : ℕ) →
         Σ
         (λ n →
            Σ
            (λ x →
               (n' : ℕ) →
               ((α β : ℕ → 𝟚) → α ＝⟦ n' ⟧ β → t₁ α ＝⟦ m ⟧ t₁ β) →
               n gist.C-Space.Preliminaries.Naturals.Order.≤ n'))) →
        Σ
        (λ n →
           Σ
           (λ x →
              (n' : ℕ) →
              ((α β : ℕ → 𝟚) →
               α ＝⟦ n' ⟧ β →
               pr₁ (pr₁ (r (t (t₁ α))) (p (t₁ α))) (p₁ α) ＝
               pr₁ (pr₁ (r (t (t₁ β))) (p (t₁ β))) (p₁ β)) →
              n gist.C-Space.Preliminaries.Naturals.Order.≤ n')))
     (fe (λ α → refl)) (λ p pP t uc q qA t₁ tC → qA) (λ x → 0)
     (0 ,
      (λ α β e → refl) ,
      (λ k prk → gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-zero))
     (λ α x → α x)
     (λ k →
        gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] (λ α x → α x)
        (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
        gist.C-Space.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
                (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                        gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                        (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                         (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                     (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                      gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))
        ,
        gist.C-Space.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
        Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
        (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
                (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                        gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                        (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                         (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                    (gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                     (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                      gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                 α β el))
               i i<k)
              refl))))
    (λ x → 0)
    (0 ,
     (λ α β e → refl) ,
     (λ k prk → gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-zero))
    (λ α x → α x)
    (λ k →
       gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] (λ α x → α x)
       (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
       gist.C-Space.UniformContinuity.Lemma[LM-modulus] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
               (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                       gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                       (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                        (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                    (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                     gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl))
       ,
       gist.C-Space.UniformContinuity.Lemma[LM-least] (λ α → _＝⟦_⟧_ α k)
       Lemma[＝⟦⟧-decidable] ＝⟦⟧-sym ＝⟦⟧-trans (λ α x → α x)
       (gist.C-Space.UniformContinuity.LM (λ α → _＝⟦_⟧_ α (succ k))
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
               (gist.C-Space.UniformContinuity.Lemma[LM-modulus]
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
                       gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e i₁
                       (gist.C-Space.Preliminaries.Naturals.Order.≤-trans r
                        (gist.C-Space.Preliminaries.Naturals.Order.Lemma[n≤n+1] k))))
                   (gist.C-Space.UniformContinuity.claim₀ ₁ ⟨⟩ k α₁ β₁ e e k
                    (gist.C-Space.Preliminaries.Naturals.Order._≤_.≤-succ
                     gist.C-Space.Preliminaries.Naturals.Order.≤-refl)))
                α β el))
              i i<k)
             refl)))))))
