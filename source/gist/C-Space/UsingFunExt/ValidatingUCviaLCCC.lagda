Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module gist.C-Space.UsingFunExt.ValidatingUCviaLCCC (fe : DN-funext 𝓤₀ 𝓤₀) where

open import gist.C-Space.Preliminaries.Sequence
open import gist.C-Space.Preliminaries.Naturals.Order
open import gist.C-Space.UniformContinuity
open import gist.C-Space.Coverage
open import gist.C-Space.UsingFunExt.Space
open import gist.C-Space.UsingFunExt.CartesianClosedness fe
open import gist.C-Space.UsingFunExt.DiscreteSpace fe
open import gist.C-Space.UsingFunExt.LocalCartesianClosedness fe
open import gist.C-Space.UsingFunExt.Fan fe

\end{code}

The Curry-Howard interpretation of UC is the following

 ⊢ Π (f : ₂ℕ → ℕ)  Σ (n : ℕ)  Π (α β : ₂ℕ) (α ＝⟦n⟧ β → f α ＝ f β).

we show that it is validated in C-spaces step by step:

(1) u₁  ::=  f : ₂ℕ → ℕ, n : ℕ, α : ₂ℕ, β : ₂ℕ ⊢ α ＝⟦n⟧ β

\begin{code}

Γ⁴ : Space
Γ⁴ = ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) ⊗ ℕSpace ⊗ (ℕSpace ⇒ 𝟚Space) ⊗ (ℕSpace ⇒ 𝟚Space)
πf⁴ : U Γ⁴ → U ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace)
πf⁴ (((f , _) , _) , _) = f
πn⁴ : U Γ⁴ → ℕ
πn⁴ (((_ , n) , _) , _) = n
πα⁴ : U Γ⁴ → U (ℕSpace ⇒ 𝟚Space)
πα⁴ (((_ , _) , α) , _) = α
πβ⁴ : U Γ⁴ → U (ℕSpace ⇒ 𝟚Space)
πβ⁴ (((_ , _) , _) , β) = β

Γ⁴Prp : U Γ⁴ → Set
Γ⁴Prp w = pr₁(πα⁴ w) ＝⟦ πn⁴ w ⟧ pr₁(πβ⁴ w)

dom⟦u₁⟧ : Space
dom⟦u₁⟧ = Subspace Γ⁴ Γ⁴Prp

⟦u₁⟧ : Map dom⟦u₁⟧ Γ⁴
⟦u₁⟧ = cts-incl Γ⁴ Γ⁴Prp

\end{code}

(2) u₂  ::=  f : ₂ℕ → ℕ, n : ℕ, α : ₂ℕ, β : ₂ℕ, e : α ＝⟦n⟧ β ⊢ f α ＝ f β

\begin{code}

Γ⁵ : Space
Γ⁵ = dom⟦u₁⟧
πf⁵ : U Γ⁵ → U ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace)
πf⁵ = πf⁴ ∘ pr₁
πα⁵ : U Γ⁵ → U (ℕSpace ⇒ 𝟚Space)
πα⁵ = πα⁴ ∘ pr₁
πβ⁵ : U Γ⁵ → U (ℕSpace ⇒ 𝟚Space)
πβ⁵ = πβ⁴ ∘ pr₁

Γ⁵Prp : U Γ⁵ → Set
Γ⁵Prp w = pr₁ (πf⁵ w) (πα⁵ w) ＝ pr₁ (πf⁵ w) (πβ⁵ w)

dom⟦u₂⟧ : Space
dom⟦u₂⟧ = Subspace Γ⁵ Γ⁵Prp

⟦u₂⟧ : Map dom⟦u₂⟧ Γ⁵
⟦u₂⟧ = cts-incl Γ⁵ Γ⁵Prp

\end{code}

(3) u₃  ::=  f : ₂ℕ → ℕ, n : ℕ, α : ₂ℕ, β : ₂ℕ ⊢ α ＝⟦n⟧ β → f α ＝ f β

\begin{code}

dom⟦u₃⟧ : Space
dom⟦u₃⟧ = dom⟪ dom⟦u₁⟧ , Γ⁴ ⟫Π[ ⟦u₁⟧ ] (dom⟦u₂⟧ , ⟦u₂⟧)

⟦u₃⟧ : Map dom⟦u₃⟧ Γ⁴
⟦u₃⟧ = pr₂ (⟪ dom⟦u₁⟧ , Γ⁴ ⟫Π[ ⟦u₁⟧ ] (dom⟦u₂⟧ , ⟦u₂⟧))

\end{code}

(4) u₄' ::=  f : ₂ℕ → ℕ, n : ℕ, α : ₂ℕ ⊢ ₂ℕ

    u₄  ::=  f : ₂ℕ → ℕ, n : ℕ, α : ₂ℕ ⊢ Π (β : ₂ℕ) (α ＝⟦n⟧ β → f α ＝ f β)

\begin{code}

Γ³ : Space
Γ³ = ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) ⊗ ℕSpace ⊗ (ℕSpace ⇒ 𝟚Space)

⟦u₄'⟧ : Map Γ⁴ Γ³
⟦u₄'⟧ = cpr₁ Γ³ (ℕSpace ⇒ 𝟚Space)

dom⟦u₄⟧ : Space
dom⟦u₄⟧ = dom⟪ Γ⁴ , Γ³ ⟫Π[ ⟦u₄'⟧ ] (dom⟦u₃⟧ , ⟦u₃⟧)

⟦u₄⟧ : Map dom⟦u₄⟧ Γ³
⟦u₄⟧ = pr₂ (⟪ Γ⁴ , Γ³ ⟫Π[ ⟦u₄'⟧ ] (dom⟦u₃⟧ , ⟦u₃⟧))

\end{code}

(5) u₅' ::=  f : ₂ℕ → ℕ, n : ℕ ⊢ ₂ℕ

    u₅  ::=  f : ₂ℕ → ℕ, n : ℕ ⊢ Π(α : ₂ℕ)  Π(β : ₂ℕ) (α ＝⟦n⟧ β → f α ＝ f β)

\begin{code}

Γ² : Space
Γ² = ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) ⊗ ℕSpace

⟦u₅'⟧ : Map Γ³ Γ²
⟦u₅'⟧ = cpr₁ Γ² (ℕSpace ⇒ 𝟚Space)

dom⟦u₅⟧ : Space
dom⟦u₅⟧ = dom⟪ Γ³ , Γ² ⟫Π[ ⟦u₅'⟧ ] (dom⟦u₄⟧ , ⟦u₄⟧)

⟦u₅⟧ : Map dom⟦u₅⟧ Γ²
⟦u₅⟧ = pr₂ (⟪ Γ³ , Γ² ⟫Π[ ⟦u₅'⟧ ] (dom⟦u₄⟧ , ⟦u₄⟧))

\end{code}

(6) u₆' ::=  f : ₂ℕ → ℕ ⊢ ℕ

    u₆  ::=  f : ₂ℕ → ℕ ⊢ Σ (n : ℕ)  Π(α : ₂ℕ)  Π(β : ₂ℕ) (α ＝⟦n⟧ β → f α ＝ f β)

\begin{code}

Γ¹ : Space
Γ¹ = (ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace

⟦u₆'⟧ : Map Γ² Γ¹
⟦u₆'⟧ = cpr₁ Γ¹ ℕSpace

dom⟦u₆⟧ : Space
dom⟦u₆⟧ = dom⟪ Γ² , Γ¹ ⟫Σ[ ⟦u₆'⟧ ] (dom⟦u₅⟧ , ⟦u₅⟧)

⟦u₆⟧ : Map dom⟦u₆⟧ Γ¹
⟦u₆⟧ = pr₂ (⟪ Γ² , Γ¹ ⟫Σ[ ⟦u₆'⟧ ] (dom⟦u₅⟧ , ⟦u₅⟧))

\end{code}

(7) uc  ::=  ⊢ Π (f : ₂ℕ → ℕ)  Σ (n : ℕ)  Π (α β : ₂ℕ) (α ＝⟦n⟧ β → f α ＝ f β).

\begin{code}

Γ⁰ : Space
Γ⁰ = 𝟙Space

dom⟦uc⟧ : Space
dom⟦uc⟧ = dom⟪ Γ¹ , Γ⁰ ⟫Π[ continuous-unit Γ¹ ] (dom⟦u₆⟧ , ⟦u₆⟧)

\end{code}

The Space dom⟦uc⟧ is inhabited. One inhabitant is the following, which
is defined using the fan functional.

\begin{code}

uc : U dom⟦uc⟧
uc = (⋆ , h , cts) , (λ _ → refl)
 where
  dom-h : Space
  dom-h = Subspace ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) (λ _ → ⋆ ＝ ⋆)
       -- ⟪ Γ¹ , Γ⁰ ⟫ (continuous-unit {Γ¹}) ⁻¹₍ ⋆ ₎
  cod-h : Space
  cod-h = Subspace dom⟦u₅⟧ (λ _ → ⋆ ＝ ⋆)
       -- ⟪ dom⟦u₆⟧ , Γ⁰ ⟫ (⟪ dom⟦u₆⟧ , Γ¹ , Γ⁰ ⟫ (continuous-unit {Γ¹}) ○ ⟦u₆⟧) ⁻¹₍ ⋆ ₎
  h : U dom-h → U cod-h
  h (f , _) = (((f , pr₁ fan f) , h₁ , cts₁) , (λ _ → refl)) , refl
   where
    dom-h₁ : Space
    dom-h₁ = Subspace Γ³ (λ w → pr₁ w ＝ (f , pr₁ fan f))
          -- ⟪ Γ³ , Γ² ⟫ ⟦u₅'⟧ ⁻¹₍ (f , pr₁ fan f) ₎
    cod-h₁ : Space
    cod-h₁ = Subspace dom⟦u₄⟧ (λ w → pr₁ (pr₁ ⟦u₄⟧ w) ＝ (f , pr₁ fan f))
          -- ⟪ dom⟦u₄⟧ , Γ² ⟫ ⟪ dom⟦u₄⟧ , Γ³ , Γ² ⟫ ⟦u₅'⟧ ○ ⟦u₄⟧ ⁻¹₍ (f , pr₁ fan f) ₎
    h₁ : U dom-h₁ → U cod-h₁
    h₁ (((f₁ , n₁) , α) , e₁) = (((((f₁ , n₁) , α)) , h₂ , cts₂) , (λ _ → refl)) , e₁
     where
      dom-h₂ : Space
      dom-h₂ = Subspace Γ⁴ (λ w → pr₁ w ＝ ((f₁ , n₁) , α))
            -- ⟪ Γ⁴ , Γ³ ⟫ ⟦u₄'⟧ ⁻¹₍ ((f₁ , n₁) , α) ₎
      cod-h₂ : Space
      cod-h₂ = Subspace dom⟦u₃⟧ (λ w → pr₁ (pr₁ ⟦u₃⟧ w) ＝ ((f₁ , n₁) , α))
            -- ⟪ dom⟦u₃⟧ , Γ³ ⟫ ⟪ dom⟦u₃⟧ , Γ⁴ , Γ³ ⟫ ⟦u₄'⟧ ○ ⟦u₃⟧ ⁻¹₍ ((f₁ , n₁) , α) ₎
      h₂ : U dom-h₂ → U cod-h₂
      h₂ ((((f₂ , n₂) , α₂) , β) , e₂) = (((((f₂ , n₂) , α₂) , β) , h₃ , cts₃) , (λ _ → refl)) , e₂
       where
        dom-h₃ : Space
        dom-h₃ = Subspace dom⟦u₁⟧ (λ w → pr₁ w ＝ (((f₂ , n₂) , α₂) , β))
              -- ⟪ dom⟦u₁⟧ , Γ⁴ ⟫ ⟦u₁⟧ ⁻¹₍ (((f₂ , n₂) , α₂) , β) ₎
        cod-h₃ : Space
        cod-h₃ = Subspace dom⟦u₂⟧ (λ w → pr₁ (pr₁ w) ＝ (((f₂ , n₂) , α₂) , β))
              -- ⟪ dom⟦u₂⟧ , Γ⁴ ⟫ ⟪ dom⟦u₂⟧ , dom⟦u₁⟧ , Γ⁴ ⟫ ⟦u₁⟧ ○ ⟦u₂⟧ ⁻¹₍ (((f₂ , n₂) , α₂) , β) ₎
        h₃ : U dom-h₃ → U cod-h₃
        h₃ (((((f₃ , n₃) , α₃) , β₃) , en₃) , e₃) = (((((f₃ , n₃) , α₃) , β₃) , en₃) , goal) , e₃
         where
--        e₁ : [ (f₁ , n₁) ＝ (f , pr₁ fan f) ]
--        e₂ : [ ((f₂ , n₂) , α₂) ＝ ((f₁ , n₁) , α) ]
--        e₃ : [ (((f₃ , n₃) , α₃) , β₃) ＝ (((f₂ , n₂) , α₂) , β) ]
          eq₃₂ : (f₃ , n₃) ＝ (f₂ , n₂)
          eq₃₂ = ap (pr₁ ∘ pr₁) e₃
          eq₂₁ : (f₂ , n₂) ＝ (f₁ , n₁)
          eq₂₁ = ap pr₁ e₂
          eq₃₀ : (f₃ , n₃) ＝ (f , pr₁ fan f)
          eq₃₀ = eq₃₂  ∙ eq₂₁ ∙ e₁
          eqf : f₃ ＝ f
          eqf = ap pr₁ eq₃₀
          eqn : n₃ ＝ pr₁ fan f
          eqn = ap pr₂ eq₃₀
          eqn₃ : n₃ ＝ pr₁ fan f₃
          eqn₃ = transport (λ x → n₃ ＝ pr₁ fan x) (eqf ⁻¹) eqn
          en₃' : pr₁ α₃ ＝⟦ pr₁ fan f₃ ⟧ pr₁ β₃
          en₃' = transport (λ x → pr₁ α₃ ＝⟦ x ⟧ pr₁ β₃) eqn₃ en₃
          goal : pr₁ f₃ α₃ ＝ pr₁ f₃ β₃
          goal = fan-behaviour f₃ α₃ β₃ en₃'
                 -------------
        cts₃ : continuous dom-h₃ cod-h₃ h₃
            -- ∀(p : ₂ℕ → U dom-h₃) → pr₁ ∘ pr₁ ∘ p ∈ Probe Γ⁴ →
            -- pr₁ ∘ pr₁ ∘ pr₁ ∘ h₃ ∘ p ∈ Probe Γ⁴
        cts₃ _ pP = pP

      cts₂ : continuous dom-h₂ cod-h₂ h₂
          -- ∀(p : ₂ℕ → U dom-h₂) → pr₁ ∘ p ∈ Probe Γ⁴ → pr₁ ∘ h₂ ∘ p ∈ Probe dom⟦u₃⟧
      cts₂ _ pP = pP , (λ _ _ _ qQ _ → qQ)

    cts₁ : continuous dom-h₁ cod-h₁ h₁
        -- ∀(p : ₂ℕ → U dom-h₁) → pr₁ ∘ p ∈ Probe Γ³ → pr₁ ∘ h₁ ∘ p ∈ Probe dom⟦u₄⟧
    cts₁ _ pP = pP , (λ _ _ _ qQ _ → qQ , (λ _ _ _ rR _ → rR))

  cts : continuous dom-h cod-h h
     -- ∀(p : ₂ℕ → U dom-h) → pr₁ ∘ p ∈ Probe ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) →
     -- pr₁ ∘ h ∘ p ∈ Probe dom⟦u₅⟧
  cts p pP = (pP , (pr₂ fan (pr₁ ∘ p) pP)) ,
                 (λ _ _ _ qQ _ → qQ , (λ _ _ _ rR _ → rR , (λ _ _ _ sS _ → sS)))

\end{code}

To validate UC is equivalent to inhabit the space dom⟦uc⟧.

\begin{code}

UC-is-validated : Set
UC-is-validated = U dom⟦uc⟧

Theorem : UC-is-validated
Theorem = uc

\end{code}
