Martin Escardo, August 2026

The Brouwer ordinal codes are embedded into the inductive-recursive
universe E of ordinal codes of the module
Ordinals.InductiveRecursiveCodesInterpretations.

The embedding commutes with both the discrete and the compact
interpretations, in each case up to order equivalence rather than on
the nose.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Ordinals.BrouwerCodesIntoInductiveRecursiveCodes
        (fe : FunExt)
       where

open import CoNaturals.Type
open import MLTT.Plus-Properties
open import Notation.CanonicalMap hiding (ι)
open import Ordinals.Arithmetic fe
open import Ordinals.BrouwerCodes
open import Ordinals.BrouwerCodesDiscreteAndCompactInterpretations fe
       using (Δ ; Κ)
open import Ordinals.Closure fe
open import Ordinals.Equivalence
open import Ordinals.InductiveRecursiveCodesInterpretations fe
       using (E ; ⌜𝟙⌝ ; ⌜ω+𝟙⌝ ; _⌜+⌝_ ; _⌜×⌝_ ; ⌜Σ⌝ ; E-is-set ; 𝓚)
       renaming (Δ to Δᴱ ; Κ to Κᴱ)
open import Ordinals.Injectivity
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import TypeTopology.SquashedSum fe
open import UF.Base
open import UF.Embeddings
open import UF.Equiv

open topped-ordinals-injectivity fe

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

\end{code}

The translation of the limit constructor works because the discrete
interpretation of the code for ω + 1 has underlying type ℕ + 𝟙, which
is exactly the index that ∑₁ sums over, so that the family can be
given by cases, with the added point sent to the code for 𝟙.

\begin{code}

B-to-E : B → E
B-to-E Z     = ⌜𝟙⌝
B-to-E (S b) = B-to-E b ⌜+⌝ ⌜𝟙⌝
B-to-E (L b) = ⌜Σ⌝ ⌜ω+𝟙⌝ (cases (λ n → B-to-E (b n)) (λ _ → ⌜𝟙⌝))

B-to-E-lc : left-cancellable B-to-E
B-to-E-lc {Z}   {Z}    p = refl
B-to-E-lc {S b} {S b'} p = ap S (B-to-E-lc (ap plus-left p))
 where
  plus-left : E → E
  plus-left ⌜𝟙⌝       = ⌜𝟙⌝
  plus-left ⌜ω+𝟙⌝     = ⌜𝟙⌝
  plus-left (ν ⌜+⌝ μ) = ν
  plus-left (ν ⌜×⌝ μ) = ⌜𝟙⌝
  plus-left (⌜Σ⌝ ν A) = ⌜𝟙⌝
B-to-E-lc {L b} {L b'} p = ap L (dfunext fe₀ I)
 where
  sigma-family : E → (ℕ + 𝟙 → E)
  sigma-family ⌜𝟙⌝                = λ _ → ⌜𝟙⌝
  sigma-family ⌜ω+𝟙⌝              = λ _ → ⌜𝟙⌝
  sigma-family (ν ⌜+⌝ μ)          = λ _ → ⌜𝟙⌝
  sigma-family (ν ⌜×⌝ μ)          = λ _ → ⌜𝟙⌝
  sigma-family (⌜Σ⌝ ⌜𝟙⌝ A)        = λ _ → ⌜𝟙⌝
  sigma-family (⌜Σ⌝ ⌜ω+𝟙⌝ A)      = A
  sigma-family (⌜Σ⌝ (ν ⌜+⌝ μ) A)  = λ _ → ⌜𝟙⌝
  sigma-family (⌜Σ⌝ (ν ⌜×⌝ μ) A)  = λ _ → ⌜𝟙⌝
  sigma-family (⌜Σ⌝ (⌜Σ⌝ ν A) A') = λ _ → ⌜𝟙⌝

  I : (n : ℕ) → b n ＝ b' n
  I n = B-to-E-lc (happly (ap sigma-family p) (inl n))

\end{code}

Since the inductive-recursive universe is a set, this makes the
inclusion an embedding.

\begin{code}

B-to-E-is-embedding : is-embedding B-to-E
B-to-E-is-embedding = lc-maps-into-sets-are-embeddings
                       B-to-E
                       B-to-E-lc
                       E-is-set

\end{code}

The inclusion commutes with the discrete interpretations, up to order
equivalence.

\begin{code}

Δ-agreement : (b : B) → [ Δ b ] ≃ₒ [ Δᴱ (B-to-E b) ]
Δ-agreement Z     = ≃ₒ-refl [ 𝟙ᵒ ]
Δ-agreement (S b) = ∑-≃ₒ
                     𝟚ᵒ
                     (cases (λ _ → Δ b) (λ _ → 𝟙ᵒ))
                     (cases (λ _ → Δᴱ (B-to-E b)) (λ _ → 𝟙ᵒ))
                     (dep-cases
                       (λ _ → Δ-agreement b)
                       (λ _ → ≃ₒ-refl [ 𝟙ᵒ ]))
Δ-agreement (L b) = ∑-≃ₒ
                     (succₒ ω)
                     ((Δ ∘ b) ↗ (over , over-embedding))
                     (Δᴱ ∘ cases (λ n → B-to-E (b n)) (λ _ → ⌜𝟙⌝))
                     I
 where
  I : (z : ℕ + 𝟙)
    → [ ((Δ ∘ b) ↗ (over , over-embedding)) z ]
    ≃ₒ [ Δᴱ (cases (λ n → B-to-E (b n)) (λ _ → ⌜𝟙⌝) z) ]
  I (inl n) = ≃ₒ-trans
               [ ((Δ ∘ b) ↗ (over , over-embedding)) (inl n) ]
               [ Δ (b n) ]
               [ Δᴱ (B-to-E (b n)) ]
               (↗-propertyₒ (Δ ∘ b) (over , over-embedding) n)
               (Δ-agreement (b n))
  I (inr ⋆) = ↗-out-of-range
               (Δ ∘ b)
               (over , over-embedding)
               (inr ⋆)
               (λ n → +disjoint)

\end{code}

The inclusion also commutes with the compact interpretations.

\begin{code}

Κ-agreement : (b : B) → [ Κ b ] ≃ₒ [ Κᴱ (B-to-E b) ]
Κ-agreement Z     = ≃ₒ-refl [ 𝟙ᵒ ]
Κ-agreement (S b) = ∑-≃ₒ
                     𝟚ᵒ
                     (cases (λ _ → Κ b) (λ _ → 𝟙ᵒ))
                     (cases (λ _ → Κᴱ (B-to-E b)) (λ _ → 𝟙ᵒ))
                     (dep-cases
                       (λ _ → Κ-agreement b)
                       (λ _ → ≃ₒ-refl [ 𝟙ᵒ ]))
Κ-agreement (L b) = ∑-≃ₒ ℕ∞ᵒ ((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) (𝓚 ⌜ω+𝟙⌝ A) I
 where
  A : ℕ + 𝟙 → E
  A = cases (λ n → B-to-E (b n)) (λ _ → ⌜𝟙⌝)

  κ κᴱ : ℕ → Ordinal 𝓤₀
  κ  n = [ Κ (b n) ]
  κᴱ n = [ Κᴱ (B-to-E (b n)) ]

  h : (n : ℕ) → ⟨ κ n ⟩ → ⟨ κᴱ n ⟩
  h n = ≃ₒ-to-fun (κ n) (κᴱ n) (Κ-agreement (b n))

  h⁻¹ : (n : ℕ) → ⟨ κᴱ n ⟩ → ⟨ κ n ⟩
  h⁻¹ n = ≃ₒ-to-fun⁻¹ (κ n) (κᴱ n) (Κ-agreement (b n))

  he : (n : ℕ) → is-order-equiv (κ n) (κᴱ n) (h n)
  he n = ≃ₒ-to-fun-is-order-equiv (κ n) (κᴱ n) (Κ-agreement (b n))

  hi : (n : ℕ) → is-equiv (h n)
  hi n = order-equivs-are-equivs (κ n) (κᴱ n) (he n)

  I : (u : ℕ∞)
    → [ ((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) u ] ≃ₒ [ 𝓚 ⌜ω+𝟙⌝ A u ]
  I u = f ,
        order-preserving-reflecting-equivs-are-order-equivs
         [ ((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) u ]
         [ 𝓚 ⌜ω+𝟙⌝ A u ]
         f
         f-is-equiv
         f-is-order-preserving
         f-is-order-reflecting
   where
    f : ⟨ ((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) u ⟩ → ⟨ 𝓚 ⌜ω+𝟙⌝ A u ⟩
    f φ (inl n , p) = h n (φ (n , p))
    f φ (inr ⋆ , p) = ⋆

    g : ⟨ 𝓚 ⌜ω+𝟙⌝ A u ⟩ → ⟨ ((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) u ⟩
    g ψ (n , p) = h⁻¹ n (ψ (inl n , p))

    gf : g ∘ f ∼ id
    gf φ = dfunext fe₀
            (λ (n , p) → inverses-are-retractions (h n) (hi n) (φ (n , p)))

    fg : f ∘ g ∼ id
    fg ψ = dfunext fe₀ γ
     where
      γ : (w : fiber ι𝟙 u) → f (g ψ) w ＝ ψ w
      γ (inl n , p) = inverses-are-sections (h n) (hi n) (ψ (inl n , p))
      γ (inr ⋆ , p) = refl

    f-is-equiv : is-equiv f
    f-is-equiv = qinvs-are-equivs f (g , gf , fg)

    f-is-order-preserving : is-order-preserving
                             (((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) u)
                             (𝓚 ⌜ω+𝟙⌝ A u)
                             f
    f-is-order-preserving φ φ' ((n , p) , l) =
     (inl n , p) ,
     order-equivs-are-order-preserving (κ n) (κᴱ n) (he n)
      (φ (n , p)) (φ' (n , p)) l

    f-is-order-reflecting : is-order-reflecting
                             (((Κ ∘ b) ↗ embedding-ℕ-to-ℕ∞ fe₀) u)
                             (𝓚 ⌜ω+𝟙⌝ A u)
                             f
    f-is-order-reflecting φ φ' ((inl n , p) , l) =
     (n , p) ,
     order-equivs-are-order-reflecting (κ n) (κᴱ n) (h n) (he n)
      (φ (n , p)) (φ' (n , p)) l
    f-is-order-reflecting φ φ' ((inr ⋆ , p) , l) = 𝟘-elim l

\end{code}
