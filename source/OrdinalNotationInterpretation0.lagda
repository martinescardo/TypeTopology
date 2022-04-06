Martin Escardo, 4th April 2022

See the 2018 file OrdinalNotationInterpretation1 for discussion.

We interpret Brouwer ordinal codes as ordinals in two ways and relate
them.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import SpartanMLTT
open import UF-Univalence
open import UF-PropTrunc

module OrdinalNotationInterpretation0
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons
open import UF-UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open PropositionalTruncation pt

open import UF-ImageAndSurjection
open import UF-Embeddings
open import UF-Quotient-Axiomatically

open import ConvergentSequenceCompact
open import CompactTypes
open import GenericConvergentSequence
open import OrdinalCodes
open import OrdinalsType
open import OrdinalArithmetic fe
open import OrdinalArithmetic-Properties ua
open import OrdinalOfOrdinalsSuprema ua
open import OrdinalOfOrdinals ua
open import OrdinalsType-Injectivity fe
open import Plus-Properties
open import PropTychonoff
open import SquashedSum fe
open import ToppedOrdinalArithmetic fe
open import ToppedOrdinalsType fe

open ImageAndSurjection pt
open ordinals-injectivity

module _ (sq : set-quotients-exist) where

 open suprema sq

 private
  extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
  extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')

 brouwer-ordinal₀ : B → Ordinal 𝓤₀
 brouwer-ordinal₀ Z     = 𝟘ₒ
 brouwer-ordinal₀ (S b) = brouwer-ordinal₀ b +ₒ 𝟙ₒ
 brouwer-ordinal₀ (L b) = sup (λ i → brouwer-ordinal₀ (b i))

 brouwer-ordinal₁ : B → Ordinal 𝓤₀
 brouwer-ordinal₁ Z     = 𝟙ₒ
 brouwer-ordinal₁ (S b) = brouwer-ordinal₁ b +ₒ 𝟙ₒ
 brouwer-ordinal₁ (L b) = sup (extension (brouwer-ordinal₁ ∘ b))

 brouwer-ordinal₁-is-compact∙ : (b : B) → compact∙ ⟨ brouwer-ordinal₁ b ⟩
 brouwer-ordinal₁-is-compact∙ Z     = 𝟙-compact∙
 brouwer-ordinal₁-is-compact∙ (S b) = +-compact∙
                                       (brouwer-ordinal₁-is-compact∙ b)
                                       (𝟙-compact∙)
 brouwer-ordinal₁-is-compact∙ (L b) =
   surjection-compact∙ _
    (sum-to-sup (extension (brouwer-ordinal₁ ∘ b)))
    (sum-to-sup-is-surjection (extension (brouwer-ordinal₁ ∘ b)))
    (Σ-compact∙
      (ℕ∞-compact∙ fe')
      (λ u → prop-tychonoff fe
              (ℕ-to-ℕ∞-is-embedding fe' u)
              (λ (i , _) → brouwer-ordinal₁-is-compact∙ (b i))))

 brouwer-ordinal₂ : B → Ordinalᵀ 𝓤₀
 brouwer-ordinal₂ Z     = 𝟙ᵒ
 brouwer-ordinal₂ (S b) = brouwer-ordinal₂ b +ᵒ 𝟙ᵒ
 brouwer-ordinal₂ (L b) = ∑¹ (brouwer-ordinal₂ ∘ b)

 brouwer-ordinal₂-is-compact∙ : (b : B) → compact∙ ⟪ brouwer-ordinal₂ b ⟫
 brouwer-ordinal₂-is-compact∙ Z     = 𝟙-compact∙
 brouwer-ordinal₂-is-compact∙ (S b) = Σ-compact∙ 𝟙+𝟙-compact∙
                                       (dep-cases
                                         (λ _ → brouwer-ordinal₂-is-compact∙ b)
                                         (λ _ → 𝟙-compact∙))
 brouwer-ordinal₂-is-compact∙ (L b) = Σ¹-compact∙
                                        (λ i → ⟪ brouwer-ordinal₂ (b i) ⟫)
                                        (λ i → brouwer-ordinal₂-is-compact∙ (b i))

 comparison₂₋₁ : (b : B) → ⟪ brouwer-ordinal₂ b ⟫ → ⟨ brouwer-ordinal₁ b ⟩
 comparison₂₋₁ Z     x           = x
 comparison₂₋₁ (S b) (inl ⋆ , x) = inl (comparison₂₋₁ b x)
 comparison₂₋₁ (S b) (inr ⋆ , y) = inr ⋆
 comparison₂₋₁ (L b) (u , f)     = sum-to-sup (extension (λ n → brouwer-ordinal₁ (b n))) (u , g)
  where
   g : ((i , _) : fiber ℕ-to-ℕ∞ u) → ⟨ brouwer-ordinal₁ (b i) ⟩
   g (i , p) = comparison₂₋₁ (b i) (f (i , p))

\end{code}

More can be said about this.
