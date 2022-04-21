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
open import UF-Size

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

module _ (sr : Set-Replacement pt) where

 open suprema pt sr

 private
  extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
  extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')

 brouwer-ordinal₀ : B → Ordinal 𝓤₀
 brouwer-ordinal₀ Z     = 𝟘ₒ
 brouwer-ordinal₀ (S b) = brouwer-ordinal₀ b +ₒ 𝟙ₒ
 brouwer-ordinal₀ (L b) = sup (brouwer-ordinal₀ ∘ b)

 brouwer-ordinal₁ : B → Ordinal 𝓤₀
 brouwer-ordinal₁ Z     = 𝟙ₒ
 brouwer-ordinal₁ (S b) = brouwer-ordinal₁ b +ₒ 𝟙ₒ
 brouwer-ordinal₁ (L b) = sup (extension (brouwer-ordinal₁ ∘ b))

 brouwer-ordinal₂ : B → Ordinalᵀ 𝓤₀
 brouwer-ordinal₂ Z     = 𝟙ᵒ
 brouwer-ordinal₂ (S b) = brouwer-ordinal₂ b +ᵒ 𝟙ᵒ
 brouwer-ordinal₂ (L b) = ∑¹ (brouwer-ordinal₂ ∘ b)

 brouwer-ordinal₁-is-compact∙ : (b : B) → compact∙ ⟨ brouwer-ordinal₁ b ⟩
 brouwer-ordinal₁-is-compact∙ Z     = 𝟙-compact∙
 brouwer-ordinal₁-is-compact∙ (S b) = +-compact∙
                                       (brouwer-ordinal₁-is-compact∙ b)
                                       (𝟙-compact∙)
 brouwer-ordinal₁-is-compact∙ (L b) =
   surjection-compact∙ pt
    (sum-to-sup (extension (brouwer-ordinal₁ ∘ b)))
    (sum-to-sup-is-surjection (extension (brouwer-ordinal₁ ∘ b)))
    (Σ-compact∙
      (ℕ∞-compact∙ fe')
      (λ u → prop-tychonoff fe
              (ℕ-to-ℕ∞-is-embedding fe' u)
              (λ (i , _) → brouwer-ordinal₁-is-compact∙ (b i))))

 brouwer-ordinal₂-is-compact∙ : (b : B) → compact∙ ⟪ brouwer-ordinal₂ b ⟫
 brouwer-ordinal₂-is-compact∙ Z     = 𝟙-compact∙
 brouwer-ordinal₂-is-compact∙ (S b) = Σ-compact∙ 𝟙+𝟙-compact∙
                                       (dep-cases
                                         (λ _ → brouwer-ordinal₂-is-compact∙ b)
                                         (λ _ → 𝟙-compact∙))
 brouwer-ordinal₂-is-compact∙ (L b) = Σ¹-compact∙
                                        (λ i → ⟪ brouwer-ordinal₂ (b i) ⟫)
                                        (λ i → brouwer-ordinal₂-is-compact∙ (b i))

\end{code}

The successor function on ordinals is not necessarily monotone, but it
is if excluded middle holds.

\begin{code}

 open import UF-ExcludedMiddle

 comparison₀₁ : EM 𝓤₁ → (b : B) → brouwer-ordinal₀ b ⊴ brouwer-ordinal₁ b
 comparison₀₁ em Z     = 𝟘ₒ-least-⊴ 𝟙ₒ
 comparison₀₁ em (S b) = succ-monotone em (brouwer-ordinal₀ b) (brouwer-ordinal₁ b) (comparison₀₁ em b)
 comparison₀₁ em (L b) = VI
  where
   I : (n : ℕ) → brouwer-ordinal₀ (b n) ⊴ brouwer-ordinal₁ (b n)
   I n = comparison₀₁ em (b n)

   II : (n : ℕ) → extension (brouwer-ordinal₁ ∘ b) (ℕ-to-ℕ∞ n)
                ≡ brouwer-ordinal₁ (b n)
   II n = eqtoidₒ _ _ (↗-property (brouwer-ordinal₁ ∘ b) (embedding-ℕ-to-ℕ∞ fe') n)

   III : (n : ℕ) → brouwer-ordinal₀ (b n)
                 ⊴ extension (brouwer-ordinal₁ ∘ b) (ℕ-to-ℕ∞ n)
   III n = transport (brouwer-ordinal₀ (b n) ⊴_) ((II n)⁻¹) (I n)

   IV : sup (brouwer-ordinal₀ ∘ b) ⊴ sup (extension (brouwer-ordinal₁ ∘ b) ∘ ℕ-to-ℕ∞)
   IV = sup-monotone _ _ III

   V : sup (extension (brouwer-ordinal₁ ∘ b) ∘ ℕ-to-ℕ∞) ⊴ sup (extension (brouwer-ordinal₁ ∘ b))
   V = sup-is-lower-bound-of-upper-bounds _ _ (λ n → sup-is-upper-bound _ (ℕ-to-ℕ∞ n))

   VI : sup (brouwer-ordinal₀ ∘ b) ⊴ sup (extension (brouwer-ordinal₁ ∘ b))
   VI = ⊴-trans _ _ _ IV V

 comparison₂₁ : (b : B) → ⟪ brouwer-ordinal₂ b ⟫ → ⟨ brouwer-ordinal₁ b ⟩
 comparison₂₁ Z     x           = x
 comparison₂₁ (S b) (inl ⋆ , x) = inl (comparison₂₁ b x)
 comparison₂₁ (S b) (inr ⋆ , y) = inr ⋆
 comparison₂₁ (L b) (u , f)     = sum-to-sup
                                   (extension (brouwer-ordinal₁ ∘ b))
                                   (u , g)
  where
   g : ((i , _) : fiber ℕ-to-ℕ∞ u) → ⟨ brouwer-ordinal₁ (b i) ⟩
   g (i , p) = comparison₂₁ (b i) (f (i , p))

\end{code}

Question. Is the function comparison₂₁ a surjection?
