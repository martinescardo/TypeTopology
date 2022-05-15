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
open import OrdinalsType-Injectivity
open import Plus-Properties
open import PropTychonoff
open import SquashedSum fe
open import OrdinalToppedArithmetic fe
open import OrdinalsToppedType fe

open ImageAndSurjection pt
open ordinals-injectivity fe

module _ (sr : Set-Replacement pt) where

 open suprema pt sr

 private
  extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
  extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')

 ⟦_⟧₀ : B → Ordinal 𝓤₀
 ⟦ Z ⟧₀   = 𝟘ₒ
 ⟦ S b ⟧₀ = ⟦ b ⟧₀ +ₒ 𝟙ₒ
 ⟦ L b ⟧₀ = sup (λ i → ⟦ b i ⟧₀)

 ⟦_⟧₂ : B → Ordinal 𝓤₀
 ⟦ Z ⟧₂   = 𝟙ₒ
 ⟦ S b ⟧₂ = ⟦ b ⟧₂ +ₒ 𝟙ₒ
 ⟦ L b ⟧₂ = sup (extension (λ i → ⟦ b i ⟧₂))

 ⟦_⟧₃ : B → Ordinalᵀ 𝓤₀
 ⟦ Z ⟧₃   = 𝟙ᵒ
 ⟦ S b ⟧₃ = ⟦ b ⟧₃ +ᵒ 𝟙ᵒ
 ⟦ L b ⟧₃ = ∑¹ (λ i → ⟦ b i ⟧₃)

 ⟦_⟧₂-is-compact∙ : (b : B) → compact∙ ⟨ ⟦ b ⟧₂ ⟩
 ⟦ Z ⟧₂-is-compact∙    = 𝟙-compact∙
 ⟦ S b ⟧₂-is-compact∙  = +-compact∙ ⟦ b ⟧₂-is-compact∙ (𝟙-compact∙)
 ⟦ L b ⟧₂-is-compact∙ =
   surjection-compact∙ pt
    (sum-to-sup (extension (λ i → ⟦ b i ⟧₂)))
    (sum-to-sup-is-surjection (extension (λ i → ⟦ b i ⟧₂)))
    (Σ-compact∙
      (ℕ∞-compact∙ fe')
      (λ u → prop-tychonoff fe
              (ℕ-to-ℕ∞-is-embedding fe' u)
              (λ (i , _) → ⟦ b i ⟧₂-is-compact∙)))

 ⟦_⟧₃-is-compact∙ : (b : B) → compact∙ ⟪ ⟦_⟧₃ b ⟫
 ⟦ Z ⟧₃-is-compact∙   = 𝟙-compact∙
 ⟦ S b ⟧₃-is-compact∙ = Σ-compact∙ 𝟙+𝟙-compact∙
                         (dep-cases
                           (λ _ → ⟦ b ⟧₃-is-compact∙)
                           (λ _ → 𝟙-compact∙))
 ⟦ L b ⟧₃-is-compact∙ = Σ¹-compact∙
                          (λ i → ⟪ ⟦ b i ⟧₃ ⟫)
                          (λ i → ⟦ b i ⟧₃-is-compact∙)
\end{code}

The successor function on ordinals is not necessarily monotone, but it
is if excluded middle holds.

\begin{code}

 open import UF-ExcludedMiddle

 comparison₀₂ : EM 𝓤₁ → (b : B) → ⟦ b ⟧₀ ⊴ ⟦ b ⟧₂
 comparison₀₂ em Z     = 𝟘ₒ-least-⊴ 𝟙ₒ
 comparison₀₂ em (S b) = succ-monotone em ⟦ b ⟧₀ ⟦ b ⟧₂ (comparison₀₂ em b)
 comparison₀₂ em (L b) = VI
  where
   I : (n : ℕ) → ⟦ b n ⟧₀ ⊴ ⟦ b n ⟧₂
   I n = comparison₀₂ em (b n)

   II : (n : ℕ) → extension (λ i → ⟦ b i ⟧₂) (ℕ-to-ℕ∞ n) ≡ ⟦ b n ⟧₂
   II n = eqtoidₒ _ _ (↗-property (λ i → ⟦ b i ⟧₂) (embedding-ℕ-to-ℕ∞ fe') n)

   III : (n : ℕ) → ⟦ b n ⟧₀ ⊴ extension (λ i → ⟦ b i ⟧₂) (ℕ-to-ℕ∞ n)
   III n = transport (⟦_⟧₀ (b n) ⊴_) ((II n)⁻¹) (I n)

   IV : sup (λ i → ⟦ b i ⟧₀) ⊴ sup (extension (λ i → ⟦ b i ⟧₂) ∘ ℕ-to-ℕ∞)
   IV = sup-monotone _ _ III

   V : sup (extension (λ i → ⟦ b i ⟧₂) ∘ ℕ-to-ℕ∞) ⊴ sup (extension (λ i → ⟦ b i ⟧₂))
   V = sup-is-lower-bound-of-upper-bounds _ _ (λ n → sup-is-upper-bound _ (ℕ-to-ℕ∞ n))

   VI : sup (λ i → ⟦ b i ⟧₀) ⊴ sup (extension (λ i → ⟦ b i ⟧₂))
   VI = ⊴-trans _ _ _ IV V

 comparison₃₂ : (b : B) → ⟪ ⟦ b ⟧₃ ⟫ → ⟨ ⟦ b ⟧₂ ⟩
 comparison₃₂ Z     x           = x
 comparison₃₂ (S b) (inl ⋆ , x) = inl (comparison₃₂ b x)
 comparison₃₂ (S b) (inr ⋆ , y) = inr ⋆
 comparison₃₂ (L b) (u , f)     = sum-to-sup
                                   (extension (λ i → ⟦ b i ⟧₂))
                                   (u , g)
  where
   g : ((i , _) : fiber ℕ-to-ℕ∞ u) → ⟨ ⟦ b i ⟧₂ ⟩
   g (i , p) = comparison₃₂ (b i) (f (i , p))

\end{code}

Question. Is the function comparison₃₂ a surjection?
