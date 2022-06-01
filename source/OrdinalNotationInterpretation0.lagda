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
open import OrdinalsTrichotomousType fe
open import OrdinalTrichotomousArithmetic fe
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

 ⟦_⟧₁ : B → Ordinal₃ 𝓤₀
 ⟦ Z ⟧₁    = 𝟘₃
 ⟦ S b ⟧₁  = ⟦ b ⟧₁ +₃ 𝟙₃
 ⟦ L b ⟧₁  = ∑³ ω₃ (λ i → ⟦ b i ⟧₁)

 ⟦_⟧₂ : B → Ordinal 𝓤₀
 ⟦ Z ⟧₂   = 𝟙ₒ
 ⟦ S b ⟧₂ = ⟦ b ⟧₂ +ₒ 𝟙ₒ
 ⟦ L b ⟧₂ = sup (extension (λ i → ⟦ b i ⟧₂))

 ⟦_⟧₃ : B → Ordinalᵀ 𝓤₀
 ⟦ Z ⟧₃   = 𝟙ᵒ
 ⟦ S b ⟧₃ = ⟦ b ⟧₃ +ᵒ 𝟙ᵒ
 ⟦ L b ⟧₃ = ∑¹ (λ i → ⟦ b i ⟧₃)

\end{code}

We'll prove the following inequalities, where the arrows represent the
relation _⊴_ on ordinals, under the assumption of excluded middle:

 ⟦ b ⟧₀ → ⟦ b ⟧₁
   ↓       ↓
 ⟦ b ⟧₂ → ⟦ b ⟧₃

But we first show that ⟦ b ⟧₂ and ⟦ b ⟧₃ are compact. And pointed. The
pointedness is absolutely essential in the proofs by induction, via
the indirect use of prop-tychonoff in Σ¹, because a version of
prop-tychonoff without pointedness implies excluded middle. And this
is why we defined the base cases to be 𝟙 rather than 𝟘.

\begin{code}

 ⟦_⟧₂-is-compact∙ : (b : B) → compact∙ ⟨ ⟦ b ⟧₂ ⟩
 ⟦ Z ⟧₂-is-compact∙   = 𝟙-compact∙
 ⟦ S b ⟧₂-is-compact∙ = +-compact∙ ⟦ b ⟧₂-is-compact∙ (𝟙-compact∙)
 ⟦ L b ⟧₂-is-compact∙ =
   surjection-compact∙ pt
    (sum-to-sup (extension (λ i → ⟦ b i ⟧₂)))
    (sum-to-sup-is-surjection (extension (λ i → ⟦ b i ⟧₂)))
    (Σ¹-compact∙
       (λ i → ⟨ ⟦ b i ⟧₂ ⟩)
       (λ i → ⟦ b i ⟧₂-is-compact∙ ))

 ⟦_⟧₃-is-compact∙ : (b : B) → compact∙ ⟪ ⟦ b ⟧₃ ⟫
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
 open import OrdinalsSupSum ua

 comparison₀₁ : Excluded-Middle → (b : B) → ⟦ b ⟧₀ ⊴ ⁅ ⟦ b ⟧₁ ⁆
 comparison₀₁ em Z     = ⊴-refl 𝟘ₒ
 comparison₀₁ em (S b) = succ-monotone em ⟦ b ⟧₀ ⁅ ⟦ b ⟧₁ ⁆ (comparison₀₁ em b)
 comparison₀₁ em (L b) = IV
  where
   I : (i : ℕ) → ⟦ b i ⟧₀ ⊴ ⁅ ⟦ b i ⟧₁ ⁆
   I i = comparison₀₁ em (b i)

   II : sup (λ i → ⟦ b i ⟧₀) ⊴ sup (λ i → ⁅ ⟦ b i ⟧₁ ⁆)
   II = sup-monotone (λ i → ⟦ b i ⟧₀) (λ i → ⁅ ⟦ b i ⟧₁ ⁆) I

   III : sup (λ i → ⁅ ⟦ b i ⟧₁ ⁆)  ⊴ ⁅ ∑³ ω₃ (λ i → ⟦ b i ⟧₁) ⁆
   III = sup-bounded-by-sum₃ em pt sr _ _

   IV : sup (λ i → ⟦ b i ⟧₀) ⊴ ⁅ ∑³ ω₃ (λ i → ⟦ b i ⟧₁) ⁆
   IV = ⊴-trans _ _ _ II III

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

 comparison₂₃ : Excluded-Middle → (b : B) → ⟦ b ⟧₂ ⊴ [ ⟦ b ⟧₃ ]
 comparison₂₃ em Z     = ⊴-refl 𝟙ₒ
 comparison₂₃ em (S b) = III
  where
   I : (⟦ b ⟧₂ +ₒ 𝟙ₒ) ⊴ ([ ⟦ b ⟧₃ ] +ₒ 𝟙ₒ)
   I = succ-monotone em (⟦ b ⟧₂) [ ⟦ b ⟧₃ ] (comparison₂₃ em b)

   II : [ ⟦ b ⟧₃ +ᵒ 𝟙ᵒ ] ≡ ([ ⟦ b ⟧₃ ] +ₒ 𝟙ₒ)
   II = alternative-plus (⟦ b ⟧₃) 𝟙ᵒ

   III : (⟦ b ⟧₂ +ₒ 𝟙ₒ) ⊴ [ ⟦ b ⟧₃ +ᵒ 𝟙ᵒ ]
   III = transport⁻¹ ((⟦ b ⟧₂ +ₒ 𝟙ₒ) ⊴_) II I

 comparison₂₃ em (L b) = V
  where
   α : ℕ∞ → Ordinal 𝓤₀
   α = extension (λ i → ⟦ b i ⟧₂)

   β : ℕ∞ → Ordinal 𝓤₀
   β = extension (λ i → [ ⟦ b i ⟧₃ ])

   τ : ℕ∞ → Ordinalᵀ 𝓤₀
   τ = topped-ordinals-injectivity._↗_ fe (λ i → ⟦ b i ⟧₃) (embedding-ℕ-to-ℕ∞ fe')

   I : (i : ℕ) →  ⟦ b i ⟧₂ ⊴ [ ⟦ b i ⟧₃ ]
   I i = comparison₂₃ em (b i)

   II : (u : ℕ∞) → α u ⊴ β u
   II = ordinals-injectivity-order.↗-preserves-⊴ ua (embedding-ℕ-to-ℕ∞ fe') _ _ I

   III : sup α ⊴ sup β
   III = sup-monotone α β II

   IV : sup β ⊴ [ ∑ ℕ∞ᵒ τ ]
   IV = sup-bounded-by-sumᵀ em pt sr ℕ∞ᵒ τ

   V : sup α ⊴ [ ∑ ℕ∞ᵒ τ ]
   V = ⊴-trans _ _ _ III IV

 map₁₃ : (b : B) → ⦅ ⟦ b ⟧₁ ⦆ → ⟪ ⟦ b ⟧₃ ⟫
 map₁₃ Z     x = unique-from-𝟘 x
 map₁₃ (S b) (inl x) = inl ⋆ , map₁₃ b x
 map₁₃ (S b) (inr x) = inr ⋆ , ⋆
 map₁₃ (L b) (i , x) = ℕ-to-ℕ∞ i , f
  where
   f : ((j , p) : fiber ℕ-to-ℕ∞ (ℕ-to-ℕ∞ i)) → ⟪ ⟦ b j ⟧₃ ⟫
   f (j , p) = transport⁻¹ (λ - → ⟪ ⟦ b - ⟧₃ ⟫) (ℕ-to-ℕ∞-lc p) (map₁₃ (b i) x)

 map₁₃-is-order-preserving : (b : B) → is-order-preserving ⁅ ⟦ b ⟧₁ ⁆ [ ⟦ b ⟧₃ ] (map₁₃ b)
 map₁₃-is-order-preserving (S b) (inl x) (inl y) l =
  inr (refl , (map₁₃-is-order-preserving b x y l))
 map₁₃-is-order-preserving (S b) (inl x) (inr y) ⋆ = inl ⋆
 map₁₃-is-order-preserving (L b) (i , x) (j , y) (inl l) =
  inl (ℕ-to-ℕ∞-order-preserving i j l)
 map₁₃-is-order-preserving (L b) (i , x) (.i , y) (inr (refl , m)) =
  inr (refl , (i , refl) , γ)
  where
   IH : map₁₃ (b i) x ≺⟪ ⟦ b i ⟧₃ ⟫ map₁₃ (b i) y
   IH = map₁₃-is-order-preserving (b i) x y m

   γ : transport⁻¹ (λ - → ⟪ ⟦ b - ⟧₃ ⟫) (ℕ-to-ℕ∞-lc refl) (map₁₃ (b i) x) ≺⟪ ⟦ b i ⟧₃ ⟫
       transport⁻¹ (λ - → ⟪ ⟦ b - ⟧₃ ⟫) (ℕ-to-ℕ∞-lc refl) (map₁₃ (b i) y)
   γ = transport⁻¹
        (λ r → transport⁻¹ (λ - → ⟪ ⟦ b - ⟧₃ ⟫) r (map₁₃ (b i) x) ≺⟪ ⟦ b i ⟧₃ ⟫
               transport⁻¹ (λ - → ⟪ ⟦ b - ⟧₃ ⟫) r (map₁₃ (b i) y))
        (ℕ-to-ℕ∞-lc-refl i)
        IH

 comparison₁₃ : EM 𝓤₁ → (b : B) → ⁅ ⟦ b ⟧₁ ⁆ ⊴ [ ⟦ b ⟧₃ ]
 comparison₁₃ em b = ≼-gives-⊴ _ _
                      (order-preserving-gives-≼ em _ _
                        (map₁₃ b , map₁₃-is-order-preserving b))
\end{code}

This completes the promised comparisons.

We also have:

\begin{code}

 map₃₂ : (b : B) → ⟪ ⟦ b ⟧₃ ⟫ → ⟨ ⟦ b ⟧₂ ⟩
 map₃₂ Z     x           = x
 map₃₂ (S b) (inl ⋆ , x) = inl (map₃₂ b x)
 map₃₂ (S b) (inr ⋆ , y) = inr ⋆
 map₃₂ (L b) (u , f)     = sum-to-sup
                            (extension (λ i → ⟦ b i ⟧₂))
                            (u , g)
  where
   g : ((i , _) : fiber ℕ-to-ℕ∞ u) → ⟨ ⟦ b i ⟧₂ ⟩
   g (i , p) = map₃₂ (b i) (f (i , p))

\end{code}

Question. Is the function map₃₂ a surjection?
