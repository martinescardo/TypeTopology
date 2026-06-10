Martin Escardo, 4th April 2022

See the 2018 file OrdinalNotationInterpretation1 for discussion.

We interpret Brouwer ordinal codes as ordinals in four ways and relate
them.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc

module Ordinals.NotationInterpretation0
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open PropositionalTruncation pt

open import CoNaturals.Type
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Brouwer
open import Ordinals.Injectivity
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.ToppedAdditionProperties ua
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.TrichotomousArithmetic fe
open import Ordinals.TrichotomousType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import TypeTopology.CompactTypes
open import TypeTopology.SquashedSum fe
open import TypeTopology.TotallySeparated
open import UF.DiscreteAndSeparated
open import UF.Size

open ordinals-injectivity fe

module _ (sr : Set-Replacement pt) where

 open suprema pt sr

 private
  extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
  extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')

\end{code}

We now define our four interpretations of Brouwer ordinal trees as
ordinals.

The first interpretation is the intended one.

\begin{code}

 ⟦_⟧₀ : B → Ordinal 𝓤₀
 ⟦ Z ⟧₀   = 𝟘ₒ
 ⟦ S b ⟧₀ = ⟦ b ⟧₀ +ₒ 𝟙ₒ
 ⟦ L b ⟧₀ = sup (λ i → ⟦ b i ⟧₀)

\end{code}

The second interpretation is into topped ordinals. It enlarges, in
some sense, the first interpretation, so that we get bigger, and,
importantly for our purposes, compact ordinals.

\begin{code}

 ⟦_⟧₁ : B → Ordinalᵀ 𝓤₀
 ⟦ Z ⟧₁   = 𝟙ᵒ
 ⟦ S b ⟧₁ = ⟦ b ⟧₁ +ᵒ 𝟙ᵒ
 ⟦ L b ⟧₁ = ∑¹ (λ i → ⟦ b i ⟧₁)

\end{code}

The third interpretation enlarges the first one in a different way.

\begin{code}

 ⟦_⟧₂ : B → Ordinal 𝓤₀
 ⟦ Z ⟧₂   = 𝟙ₒ
 ⟦ S b ⟧₂ = ⟦ b ⟧₂ +ₒ 𝟙ₒ
 ⟦ L b ⟧₂ = sup (extension (λ i → ⟦ b i ⟧₂))

\end{code}

And the fourth and last interpretation is into trichomotomous
ordinals, where Ordinal₃ 𝓤 is the type of trichotomous ordinals in the
universe 𝓤. We again take sums rather than sups.

\begin{code}

 ⟦_⟧₃ : B → Ordinal₃ 𝓤₀
 ⟦ Z ⟧₃    = 𝟘₃
 ⟦ S b ⟧₃  = ⟦ b ⟧₃ +₃ 𝟙₃
 ⟦ L b ⟧₃  = ∑³ ω₃ (λ i → ⟦ b i ⟧₃)

\end{code}

We'll prove the following inequalities, where the arrows represent the
relation _⊴_ on ordinals, under the assumption of excluded middle:

 ⟦ b ⟧₀ → ⟦ b ⟧₃
   ↓       ↓
 ⟦ b ⟧₂ → ⟦ b ⟧₁

But we first show that ⟦ b ⟧₂ and ⟦ b ⟧₁ are compact and pointed. The
pointedness is absolutely essential in the proofs by induction, via
the indirect use of micro-tychonoff in Σ¹, because a version of
micro-tychonoff without pointedness implies excluded middle. And this
is why we defined the base cases to be 𝟙 rather than 𝟘.

\begin{code}

 ⟦_⟧₁-is-compact∙ : (b : B) → is-compact∙ ⟨ ⟦ b ⟧₁ ⟩
 ⟦ Z ⟧₁-is-compact∙   = 𝟙-is-compact∙
 ⟦ S b ⟧₁-is-compact∙ = Σ-is-compact∙ 𝟙+𝟙-is-compact∙
                         (dep-cases
                           (λ _ → ⟦ b ⟧₁-is-compact∙)
                           (λ _ → 𝟙-is-compact∙))
 ⟦ L b ⟧₁-is-compact∙ = Σ¹-compact∙
                          (λ i → ⟨ ⟦ b i ⟧₁ ⟩)
                          (λ i → ⟦ b i ⟧₁-is-compact∙)

 ⟦_⟧₁-is-totally-separated : (b : B) → is-totally-separated ⟨ ⟦ b ⟧₁ ⟩
 ⟦ Z ⟧₁-is-totally-separated = 𝟙-is-totally-separated
 ⟦ S b ⟧₁-is-totally-separated = Σ-is-totally-separated-if-index-type-is-discrete
                                  (𝟙 + 𝟙)
                                  (λ x → ⟨ cases (λ _ → ⟦ b ⟧₁) (λ _ → 𝟙ᵒ) x ⟩)
                                  (+-is-discrete 𝟙-is-discrete 𝟙-is-discrete)
                                  (λ {(inl ⋆) → ⟦ b ⟧₁-is-totally-separated ;
                                      (inr ⋆) → 𝟙-is-totally-separated})
 ⟦ L b ⟧₁-is-totally-separated = Σ¹-is-totally-separated
                                  (λ i → ⟨ ⟦ b i ⟧₁ ⟩)
                                  (λ i → ⟦ b i ⟧₁-is-totally-separated)

 ⟦_⟧₂-is-compact∙ : (b : B) → is-compact∙ ⟨ ⟦ b ⟧₂ ⟩
 ⟦ Z ⟧₂-is-compact∙   = 𝟙-is-compact∙
 ⟦ S b ⟧₂-is-compact∙ = +-is-compact∙ ⟦ b ⟧₂-is-compact∙ (𝟙-is-compact∙)
 ⟦ L b ⟧₂-is-compact∙ = codomain-of-surjection-is-compact∙ pt
                         (sum-to-sup (extension (λ i → ⟦ b i ⟧₂)))
                         (sum-to-sup-is-surjection (extension (λ i → ⟦ b i ⟧₂)))
                         (Σ¹-compact∙
                            (λ i → ⟨ ⟦ b i ⟧₂ ⟩)
                            (λ i → ⟦ b i ⟧₂-is-compact∙ ))

\end{code}

TODO. I don't think ⟦ b ⟧₂ is totally separated without assuming classical logic.

The successor function on ordinals is not necessarily monotone, but it
is if excluded middle holds.

\begin{code}

 open import UF.ClassicalLogic
 open import Ordinals.SupSum ua

 comparison₀₃ : Excluded-Middle → (b : B) → ⟦ b ⟧₀ ⊴ [ ⟦ b ⟧₃ ]
 comparison₀₃ em Z     = ⊴-refl 𝟘ₒ
 comparison₀₃ em (S b) = succ-monotone em ⟦ b ⟧₀ [ ⟦ b ⟧₃ ] (comparison₀₃ em b)
 comparison₀₃ em (L b) = IV
  where
   I : (i : ℕ) → ⟦ b i ⟧₀ ⊴ [ ⟦ b i ⟧₃ ]
   I i = comparison₀₃ em (b i)

   II : sup (λ i → ⟦ b i ⟧₀) ⊴ sup (λ i → [ ⟦ b i ⟧₃ ])
   II = sup-monotone (λ i → ⟦ b i ⟧₀) (λ i → [ ⟦ b i ⟧₃ ]) I

   III : sup (λ i → [ ⟦ b i ⟧₃ ])  ⊴ [ ∑³ ω₃ (λ i → ⟦ b i ⟧₃) ]
   III = sup-bounded-by-sum₃ em pt sr _ _

   IV : sup (λ i → ⟦ b i ⟧₀) ⊴ [ ∑³ ω₃ (λ i → ⟦ b i ⟧₃) ]
   IV = ⊴-trans _ _ _ II III

 comparison₀₂ : EM 𝓤₁ → (b : B) → ⟦ b ⟧₀ ⊴ ⟦ b ⟧₂
 comparison₀₂ em Z     = 𝟘ₒ-least-⊴ 𝟙ₒ
 comparison₀₂ em (S b) = succ-monotone em ⟦ b ⟧₀ ⟦ b ⟧₂ (comparison₀₂ em b)
 comparison₀₂ em (L b) = VI
  where
   I : (n : ℕ) → ⟦ b n ⟧₀ ⊴ ⟦ b n ⟧₂
   I n = comparison₀₂ em (b n)

   II : (n : ℕ) → extension (λ i → ⟦ b i ⟧₂) (ℕ-to-ℕ∞ n) ＝ ⟦ b n ⟧₂
   II n = ↗-property (ua 𝓤₀) (λ i → ⟦ b i ⟧₂) (embedding-ℕ-to-ℕ∞ fe') n

   III : (n : ℕ) → ⟦ b n ⟧₀ ⊴ extension (λ i → ⟦ b i ⟧₂) (ℕ-to-ℕ∞ n)
   III n = transport (⟦_⟧₀ (b n) ⊴_) ((II n)⁻¹) (I n)

   IV : sup (λ i → ⟦ b i ⟧₀) ⊴ sup (extension (λ i → ⟦ b i ⟧₂) ∘ ℕ-to-ℕ∞)
   IV = sup-monotone _ _ III

   V : sup (extension (λ i → ⟦ b i ⟧₂) ∘ ℕ-to-ℕ∞)
     ⊴ sup (extension (λ i → ⟦ b i ⟧₂))
   V = sup-is-lower-bound-of-upper-bounds _ _
        (λ n → sup-is-upper-bound _ (ℕ-to-ℕ∞ n))

   VI : sup (λ i → ⟦ b i ⟧₀) ⊴ sup (extension (λ i → ⟦ b i ⟧₂))
   VI = ⊴-trans _ _ _ IV V

 comparison₂₁ : Excluded-Middle → (b : B) → ⟦ b ⟧₂ ⊴ [ ⟦ b ⟧₁ ]
 comparison₂₁ em Z     = ⊴-refl 𝟙ₒ
 comparison₂₁ em (S b) = III
  where
   I : (⟦ b ⟧₂ +ₒ 𝟙ₒ) ⊴ ([ ⟦ b ⟧₁ ] +ₒ 𝟙ₒ)
   I = succ-monotone em (⟦ b ⟧₂) [ ⟦ b ⟧₁ ] (comparison₂₁ em b)

   II : [ ⟦ b ⟧₁ +ᵒ 𝟙ᵒ ] ＝ ([ ⟦ b ⟧₁ ] +ₒ 𝟙ₒ)
   II = alternative-plus (⟦ b ⟧₁) 𝟙ᵒ

   III : (⟦ b ⟧₂ +ₒ 𝟙ₒ) ⊴ [ ⟦ b ⟧₁ +ᵒ 𝟙ᵒ ]
   III = transport⁻¹ ((⟦ b ⟧₂ +ₒ 𝟙ₒ) ⊴_) II I

 comparison₂₁ em (L b) = V
  where
   α : ℕ∞ → Ordinal 𝓤₀
   α = extension (λ i → ⟦ b i ⟧₂)

   β : ℕ∞ → Ordinal 𝓤₀
   β = extension (λ i → [ ⟦ b i ⟧₁ ])

   τ : ℕ∞ → Ordinalᵀ 𝓤₀
   τ = topped-ordinals-injectivity._↗_ fe
        (λ i → ⟦ b i ⟧₁)
        (embedding-ℕ-to-ℕ∞ fe')

   I : (i : ℕ) →  ⟦ b i ⟧₂ ⊴ [ ⟦ b i ⟧₁ ]
   I i = comparison₂₁ em (b i)

   II : (u : ℕ∞) → α u ⊴ β u
   II = ordinals-injectivity-order.↗-preserves-⊴ ua (embedding-ℕ-to-ℕ∞ fe') _ _ I

   III : sup α ⊴ sup β
   III = sup-monotone α β II

   IV : sup β ⊴ [ ∑ ℕ∞ᵒ τ ]
   IV = sup-bounded-by-sumᵀ em pt sr ℕ∞ᵒ τ

   V : sup α ⊴ [ ∑ ℕ∞ᵒ τ ]
   V = ⊴-trans _ _ _ III IV

 map₃₁ : (b : B) → ⟨ ⟦ b ⟧₃ ⟩ → ⟨ ⟦ b ⟧₁ ⟩
 map₃₁ Z     x = unique-from-𝟘 x
 map₃₁ (S b) (inl x) = inl ⋆ , map₃₁ b x
 map₃₁ (S b) (inr x) = inr ⋆ , ⋆
 map₃₁ (L b) (i , x) = ℕ-to-ℕ∞ i , f
  where
   f : ((j , p) : fiber ℕ-to-ℕ∞ (ℕ-to-ℕ∞ i)) → ⟨ ⟦ b j ⟧₁ ⟩
   f (j , p) = transport⁻¹ (λ - → ⟨ ⟦ b - ⟧₁ ⟩) (ℕ-to-ℕ∞-lc p) (map₃₁ (b i) x)

 map₃₁-is-order-preserving : (b : B)
                           → is-order-preserving [ ⟦ b ⟧₃ ] [ ⟦ b ⟧₁ ] (map₃₁ b)
 map₃₁-is-order-preserving (S b) (inl x) (inl y) l =
  inr (refl , (map₃₁-is-order-preserving b x y l))
 map₃₁-is-order-preserving (S b) (inl x) (inr y) ⋆ = inl ⋆
 map₃₁-is-order-preserving (L b) (i , x) (j , y) (inl l) =
  inl (ℕ-to-ℕ∞-order-preserving i j l)
 map₃₁-is-order-preserving (L b) (i , x) (.i , y) (inr (refl , m)) =
  inr (refl , (i , refl) , γ)
  where
   IH : map₃₁ (b i) x ≺⟨ ⟦ b i ⟧₁ ⟩ map₃₁ (b i) y
   IH = map₃₁-is-order-preserving (b i) x y m

   γ : transport⁻¹ (λ - → ⟨ ⟦ b - ⟧₁ ⟩) (ℕ-to-ℕ∞-lc refl) (map₃₁ (b i) x)
     ≺⟨ ⟦ b i ⟧₁ ⟩
       transport⁻¹ (λ - → ⟨ ⟦ b - ⟧₁ ⟩) (ℕ-to-ℕ∞-lc refl) (map₃₁ (b i) y)
   γ = transport⁻¹
        (λ r → transport⁻¹ (λ - → ⟨ ⟦ b - ⟧₁ ⟩) r (map₃₁ (b i) x) ≺⟨ ⟦ b i ⟧₁ ⟩
               transport⁻¹ (λ - → ⟨ ⟦ b - ⟧₁ ⟩) r (map₃₁ (b i) y))
        (ℕ-to-ℕ∞-lc-refl i)
        IH

 comparison₃₁ : EM 𝓤₀ → (b : B) → [ ⟦ b ⟧₃ ] ⊴ [ ⟦ b ⟧₁ ]
 comparison₃₁ em b = ≼-gives-⊴ _ _
                      (EM-implies-order-preserving-gives-≼ em _ _
                        (map₃₁ b , map₃₁-is-order-preserving b))
\end{code}

This completes the promised comparisons.

We also have:

\begin{code}

 map₁₂ : (b : B) → ⟨ ⟦ b ⟧₁ ⟩ → ⟨ ⟦ b ⟧₂ ⟩
 map₁₂ Z     x           = x
 map₁₂ (S b) (inl ⋆ , x) = inl (map₁₂ b x)
 map₁₂ (S b) (inr ⋆ , y) = inr ⋆
 map₁₂ (L b) (u , f)     = sum-to-sup
                            (extension (λ i → ⟦ b i ⟧₂))
                            (u , g)
  where
   g : ((i , _) : fiber ℕ-to-ℕ∞ u) → ⟨ ⟦ b i ⟧₂ ⟩
   g (i , p) = map₁₂ (b i) (f (i , p))

\end{code}

TODO. Is the function map₁₂ a surjection?
