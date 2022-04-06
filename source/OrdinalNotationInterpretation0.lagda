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
open import UF-Quotient pt fe' pe

open import ConvergentSequenceCompact
open import CompactTypes
open import GenericConvergentSequence
open import OrdinalCodes
open import OrdinalsType
open import OrdinalArithmetic fe
open import OrdinalArithmetic-Properties ua
open import OrdinalOfOrdinalsSuprema pt ua
open import OrdinalOfOrdinals ua
open import OrdinalsType-Injectivity fe
open import Plus-Properties
open import PropTychonoff

open ImageAndSurjection pt
open ordinals-injectivity

module _ (ssq : Small-Set-Quotients 𝓤₀) where

 open suprema ssq

 private
  extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
  extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')

 brouwer-ordinal : B → Ordinal 𝓤₀
 brouwer-ordinal Z     = 𝟘ₒ
 brouwer-ordinal (S b) = brouwer-ordinal b +ₒ 𝟙ₒ
 brouwer-ordinal (L b) = sup (λ i → brouwer-ordinal (b i))

 brouwer-compact∙-ordinal : B → Ordinal 𝓤₀
 brouwer-compact∙-ordinal Z     = 𝟙ₒ
 brouwer-compact∙-ordinal (S b) = brouwer-compact∙-ordinal b +ₒ 𝟙ₒ
 brouwer-compact∙-ordinal (L b) = sup (extension (brouwer-compact∙-ordinal ∘ b))

 brouwer-compact∙-ordinal-is-compact∙ : (b : B) → compact∙ ⟨ brouwer-compact∙-ordinal b ⟩
 brouwer-compact∙-ordinal-is-compact∙ Z     = 𝟙-compact∙
 brouwer-compact∙-ordinal-is-compact∙ (S b) = +-compact∙
                                              (brouwer-compact∙-ordinal-is-compact∙ b)
                                              (𝟙-compact∙)
 brouwer-compact∙-ordinal-is-compact∙ (L b) =
   surjection-compact∙ pt
    (sum-to-sup (extension (brouwer-compact∙-ordinal ∘ b)))
    (sum-to-sup-is-surjection (extension (brouwer-compact∙-ordinal ∘ b)))
    (Σ-compact∙
      (ℕ∞-compact∙ fe')
      (λ u → prop-tychonoff fe
              (ℕ-to-ℕ∞-is-embedding fe' u)
              (λ (i , _) → brouwer-compact∙-ordinal-is-compact∙ (b i))))
\end{code}

More things to be added soon.
