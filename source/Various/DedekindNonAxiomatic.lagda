Tom de Jong, 9 January 2026.

The purpose of this module is to re-export the constructions of Various.Dedekind
but without any assumptions on ℚ and its strict order by fulfilling them using
Andrew Sneap's development of rational numbers.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Various.DedekindNonAxiomatic
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
       where

 open PropositionalTruncation pt

 open import MLTT.Spartan
 open import Notation.Order using (_<_ ; _≮_)
 open import Rationals.Order
 open import Rationals.Type

 open import Various.Dedekind pt fe pe
              ℚ _<ℚ_ ℚ<-is-prop ℚ<-irrefl
             public

 ℚ-order-criterion : (p q : ℚ) → q ≮ p → p ≠ q → p < q
 ℚ-order-criterion p q h₁ h₂ = κ (ℚ-trichotomous p q)
  where
   κ : (p < q) + (p ＝ q) + (q < p) → p < q
   κ (inl l) = l
   κ (inr (inl e)) = 𝟘-elim (h₂ e)
   κ (inr (inr l)) = 𝟘-elim (h₁ l)

 ℚ-tightness : (p q : ℚ) → q ≮ p → p ≮ q → p ＝ q
 ℚ-tightness p q h₁ h₂ = κ (ℚ-trichotomous p q)
  where
   κ : (p < q) + (p ＝ q) + (q < p) → p ＝ q
   κ (inl l) = 𝟘-elim (h₂ l)
   κ (inr (inl e)) = e
   κ (inr (inr l)) = 𝟘-elim (h₁ l)

 open ℚ-assumptions
       ℚ-dense
       ℚ<-trans
       ℚ-order-criterion
       (λ p q r l → ∣ located-property p r q l ∣)
       ℚ-tightness
       (λ q → ∣ ℚ-no-least-element q ∣)
       (λ p → ∣ ℚ-no-max-element p ∣)
       0ℚ
       1/2
       1ℚ
       0<1/2
       1/2<1
      public

\end{code}
