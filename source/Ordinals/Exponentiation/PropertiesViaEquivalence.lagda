Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
December 2024

TODO: COMMENT

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.PropertiesViaEquivalence
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.List
open import MLTT.Spartan

open import UF.Base
open import UF.DiscreteAndSeparated

open import Ordinals.Arithmetic fe
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua
open import Ordinals.Exponentiation.Equivalence ua pt sr
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.TrichotomousLeastElement ua

open import DiscreteGraphicMonoids.ListsWithoutRepetitions fe'
             using (List-is-discrete)
open import TypeTopology.SigmaDiscreteAndTotallySeparated
             using (×-is-discrete)

\end{code}

The exponentiation constructions inherit decidability properties from α and β.

\begin{code}

expᴸ-preserves-discreteness : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                            → is-discrete ⟨ α ⟩
                            → is-discrete ⟨ β ⟩
                            → is-discrete ⟨ expᴸ α β ⟩
expᴸ-preserves-discreteness α β α-is-disc β-is-disc l@(xs , _) l'@(ys , _) =
 III II
  where
   I : is-discrete (⟨ α ⟩ × ⟨ β ⟩)
   I = ×-is-discrete α-is-disc β-is-disc

   II : is-decidable (xs ＝ ys)
   II = List-is-discrete ⦃ discrete-gives-discrete' I ⦄ xs ys

   III : is-decidable (xs ＝ ys) → is-decidable (l ＝ l')
   III (inl  eq) = inl (to-expᴸ-＝ α β eq)
   III (inr neq) = inr (λ p → neq (ap (expᴸ-list α β) p))

exponentiationᴸ-preserves-discreteness : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                         (h : has-trichotomous-least-element α)
                                       → is-discrete ⟨ α ⟩
                                       → is-discrete ⟨ β ⟩
                                       → is-discrete ⟨ exponentiationᴸ α h β ⟩
exponentiationᴸ-preserves-discreteness α β h@(⊥ , _) α-is-discrete β-is-discrete =
 expᴸ-preserves-discreteness (α ⁺[ h ]) β α⁺-is-discrete β-is-discrete
  where
   α⁺-is-discrete : is-discrete ⟨ α ⁺[ h ] ⟩
   α⁺-is-discrete = subtype-is-discrete
                     (Prop-valuedness α ⊥)
                     α-is-discrete

^ₒ-preserves-discreteness-for-basis-with-trichotomous-least-element
 : (α β : Ordinal 𝓤) (h : has-trichotomous-least-element α)
 → is-discrete ⟨ α ⟩
 → is-discrete ⟨ β ⟩
 → is-discrete ⟨ α ^ₒ β ⟩
^ₒ-preserves-discreteness-for-basis-with-trichotomous-least-element
 α β h α-disc β-disc =
  transport (λ - → is-discrete ⟨ - ⟩)
            (exponentiation-constructions-agree α β h)
            (exponentiationᴸ-preserves-discreteness α β h α-disc β-disc)

expᴸ-preserves-trichotomy : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                          → is-trichotomous α
                          → is-trichotomous β
                          → is-trichotomous (expᴸ α β)
expᴸ-preserves-trichotomy α β tri-α tri-β l@(xs , _) l'@(ys , _) =
 κ (tri xs ys)
 where
  tri : (xs ys : List ⟨  α ×ₒ β ⟩)
      → (xs ≺⟨List (α ×ₒ β) ⟩ ys) + (xs ＝ ys) + (ys ≺⟨List (α ×ₒ β) ⟩ xs)
  tri [] [] = inr (inl refl)
  tri [] (x ∷ ys) = inl []-lex
  tri (x ∷ xs) [] = inr (inr []-lex)
  tri ((a , b) ∷ xs) ((a' , b') ∷ ys) =
   ϕ (×ₒ-is-trichotomous α β tri-α tri-β (a , b) (a' , b')) (tri xs ys)
   where
    ϕ : in-trichotomy (underlying-order (α ×ₒ β)) (a , b) (a' , b')
      → in-trichotomy (λ l l' → l ≺⟨List (α ×ₒ β) ⟩ l') xs ys
      → in-trichotomy (λ l l' → l ≺⟨List (α ×ₒ β) ⟩ l')
                      ((a , b) ∷ xs)
                      ((a' , b') ∷ ys)
    ϕ (inl p)       _              = inl (head-lex p)
    ϕ (inr (inl r)) (inl ps)       = inl (tail-lex r ps)
    ϕ (inr (inl r)) (inr (inl rs)) = inr (inl (ap₂ _∷_ r rs))
    ϕ (inr (inl r)) (inr (inr qs)) = inr (inr (tail-lex (r ⁻¹) qs))
    ϕ (inr (inr q)) _              = inr (inr (head-lex q))

  κ : (xs ≺⟨List (α ×ₒ β) ⟩ ys) + (xs ＝ ys) + (ys ≺⟨List (α ×ₒ β) ⟩ xs)
    → (l ≺⟨ expᴸ α β ⟩ l') + (l ＝ l') + (l' ≺⟨ expᴸ α β ⟩ l)
  κ (inl p) = inl p
  κ (inr (inl e)) = inr (inl (to-expᴸ-＝ α β e))
  κ (inr (inr q)) = inr (inr q)

exponentiationᴸ-preserves-trichotomy : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                                       (h : has-trichotomous-least-element α)
                                     → is-trichotomous α
                                     → is-trichotomous β
                                     → is-trichotomous (exponentiationᴸ α h β)
exponentiationᴸ-preserves-trichotomy α β h tri-α tri-β =
 expᴸ-preserves-trichotomy (α ⁺[ h ]) β tri-α⁺ tri-β
  where
   tri-α⁺ : is-trichotomous (α ⁺[ h ])
   tri-α⁺ (x , p) (y , q) = κ (tri-α x y)
    where
     κ : in-trichotomy (underlying-order α) x y
       → in-trichotomy (underlying-order (α ⁺[ h ])) (x , p) (y , q)
     κ (inl l)       = inl l
     κ (inr (inl e)) = inr (inl (to-⁺-＝ α h e))
     κ (inr (inr k)) = inr (inr k)

^ₒ-preserves-trichotomy-for-basis-with-trichotomous-least-element
 : (α β : Ordinal 𝓤)
 → has-trichotomous-least-element α
 → is-trichotomous α
 → is-trichotomous β
 → is-trichotomous (α ^ₒ β)
^ₒ-preserves-trichotomy-for-basis-with-trichotomous-least-element
 α β h tri-α tri-β = transport is-trichotomous
                      (exponentiation-constructions-agree α β h)
                      (exponentiationᴸ-preserves-trichotomy α β h tri-α tri-β)

\end{code}

\begin{code}

module _
        (α : Ordinal 𝓤)
        (h : has-trichotomous-least-element α)
       where

 exponentiationᴸ-satisfies-zero-specification
  : exp-specification-zero α (exponentiationᴸ α h)
 exponentiationᴸ-satisfies-zero-specification =
  transport⁻¹ (exp-specification-zero α)
              (dfunext fe' (λ β → exponentiation-constructions-agree α β h))
              (^ₒ-satisfies-zero-specification α)

 exponentiationᴸ-satisfies-succ-specification
  : exp-specification-succ α (exponentiationᴸ α h)
 exponentiationᴸ-satisfies-succ-specification =
  transport⁻¹ (exp-specification-succ α)
              (dfunext fe' (λ β → exponentiation-constructions-agree α β h))
              (^ₒ-satisfies-succ-specification α
                (trichotomous-least-element-gives-𝟙ₒ-⊴ α h))

 exponentiationᴸ-satisfies-sup-specification
  : exp-specification-sup α (exponentiationᴸ α h)
 exponentiationᴸ-satisfies-sup-specification =
  transport⁻¹ (exp-specification-sup α)
              (dfunext fe' (λ β → exponentiation-constructions-agree α β h))
              (^ₒ-satisfies-sup-specification α)

\end{code}

\begin{code}

 exponentiationᴸ-monotone-in-exponent :
  (β γ : Ordinal 𝓤) → β ⊴ γ → exponentiationᴸ α h β ⊴ exponentiationᴸ α h γ
 exponentiationᴸ-monotone-in-exponent β γ l =
  transport₂ _⊴_
   ((exponentiation-constructions-agree α β h) ⁻¹)
   ((exponentiation-constructions-agree α γ h) ⁻¹)
   (^ₒ-monotone-in-exponent α β γ l)

 𝟙ₒ-neutral-exponentiationᴸ : exponentiationᴸ α h 𝟙ₒ ＝ α
 𝟙ₒ-neutral-exponentiationᴸ =
  transport⁻¹
   (_＝ α)
   (exponentiation-constructions-agree α 𝟙ₒ h)
   (𝟙ₒ-neutral-^ₒ α (trichotomous-least-element-gives-𝟙ₒ-⊴ α h))

 exponentiationᴸ-by-𝟚ₒ-is-×ₒ : exponentiationᴸ α h 𝟚ₒ ＝ α ×ₒ α
 exponentiationᴸ-by-𝟚ₒ-is-×ₒ =
  transport⁻¹
   (_＝ α ×ₒ α)
   (exponentiation-constructions-agree α 𝟚ₒ h)
   (^ₒ-𝟚ₒ-is-×ₒ α (trichotomous-least-element-gives-𝟙ₒ-⊴ α h))

 exponentiationᴸ-by-+ₒ
  : (β γ : Ordinal 𝓤)
  → exponentiationᴸ α h (β +ₒ γ)
    ＝ exponentiationᴸ α h β ×ₒ exponentiationᴸ α h γ
 exponentiationᴸ-by-+ₒ β γ =
  transport₂
   _＝_
    (exponentiation-constructions-agree α (β +ₒ γ) h ⁻¹)
    (ap₂ _×ₒ_
         ((exponentiation-constructions-agree α β h) ⁻¹)
         ((exponentiation-constructions-agree α γ h) ⁻¹))
    (^ₒ-by-+ₒ α β γ)

 module _
         (β γ : Ordinal 𝓤)
        where

  private
   h' : has-trichotomous-least-element (exponentiationᴸ α h β)
   h' = exponentiationᴸ-has-trichotomous-least-element α h β

  exponentiationᴸ-by-×ₒ
   : exponentiationᴸ α h (β ×ₒ γ)
     ＝ exponentiationᴸ (exponentiationᴸ α h β) h' γ
  exponentiationᴸ-by-×ₒ =
   transport₂
    _＝_
     (exponentiation-constructions-agree α (β ×ₒ γ) h ⁻¹)
     ((exponentiation-constructions-agree (exponentiationᴸ α h β) γ h'
        ∙ ap (_^ₒ γ) (exponentiation-constructions-agree α β h)) ⁻¹)
     (^ₒ-by-×ₒ α β γ)

 exponentiationᴸ-order-preserving-in-exponent
  : (β γ : Ordinal 𝓤)
  → 𝟙ₒ ⊲ α
  → β ⊲ γ → exponentiationᴸ α h β ⊲ exponentiationᴸ α h γ
 exponentiationᴸ-order-preserving-in-exponent β γ l k =
  transport₂
   _⊲_
   (exponentiation-constructions-agree α β h ⁻¹)
   (exponentiation-constructions-agree α γ h ⁻¹)
   (^ₒ-order-preserving-in-exponent α β γ l k)

\end{code}