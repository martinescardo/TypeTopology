Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
December 2024

TODO: Implement properties via Exponentiation.Equivalence

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.DecreasingListProperties
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
open import Ordinals.Type
open import Ordinals.Underlying

open import Ordinals.Exponentiation.DecreasingList ua

open import DiscreteGraphicMonoids.ListsWithoutRepetitions fe'
             using (List-is-discrete)
open import TypeTopology.SigmaDiscreteAndTotallySeparated
             using (×-is-discrete)

\end{code}

The type expᴸ α β inherits decidability properties from α and β.

\begin{code}

expᴸ-preserves-discreteness : (α : Ordinal 𝓤) (β : Ordinal 𝓥)
                            → is-discrete ⟨ α ⟩
                            → is-discrete ⟨ β ⟩
                            → is-discrete ⟨ expᴸ α β ⟩
expᴸ-preserves-discreteness α β dec-α dec-β l@(xs , _) l'@(ys , _) = III II
 where
  I : is-discrete (⟨ α ⟩ × ⟨ β ⟩)
  I = ×-is-discrete dec-α dec-β

  II : is-decidable (xs ＝ ys)
  II = List-is-discrete ⦃ discrete-gives-discrete' I ⦄ xs ys

  III : is-decidable (xs ＝ ys) → is-decidable (l ＝ l')
  III (inl  eq) = inl (to-expᴸ-＝ α β eq)
  III (inr neq) = inr (λ p → neq (ap (expᴸ-list α β) p))

expᴸ-preserves-trichotomy : (α : Ordinal 𝓤)(β : Ordinal 𝓥)
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

\end{code}