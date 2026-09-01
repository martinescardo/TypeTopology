Martin Escardo, 1st September 2026.

The order notion of limit point, for contrast with the
topological notion of TypeTopology.LimitPoints. The two notions do not
agree, as the simple example below shows.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Ordinals.LimitPoints
        (fe : FunExt)
       where

open import CoNaturals.Type
open import Notation.CanonicalMap
open import Notation.Order
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import TypeTopology.LimitPoints
open import TypeTopology.SigmaDiscrete
open import UF.DiscreteAndSeparated

\end{code}

A point y of an ordinal α is the successor of x when x is below y and
nothing below y goes beyond x. An order limit point is a
point that is neither least nor a successor.

\begin{code}

is-successor-of : (α : Ordinal 𝓤) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
is-successor-of α x y = (y ≺⟨ α ⟩ x)
                      × ((z : ⟨ α ⟩) → z ≺⟨ α ⟩ x → z ≼⟨ α ⟩ y)

is-order-limit-point : (α : Ordinal 𝓤) → ⟨ α ⟩ → 𝓤 ̇
is-order-limit-point α x = ¬ is-least α x
                         × ¬ (Σ y ꞉ ⟨ α ⟩ , is-successor-of α x y)

\end{code}

The point (∞ , ι 1) of the compact ordinal ℕ∞ᵒ ×ᵒ ℕ∞ᵒ is a
topological limit point but not an order one.

\begin{code}

example-of-topological-limit-point-which-is-not-order-limit
 : Σ α ꞉ Ordinal 𝓤₀ ,
   Σ x ꞉ ⟨ α ⟩ , is-limit-point x
               × ¬ is-order-limit-point α x
example-of-topological-limit-point-which-is-not-order-limit
 = α , x , I , III
 where
  α : Ordinal 𝓤₀
  α = [ ℕ∞ᵒ ×ᵒ ℕ∞ᵒ ]

  x y : ⟨ α ⟩
  x = (∞ , ι 1)
  y = (∞ , ι 0)

  I : is-limit-point x
  I i = is-isolated-gives-is-isolated' ∞ (×-isolated-left i)

  II : is-successor-of α x y
  II = II₀ , II₁
   where
    II₀ : y ≺⟨ [ ℕ∞ᵒ ×ᵒ ℕ∞ᵒ ] ⟩ x
    II₀  = inr (refl , ℕ-to-ℕ∞-≺-diagonal 0)

    II₁ : (w : ⟨ ℕ∞ᵒ ×ᵒ ℕ∞ᵒ ⟩)
       → w ≺⟨ [ ℕ∞ᵒ ×ᵒ ℕ∞ᵒ ] ⟩ x
       → w ≼⟨ [ ℕ∞ᵒ ×ᵒ ℕ∞ᵒ ] ⟩ y
    II₁ (c , d) (inl l)          (a , b) (inl m)
     = inl (≺-trans a c ∞ m l)
    II₁ (c , d) (inl l)          (a , b) (inr (refl , _))
     = inl l
    II₁ (c , d) (inr (refl , l)) (a , b) (inl m)
     = inl m
    II₁ (c , d) (inr (refl , l)) (a , b) (inr (refl , n)) =
     𝟘-elim
      (nothing-is-below-0 b
        (transport (b ≺_) (anything-below-1-is-0 d l) n))

  III : ¬ is-order-limit-point α x
  III (nl , ns) = ns (y , II)

\end{code}
