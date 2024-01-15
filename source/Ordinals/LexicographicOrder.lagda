Martin Escardo, 20-21 December 2012.

If X and Y come with orders, both denoted by ≤, then the lexicographic
order on X × Y is defined by

  (x , y) ≤ (x' , y') ↔ x ≤ x' ∧ (x ＝ x' → y ≤ y').

More generally, we can consider the lexicographic product of two
binary relations R on X and S on Y, which is a relation on X × Y, or
even on (Σ x ꞉ X , Y x) if Y and S depend on X.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.LexicographicOrder where

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons

lex-order : ∀ {𝓣} {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
          →  (X → X → 𝓦 ̇ )
          → ({x : X} → Y x → Y x → 𝓣 ̇ )
          → (Σ Y → Σ Y → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ )
lex-order _≤_ _≼_ (x , y) (x' , y') = (x ≤ x') × ((r : x ＝ x') → transport _ r y ≼ y')

\end{code}

Added 14th June 2018, from 2013 in another development.

However, for a strict order, it makes sense to define

  (x , y) < (x' , y') ↔ x < x' ∨ (x ＝ x' ∧ y < y').

\begin{code}

slex-order : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
           →  (X → X → 𝓦 ̇ )
           → ({x : X} → Y x → Y x → 𝓣 ̇ )
           → (Σ Y → Σ Y → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ )
slex-order _<_ _≺_ (x , y) (x' , y') = (x < x') + (Σ r ꞉ x ＝ x' , transport _ r y ≺ y')

\end{code}

Usually in such a context, a ≤ b is defined to be ¬ (b < a).

The negation of the strict lexicographic product is, then,

 ¬ (x < x') ∧ ¬ (x ＝ x' ∧ y < y') by de Morgan,
↔ x ≤ x' ∧ ¬ (x ＝ x' ∧ y < y')    by definition of ≤,
↔ x' ≤ x ∧ ((x ＝ x' → ¬ (y < y')) by (un)currying,
↔ x' ≤ x ∧ ((x ＝ x' → y' ≤ y)     by definition of ≤.

What this means is that the non-strict lexigraphic product of the
induced non-strict order is induced by the strict lexicographic
product of the strict orders. This works a little more generally as
follows.

\begin{code}

module lexicographic-commutation
         {X : 𝓤 ̇ }
         {Y : X → 𝓥 ̇ }
         (_<_ : X → X → 𝓦 ̇ )
         (_≺_ : {x : X} → Y x → Y x → 𝓣 ̇ )
         (R : 𝓣 ̇ )
 where
  not : ∀ {𝓤} → 𝓤 ̇ → 𝓣 ⊔ 𝓤 ̇
  not A = A → R

  _⊏_ : Σ Y → Σ Y → 𝓣 ⊔ 𝓤 ⊔ 𝓦 ̇
  _⊏_ = slex-order _<_ _≺_

  _≤_ : X → X → 𝓦 ⊔ 𝓣 ̇
  x ≤ x' = not (x' < x)

  _≼_ : {x : X} → Y x → Y x → 𝓣 ̇
  y ≼ y' = not (y' ≺ y)

  _⊑_ : Σ Y → Σ Y → 𝓣 ⊔ 𝓤 ⊔ 𝓦 ̇
  _⊑_ = lex-order _≤_ _≼_

  forth : (x x' : X) (y : Y x) (y' : Y x') → not ((x , y) ⊏ (x' , y')) → (x' , y') ⊑ (x , y)
  forth x x' y y' f = g , h
   where
    g : not (x < x')
    g l = f (inl l)
    h : (r : x' ＝ x) → not (y ≺ transport Y r y')
    h refl l = f (inr (refl , l))

  back : (x x' : X) (y : Y x) (y' : Y x') → (x' , y') ⊑ (x , y) → not ((x , y) ⊏ (x' , y'))
  back x x' y y' (g , h) (inl l) = g l
  back x _  y y' (g , h) (inr (refl , l)) = h refl l

\end{code}
