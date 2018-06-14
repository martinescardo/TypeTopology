Martin Escardo, 20-21 December 2012.

If X and Y come with orders, both denoted by ≤, then the lexicographic
order on X × Y is defined by

  (x , y) ≤ (x' , y') ⇔ x ≤ x' ∧ (x ≡ x' → y ≤ y').

More generally, we can consider the lexicographic product of two
binary relations R on X and S on Y, which is a relation on X × Y, or
even on (Σ \(x : X) → Y x) if Y and S depend on X.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LexicographicOrder where

open import SpartanMLTT hiding (_≤_)

bin-rel : ∀ {U} → U ̇ → U ′ ̇
bin-rel {U} X = X → X → U ̇

lex-prod : ∀ {U V} {X : U ̇} {Y : X → V ̇} →  bin-rel X → ({x : X} → bin-rel(Y x)) → bin-rel(Σ Y)
lex-prod _≤_ _≼_ (x , y) (x' , y') = (x ≤ x') × ((r : x ≡ x') → transport _ r y ≼ y')

\end{code}

Added 14th June 2018:

However, for a strict order, it makes sense to define

  (x , y) < (x' , y') ⇔ x < x' ∨ (x ≡ x' ∧ y < y').

\begin{code}

slex-prod : ∀ {U V} {X : U ̇} {Y : X → V ̇} →  bin-rel X → ({x : X} → bin-rel(Y x)) → bin-rel(Σ Y)
slex-prod _<_ _≺_ (x , y) (x' , y') = (x < x') + Σ \(r : x ≡ x') → transport _ r y ≺ y'

\end{code}


Usually in such a context, a ≤ b is defined to be ¬(b < a).

The negation of the above is, then,

   ¬(x ≤ x') ∧ ¬(x ≡ x' ∧ y < y') by de Morgan
⇔ x ≤ x' ∧ ¬(x ≡ x' ∧ y < y') by definition of ≤
⇔ x' ≤ x ∧ ((x ≡ x' → ¬(y < y')) by (un)currying
⇔ x' ≤ x ∧ ((x ≡ x' → y' ≤ y) by definition of ≤

What this means is that the non-strict lexigraphic product of the
induced non-strict order is induced by the strict lexicographic
product of the strict orders. This works a little more generally as
follows.

\begin{code}

module correcteness (U V : Universe)
         (X : U ̇)
         (Y : X → V ̇)
         (_<_ : X → X → U ̇)
         (_≺_ : {x : X} → Y x → Y x → V ̇)
         (R : U₀ ̇)
 where
  not : ∀ {U} → U ̇ → U ̇
  not A = A → R
  _⊏_ : Σ Y → Σ Y → U ⊔ V ̇
  _⊏_ = slex-prod _<_ _≺_
  _≤_ : X → X → U ̇
  x ≤ x' = not(x' < x)
  _≼_ : {x : X} → Y x → Y x → V ̇
  y ≼ y' = not(y' ≺ y)
  _⊑_ : Σ Y → Σ Y → U ⊔ V ̇
  _⊑_ = lex-prod _≤_ _≼_
  forth : (x x' : X) (y : Y x) (y' : Y x') → not((x , y) ⊏ (x' , y')) → (x' , y') ⊑ (x , y) 
  forth x x' y y' f = g , h
   where
    g : not(x < x')
    g l = f (inl l)
    h : (r : x' ≡ x) → not(y ≺ transport Y r y')
    h refl l = f (inr (refl , l))
  back : (x x' : X) (y : Y x) (y' : Y x') → (x' , y') ⊑ (x , y) → not((x , y) ⊏ (x' , y'))
  back x x' y y' (f , g) (inl l) = f l
  back x _  y y' (f , g) (inr (refl , l)) = g refl l

\end{code}

TODO. Generalize the universe levels in various places.
