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
open import UF-Base hiding (_≤_)

bin-rel : ∀ {U} → U ̇ → U ′ ̇
bin-rel {U} X = X → X → U ̇

lex-prod : ∀ {U V} {X : U ̇} {Y : X → V ̇} →  bin-rel X → ({x : X} → bin-rel(Y x)) → bin-rel(Σ Y)
lex-prod _≤_ _≼_ (x , y) (x' , y') = (x ≤ x') × ((r : x ≡ x') → transport _ r y ≼ y')

\end{code}

Added 14th June 2018, from 2013 in another development.

However, for a strict order, it makes sense to define

  (x , y) < (x' , y') ⇔ x < x' ∨ (x ≡ x' ∧ y < y').

\begin{code}

slex-prod : ∀ {U V} {X : U ̇} {Y : X → V ̇} →  bin-rel X → ({x : X} → bin-rel(Y x)) → bin-rel(Σ Y)
slex-prod _<_ _≺_ (x , y) (x' , y') = (x < x') + Σ \(r : x ≡ x') → transport _ r y ≺ y'

\end{code}


Usually in such a context, a ≤ b is defined to be ¬(b < a).

The negation of the strict lexicographic product is, then,

 ¬(x < x') ∧ ¬(x ≡ x' ∧ y < y') by de Morgan
⇔ x ≤ x' ∧ ¬(x ≡ x' ∧ y < y') by definition of ≤
⇔ x' ≤ x ∧ ((x ≡ x' → ¬(y < y')) by (un)currying
⇔ x' ≤ x ∧ ((x ≡ x' → y' ≤ y) by definition of ≤

What this means is that the non-strict lexigraphic product of the
induced non-strict order is induced by the strict lexicographic
product of the strict orders. This works a little more generally as
follows.

\begin{code}

module commutation (U V : Universe)
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
  back x x' y y' (g , h) (inl l) = g l
  back x _  y y' (g , h) (inr (refl , l)) = h refl l

\end{code}

TODO. Generalize the universe levels in various places.

Done sometime in 2013 in another developement, imported 18th June
2018.

\begin{code}

open import Ordinals

lex-prod-Well : ∀ {U V} {X : U ̇} {Y : X → V ̇}
             → (_<_ : bin-rel X)
             → (_<'_ : {x : X} → bin-rel(Y x)) 
             → Well-founded _<_
             → ({x : X} → Well-founded(_<'_ {x}))
             → Well-founded(slex-prod _<_ _<'_)
lex-prod-Well {U} {V} {X} {Y} _<_ _<'_ w w' = lemma
 where
  lemma' : (P : Σ Y → Set) →
      ((z : Σ Y) → ((t : Σ Y) → slex-prod _<_ _<'_ t z → P t) → P z) →
      (x : X) (y : Y x) → P(x , y)
  lemma' P step = w Q claim
   where
    Q : X → V ̇
    Q x = (y : Y x) → P(x , y)
    claim : (x : X) → ((x' : X) → x' < x → (y' : Y x') → P(x' , y')) → (y : Y x) → P(x , y)
    claim x step' = w' (λ y → P(x , y)) (λ y f → step (x , y) (φ y f)) 
     where
      φ : (y : Y x) → ((y' : Y x) → y' <' y → P (x , y')) → (z' : Σ Y) → slex-prod _<_ _<'_ z' (x , y) → P z'
      φ y f (x' , y') (inl l) = step' x' l y'
      φ y f (x' , y') (inr (r , m)) = transport P (fact ⁻¹) almost
       where
        almost : P(x , transport Y r y')
        almost = f (transport Y r y') m
        fact : (x' , y') ≡ (x , transport Y r y') 
        fact = to-Σ-≡ x' x y' (transport Y r y') r refl

  lemma : (P : Σ Y → U₀ ̇) →
      ((z : Σ Y) → ((z' : Σ Y) → slex-prod _<_ _<'_ z' z → P z') → P z) →
      (z : Σ Y) → P z
  lemma P step (x , y) = lemma' P step x y

\end{code}
