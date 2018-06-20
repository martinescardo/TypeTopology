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

module _ {U V} {X : U ̇} {Y : X → V ̇} (_<_ : bin-rel X) (_≺_ : {x : X} → bin-rel(Y x)) where

 _⊏_ : bin-rel (Σ Y)
 _⊏_ = slex-prod _<_ _≺_

 lex-prod-wf : well-founded _<_
             → ({x : X} → Well-founded (_≺_ {x}))
             → well-founded _⊏_
 lex-prod-wf w w' (x , y) = φ x y
  where
   P : Σ Y → U ⊔ V ̇
   P = is-accessible _⊏_
   γ : (x : X) → ((x' : X) → x' < x → (y' : Y x') → P(x' , y')) → (y : Y x) → P(x , y)
   γ x step = w' (λ y → P(x , y)) (λ y f → next (x , y) (ψ y f)) 
    where
     ψ : (y : Y x) → ((y' : Y x) → y' ≺ y → P (x , y')) → (z' : Σ Y) → z' ⊏ (x , y) → P z'
     ψ y f (x' , y') (inl l) = step x' l y'
     ψ y f (x' , y') (inr (r , m)) = back-transport P p α
      where
       α : P(x , transport Y r y')
       α = f (transport Y r y') m
       p : (x' , y') ≡ (x , transport Y r y') 
       p = to-Σ-≡ x' x y' (transport Y r y') r refl
   φ : (x : X) (y : Y x) → P(x , y)
   φ = transfinite-induction _<_ w (λ x → (y : Y x) → P(x , y)) γ

 lex-prod-trans : transitive _<_
                → ({x : X} → transitive (_≺_ {x}))
                → transitive _⊏_
 lex-prod-trans t t' (a , b) (x , y) (u , v) = f
  where
   f : (a , b) ⊏ (x , y) → (x , y) ⊏ (u , v) → (a , b) ⊏ (u , v)
   f (inl l) (inl m) = inl (t _ _ _ l m)
   f (inl l) (inr (q , m)) = inl (transport (λ x → a < x) q l)
   f (inr (r , l)) (inl m) = inl (back-transport (λ x → x < u) r m)
   f (inr (r , l)) (inr (refl , m)) = inr (r , (t' _ _ _ l m))

{- TODO
 lex-prod-ex : extensional _<_
                → ({x : X} → extensional (_≺_ {x}))
                → extensional _⊏_
 lex-prod-ex = {!!}
-}

\end{code}
