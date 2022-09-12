--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

September 2022
--------------------------------------------------------------------------------

For convenience in other parts of the tree.  Using the convention that
propositions are at level zero, sets are at level one and groupoids
are at level two.

This uses global univalence because UF.hlevels does.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Univalence

module UF.SetsGroupoids (ua : Univalence) where

open import UF.FunExt
open import UF.UA-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.hlevels ua


private  
  fe : funext 𝓤 𝓤
  fe {𝓤} = univalence-gives-funext (ua 𝓤)

is-of-hlevel-one-is-set : (X : 𝓤 ̇) → X is-of-hlevel 1 → is-set X
is-of-hlevel-one-is-set X h {x} {y} = h x y

is-set-is-of-hlevel-one : (X : 𝓤 ̇) → is-set X → X is-of-hlevel 1
is-set-is-of-hlevel-one X i x y = i {x} {y}

is-set-is-of-hlevel-one-equivalent : (X : 𝓤 ̇) →
                                     is-set X ≃ X is-of-hlevel 1
is-set-is-of-hlevel-one-equivalent X = logically-equivalent-props-are-equivalent 
                                              (being-set-is-prop fe)
                                              (hlevel-relation-is-prop 1 X)
                                              (is-set-is-of-hlevel-one X)
                                              (is-of-hlevel-one-is-set X)

is-groupoid : 𝓤 ̇ → 𝓤 ̇
is-groupoid X = {x y : X} → is-set (x ＝ y)

is-groupoid-is-of-hlevel-two : (X : 𝓤 ̇) → is-groupoid X → X is-of-hlevel 2
is-groupoid-is-of-hlevel-two X i x y = λ p q → i

is-of-hlevel-two-is-groupoid : (X : 𝓤 ̇) → X is-of-hlevel 2 → is-groupoid X
is-of-hlevel-two-is-groupoid X h {x} {y} = h x y _ _

being-groupoid-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇} → is-prop (is-groupoid X)
being-groupoid-is-prop fe {X} = subtype-of-prop-is-prop g (ap f) (being-groupoid-is-prop' fe)
  where
    is-groupoid' : 𝓤 ̇ → 𝓤 ̇
    is-groupoid' X = (x y : X) → is-set (x ＝ y)

    being-groupoid-is-prop' : funext 𝓤 𝓤 → {X : 𝓤 ̇} → is-prop (is-groupoid' X)
    being-groupoid-is-prop' fe {X} = Π-is-prop fe
                                     (λ x → Π-is-prop fe (λ y → being-set-is-prop fe))

    f : {X : 𝓤 ̇} → is-groupoid' X → is-groupoid X
    f i {x} {y} = i x y

    g : {X : 𝓤 ̇} → is-groupoid X → is-groupoid' X
    g i x y = i {x} {y}

is-groupoid-is-of-hlevel-two-equivalent : (X : 𝓤 ̇) →
                                          is-groupoid X ≃ X is-of-hlevel 2
is-groupoid-is-of-hlevel-two-equivalent X = logically-equivalent-props-are-equivalent
                                            (being-groupoid-is-prop fe)
                                            (hlevel-relation-is-prop 2 X)
                                            (is-groupoid-is-of-hlevel-two X)
                                            (is-of-hlevel-two-is-groupoid X)

\end{code}
