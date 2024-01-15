--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

September 2022
--------------------------------------------------------------------------------

For convenience in other parts of the tree.  Using the convention that
propositions are at level zero, sets are at level one and groupoids
are at level two.

We define is-groupoid as an analog of is-set and is-prop,
independently of hlevels. Since UF.hlevels uses global univalence,
hlevel stuff is confined in a submodule below.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Univalence

module UF.Groupoids where

open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

is-groupoid : 𝓤 ̇ → 𝓤 ̇
is-groupoid X = {x y : X} → is-set (x ＝ y)

being-groupoid-is-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-groupoid X)
being-groupoid-is-prop fe = Π-is-prop' fe (λ x →
                            Π-is-prop' fe (λ x' → being-set-is-prop fe))
\end{code}

Sets are Groupoids.

\begin{code}

sets-are-groupoids : {X : 𝓤 ̇} → is-set X → is-groupoid X
sets-are-groupoids i = props-are-sets i

\end{code}

UF.hlevels uses global univalence.

\begin{code}

module hleveltwo (ua : Univalence)  where

  open import UF.HLevels ua

  private
    fe : funext 𝓤 𝓤
    fe {𝓤} = univalence-gives-funext (ua 𝓤)

  is-groupoid-is-of-hlevel-two : (X : 𝓤 ̇ )→ is-groupoid X → X is-of-hlevel 2
  is-groupoid-is-of-hlevel-two X i x y = λ p q → i

  is-of-hlevel-two-is-groupoid : (X : 𝓤 ̇ )→ X is-of-hlevel 2 → is-groupoid X
  is-of-hlevel-two-is-groupoid X h {x} {y} = h x y _ _


  is-groupoid-is-of-hlevel-two-equivalent : (X : 𝓤 ̇ )→
                                            is-groupoid X ≃ X is-of-hlevel 2
  is-groupoid-is-of-hlevel-two-equivalent X = logically-equivalent-props-are-equivalent
                                              (being-groupoid-is-prop fe)
                                              (hlevel-relation-is-prop 2 X)
                                              (is-groupoid-is-of-hlevel-two X)
                                              (is-of-hlevel-two-is-groupoid X)
\end{code}

This is here for want of a better place.

\begin{code}

  is-of-hlevel-one-is-set : (X : 𝓤 ̇ )→ X is-of-hlevel 1 → is-set X
  is-of-hlevel-one-is-set X h {x} {y} = h x y

  is-set-is-of-hlevel-one : (X : 𝓤 ̇ )→ is-set X → X is-of-hlevel 1
  is-set-is-of-hlevel-one X i x y = i {x} {y}

  is-set-is-of-hlevel-one-equivalent : (X : 𝓤 ̇ )→
                                       is-set X ≃ X is-of-hlevel 1
  is-set-is-of-hlevel-one-equivalent X = logically-equivalent-props-are-equivalent
                                                (being-set-is-prop fe)
                                                (hlevel-relation-is-prop 1 X)
                                                (is-set-is-of-hlevel-one X)
                                                (is-of-hlevel-one-is-set X)


\end{code}
