Tom de Jong, 30 January 2020.
Refactored December 2021.

Separate file for poset axioms.
This used to be part of DomainTheory.Basics.Dcpo.lagda.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Posets.Poset
        (fe : Fun-Ext)
       where

 module PosetAxioms
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
        where

  is-prop-valued : 𝓤 ⊔ 𝓣 ̇
  is-prop-valued = (x y : D) → is-prop(x ⊑ y)

  is-reflexive : 𝓤 ⊔ 𝓣 ̇
  is-reflexive = (x : D) → x ⊑ x

  is-transitive : 𝓤 ⊔ 𝓣 ̇
  is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

  is-antisymmetric : 𝓤 ⊔ 𝓣 ̇
  is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ＝ y

  poset-axioms : 𝓤 ⊔ 𝓣 ̇
  poset-axioms = is-set D
               × is-prop-valued
               × is-reflexive
               × is-transitive
               × is-antisymmetric

  poset-axioms-is-prop : is-prop (poset-axioms)
  poset-axioms-is-prop = prop-criterion γ
   where
    γ : poset-axioms → is-prop poset-axioms
    γ (s , p , r , t , a) = ×₅-is-prop (being-set-is-prop fe)
                                       (Π₂-is-prop fe (λ x y → being-prop-is-prop fe))
                                       (Π-is-prop fe λ x → p x x)
                                       (Π₅-is-prop fe (λ x y z k l → p x z))
                                       (Π₄-is-prop fe (λ x y k l → s))

  is-greatest : D → 𝓤 ⊔ 𝓣 ̇
  is-greatest x = (y : D) → y ⊑ x

  is-maximal : D → 𝓤 ⊔ 𝓣 ̇
  is-maximal x = (y : D) → x ⊑ y → x ＝ y

\end{code}

Added 25 August 2022, but added elsewhere in TypeTopology much earlier (June
2020): the requirement that D is a set in poset-axioms is redundant.

\begin{code}

  posets-are-sets : is-prop-valued → is-reflexive → is-antisymmetric → is-set D
  posets-are-sets = type-with-prop-valued-refl-antisym-rel-is-set _⊑_

\end{code}

Defines monotone functions.

\begin{code}

 module MonotoneAxioms  -- TODO find occurences of monotonicity and refactor
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
         {E : 𝓤' ̇ }
         (_≼_ : E → E → 𝓣' ̇ )
         (f : D → E)
        where

  is-monotone = ∀ x y → x ⊑ y → f x ≼ f y

  open PosetAxioms _≼_

  being-monotone-is-prop : is-prop-valued → is-prop is-monotone
  being-monotone-is-prop p = Π₃-is-prop fe λ _ _ _ → p _ _

\end{code}
