Tom de Jong, 30 January 2020.
Refactored December 2021.

Separate file for poset axioms.
This used to be part of Dcpo.lagda.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module Poset
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
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
  is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

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
  is-maximal x = (y : D) → x ⊑ y → x ≡ y

\end{code}
