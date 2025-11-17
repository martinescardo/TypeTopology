Martin Escardo 7th November 2025

Characterization of equality using only propositional extensionality
and function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.Identity
        (𝓣 : Universe)
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
       where

open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Lifting.Construction 𝓣

_⋍_ : 𝓛 X → 𝓛 X → 𝓣 ⊔ 𝓤 ̇
l ⋍ m = Σ (f , g) ꞉ (is-defined l ↔ is-defined m) , value l ∼ value m ∘ f

module _ {l@(P , φ , i) m@(Q , ψ , j)  : 𝓛 X} where

 to-⋍ : l ＝ m → l ⋍ m
 to-⋍ refl = (id , id) , (λ x → refl)

 module _ (pe : propext 𝓣)
          (fe : funext 𝓣 𝓤)
          (fe' : funext 𝓣 𝓣)
        where

  from-⋍ : l ⋍ m → l ＝ m
  from-⋍ ((f , g) , h) = III
   where
    I : (e : P ＝ Q) → transport (λ - → (- → X) × is-prop -) e (φ , i) ＝ (ψ , j)
    I refl = to-×-＝
              (dfunext fe (λ (p : P) → φ p     ＝⟨ h p ⟩
                                       ψ (f p) ＝⟨ ap ψ (i (f p) p) ⟩
                                       ψ p     ∎))
              (being-prop-is-prop fe' i j)

    II : P ＝ Q
    II = pe i j f g

    III : (P , φ , i) ＝ (Q , ψ , j)
    III = to-Σ-＝ (II , I II)

\end{code}

The following can be proved replacing the assumption that X is a set
by univalence. See the module IdentityViaSIP.

\begin{code}

  module _ (X-is-set : is-set X) where

   to-from-⋍ : to-⋍ ∘ from-⋍ ∼ id
   to-from-⋍ ((f , g) , h) =
    to-Σ-＝
     (to-×-＝
       (dfunext fe' (λ p → being-defined-is-prop m _ (f p)))
       (dfunext fe' (λ q → being-defined-is-prop l _ (g q))) ,
     dfunext fe (λ p → X-is-set _ _))

   from-to-⋍ : from-⋍ ∘ to-⋍ ∼ id
   from-to-⋍ refl = 𝓛-is-set fe' fe pe X-is-set (from-⋍ (to-⋍ refl)) refl

   𝓛-Id : (l ＝ m) ≃ (l ⋍ m)
   𝓛-Id = qinveq to-⋍ (from-⋍ , from-to-⋍ , to-from-⋍)

\end{code}
