Ian Ray, 17th July 2025.

We define the join of maps following the development found in Section 2 of
The Join Construction by Egbert Rijke (https://arxiv.org/abs/1701.07538.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.JoinofMaps (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Pullback
open import UF.Pushouts fe

\end{code}

Given maps f : A → X and g : B → X, the fiberwise join A *_X B is given by the
pushout of the pullback of f and g. The join of maps f and g is given by the unique
map from the fiberwise join to X, guarenteed by the universal property of the
pushout. That is,

                      π₂
          A ×_X B -----------> B ---
             |                 |     \
         π₁  |                 | inrr \
             |                 |       \
             V                 V        \ 
             A -----------> A *_X B      | g  
              \     inll         \       |  
               \                  \ u    | 
                \                  \     | 
                 \                  V    V
                   ---------------->   X 
                           f

(this is ugly but I tried).

\begin{code}

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇}
         (f : A → X) (g : B → X)
          where

 open pullback f g

 module _ (push-ex : pushouts-exist pb₁ pb₂)
           where
  
  open pushouts-exist push-ex

  fiber-wise-join : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  fiber-wise-join = pushout

  join-of-maps : fiber-wise-join → X
  join-of-maps = pushout-recursion f g pullback-square

\end{code}

TODO. Properties of the join of maps. REQUIRES FLATTENING LEMMA.
