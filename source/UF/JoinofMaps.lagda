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

Given maps f : A → X and g : B → X, the join of types, A *_X B, is given by the
pushout of the pullback of f and g (see diagram below). The join of maps f and
g, f * g, is given by the unique map from A *_X B to X, guarenteed by the
universal property of the pushout. That is,

                      π₂
          A ×_X B -----------> B ----
             |                 |      \
         π₁  |                 | inrr  \
             |                 |        \
             V                 V         \ 
             A -----------> A *_X B       | g  
              \     inll         \        |  
               \                  \       | 
                \           f * g  \      | 
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

 module _ (push-ex : pushout-exists pb₁ pb₂)
           where
  
  open pushout-exists push-ex

  join-of-types : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  join-of-types = pushout

  join-of-maps : join-of-types → X
  join-of-maps = pushout-recursion f g pullback-square

\end{code}

TODO. Properties of the join of maps:
 -universal property, recursion, uniqueness
 -join of fibers is the fiber of joins*
 -join of embeddings is embedding*

*REQUIRES FLATTENING LEMMA
