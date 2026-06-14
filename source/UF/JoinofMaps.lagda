Ian Ray, 17th July 2025.

We define the join of maps following the development found in Section 2 of
The Join Construction by Egbert Rijke (https://arxiv.org/abs/1701.07538.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.JoinofMaps (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Pullback
open import UF.Pushouts fe

\end{code}

Given maps f : A → X and g : B → X, the join of types, A *_X B, is given by the
pushout of the pullback of f and g (see diagram below). The join of maps f and
g, f * g, is given by the unique map from A *_X B to X, guarenteed by the
universal property of the pushout. That is,

                      pb₂
          A ×_X B -----------> B ----
             |                 |      \
         pb₁ |                 | inrr  \
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

\begin{code}

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇}
         (f : A → X) (g : B → X)
          where

 open pullback f g

 module _ (Push-Ex : pushouts-exist) where

  open pushouts-exist Push-Ex
  open pushout-exists (push-ex pb₁ pb₂)

  join-of-types : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  join-of-types = pushout

  join-of-maps : join-of-types → X
  join-of-maps = pushout-recursion f g pullback-square

  join-of-maps-inll : join-of-maps ∘ inll ∼ f
  join-of-maps-inll = pushout-rec-comp-inll f g pullback-square 

  join-of-maps-inrr : join-of-maps ∘ inrr ∼ g
  join-of-maps-inrr = pushout-rec-comp-inrr f g pullback-square

  join-of-maps-glue : (c : pullback)
                    → ap join-of-maps (glue c) ∙ join-of-maps-inrr (pb₂ c) 
                    ＝ join-of-maps-inll (pb₁ c) ∙ pullback-square c
  join-of-maps-glue = pushout-rec-comp-glue f g pullback-square

\end{code}

This result ended up not being neccesary and type checks very slowly so I am
going to comment it out for now. May remove/rework it completley. 

  join-of-maps-uniqueness
   : (u : join-of-types → X)
   → (H : f ∼ u ∘ inll)
   → (G : g ∼ u ∘ inrr)
   → (M : (c : pullback)
        → pullback-square c ∙ G (pb₂ c) ＝ H (pb₁ c) ∙ ap u (glue c))
   → join-of-maps ∼ u
  join-of-maps-uniqueness u H G M = pushout-uniqueness join-of-maps u I II IV
   where
    I : (a : A) → join-of-maps (inll a) ＝ u (inll a)
    I a = pushout-rec-comp-inll f g pullback-square a ∙ H a
    II : (b : B) → join-of-maps (inrr b) ＝ u (inrr b)
    II b = pushout-rec-comp-inrr f g pullback-square b ∙ G b
    III : (c : pullback)
        → ap join-of-maps (glue c)
          ∙ pushout-rec-comp-inrr f g pullback-square (pb₂ c)
        ＝ pushout-rec-comp-inll f g pullback-square (pb₁ c)
          ∙ pullback-square c
    III = pushout-rec-comp-glue f g pullback-square
    IV : (c : pullback)
        → ap join-of-maps (glue c) ∙ II (pb₂ c) ＝ I (pb₁ c) ∙ ap u (glue c)
    IV c = ap join-of-maps (glue c)
           ∙ (pushout-rec-comp-inrr f g pullback-square (pb₂ c)
           ∙ G (pb₂ c))                                           ＝⟨ V ⟩
           ap join-of-maps (glue c)
           ∙ pushout-rec-comp-inrr f g pullback-square (pb₂ c)
           ∙ G (pb₂ c)                                            ＝⟨ VI ⟩
           pushout-rec-comp-inll f g pullback-square (pb₁ c)
           ∙ pullback-square c ∙ G (pb₂ c)                        ＝⟨ VII ⟩
           pushout-rec-comp-inll f g pullback-square (pb₁ c)
           ∙ H (pb₁ c) ∙ ap u (glue c)                            ∎
     where
      V = ∙assoc (ap join-of-maps (glue c))
           (pushout-rec-comp-inrr f g pullback-square (pb₂ c)) (G (pb₂ c)) ⁻¹
      VI = ap (_∙ G (pb₂ c)) (III c)
      VII = ∙assoc (pushout-rec-comp-inll f g pullback-square (pb₁ c))
             (pullback-square c) (G (pb₂ c))
            ∙ ap (pushout-rec-comp-inll f g pullback-square (pb₁ c) ∙_) (M c)
            ∙ ∙assoc (pushout-rec-comp-inll f g pullback-square (pb₁ c))
              (H (pb₁ c)) (ap u (glue c)) ⁻¹

\end{code}

TODO. Properties of the join of maps:
 -universal property
 -join of fibers is the fiber of joins*
 -join of embeddings is embedding*

*REQUIRES FLATTENING LEMMA
