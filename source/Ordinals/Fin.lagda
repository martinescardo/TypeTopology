Alice Laroche, 25th September 2023

Fin n is an ordinal

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.Fin where

open import Fin.Embeddings
open import Fin.Type
open import Fin.Order
open import MLTT.Spartan
open import Notation.Order
open import Ordinals.Type
open import Ordinals.Notions
open import UF.Embeddings

import Naturals.Order as ℕ

<-is-prop-valued : (n : ℕ) → is-prop-valued {X = Fin n} _<_
<-is-prop-valued n i j = ℕ.<-is-prop-valued ⟦ i ⟧ ⟦ j ⟧

<-is-well-founded : (n : ℕ) → is-well-founded {X = Fin n} _<_
<-is-well-founded n i = recurs (ℕ.<-is-well-founded (⟦ i ⟧))
 where
  recurs : {i : Fin n}
         → is-accessible {X = ℕ} _<_ (⟦ i ⟧)
         → is-accessible {X = Fin n} _<_ i
  recurs (acc rec₁) = acc (λ j r → recurs (rec₁ ⟦ j ⟧ r))

<-is-extensional : (n : ℕ) → is-extensional {X = Fin n} _<_
<-is-extensional (succ n) 𝟎 𝟎 i≼j j≼i = refl
<-is-extensional (succ n) 𝟎 (suc x) i≼j j≼i = 𝟘-elim (j≼i 𝟎 ⋆)
<-is-extensional (succ n) (suc i) 𝟎 i≼j j≼i = 𝟘-elim (i≼j 𝟎 ⋆)
<-is-extensional (succ n) (suc i) (suc j) i≼j j≼i =
 ap suc (<-is-extensional n i j (i≼j ∘ suc) (j≼i ∘ suc))

<-trans : (n : ℕ) → is-transitive {X = Fin n} _<_
<-trans n i j k = ℕ.<-trans ⟦ i ⟧ ⟦ j ⟧ ⟦ k ⟧

<-is-well-order : (n : ℕ) → is-well-order {X = Fin n} _<_
<-is-well-order n = <-is-prop-valued n
                  , <-is-well-founded n
                  , <-is-extensional n
                  , <-trans n

Fin-ordinal : (n : ℕ) → Ord
Fin-ordinal n = Fin n , _<_ , <-is-well-order n

\end{code}
