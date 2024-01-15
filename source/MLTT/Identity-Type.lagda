\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Identity-Type where

open import MLTT.Universes

data _＝_ {𝓤} {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where
  refl : {x : X} → x ＝ x

-Id : (X : 𝓤 ̇ ) → X → X → 𝓤 ̇
-Id X x y = x ＝ y

syntax -Id X x y = x ＝[ X ] y

\end{code}
