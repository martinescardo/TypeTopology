\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Identity-Type where

open import MLTT.Universes

data _＝_ {𝓤} {X : 𝓤 ̇ } : X → X → 𝓤 ̇ where
 instance refl : {x : X} → x ＝ x

-Id : (X : 𝓤 ̇ ) → X → X → 𝓤 ̇
-Id X x y = x ＝ y

syntax -Id X x y = x ＝[ X ] y

\end{code}

We don't want built-in equality.

\begin{code}

-- {-# BUILTIN EQUALITY _＝_ #-}

\end{code}
