Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module UF.Sets-Properties where

open import MLTT.Spartan
open import UF.Hedberg
open import UF.Sets
open import UF.Subsingletons

subtypes-of-sets-are-sets' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (m : X → Y)
                           → left-cancellable m
                           → is-set Y
                           → is-set X
subtypes-of-sets-are-sets' {𝓤} {𝓥} {X} m i h = Id-collapsibles-are-sets (f , g)
 where
  f : {x x' : X} → x ＝ x' → x ＝ x'
  f r = i (ap m r)

  g : {x x' : X} (r s : x ＝ x') → f r ＝ f s
  g r s = ap i (h (ap m r) (ap m s))

subsets-of-sets-are-sets : (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                         → is-set X
                         → ({x : X} → is-prop (Y x))
                         → is-set (Σ x ꞉ X , Y x)
subsets-of-sets-are-sets X Y h p = subtypes-of-sets-are-sets' pr₁ (pr₁-lc p) h

\end{code}
