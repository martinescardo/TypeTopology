A Kuratowski closure operator is a closure operator that preserves joins.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt

open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Posets.KuratowskiClosure
        (fe : Fun-Ext)
       where
open import Posets.Poset fe
open import Posets.Closure fe

\end{code}
