--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

Basicfacts about 2-groups, or categorical groups, in another parlance.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.Equiv hiding (_≅_ ; ≅-refl)

module 2Groups.Type where

\end{code}

The mathematical structure of a 2-Group

\begin{code}

record 2Group-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    m : X → X → X
    α : (x y z : X) → m (m x y) y ＝ m x (m y z)
    e : X 

\end{code}
