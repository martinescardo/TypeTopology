--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

uly 2022
--------------------------------------------------------------------------------

Basicfacts about 2-groups, or categorical groups, in another parlance.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.Equiv hiding (_≅_ ; ≅-refl ; _●_)
open import UF.Groupoids

module 2Groups.Type where

\end{code}

The mathematical structure of a 2-Group

\begin{code}

record 2Group-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _●_ : X → X → X
    is-grpd : is-groupoid X
    α : {x y z : X} → (x ● y) ● z ＝  x ● (y ● z)

  private
    p : (x y z t : X) → ((x ● y) ● z) ● t ＝  x ● (y ● (z ● t))
    p x y z t = ((x ● y) ● z) ● t ＝⟨ ap (λ v → v ● t) α ⟩
                (x ● (y ● z)) ● t ＝⟨ α ⟩
                x ● ((y ● z) ● t) ＝⟨ ap (λ v → x ● v) α ⟩
                x ● (y ● (z ● t)) ∎
    q : (x y z t : X) → ((x ● y) ● z) ● t ＝ x ● (y ● (z ● t))
    q x y z t = ((x ● y) ● z) ● t ＝⟨ α ⟩
                (x ● y) ● (z ● t) ＝⟨ α ⟩
                x ● (y ● (z ● t)) ∎

  field
    π : {x y z t : X} → p x y z t ＝ q x y z t
    e : X
    l : (x : X) → e ● x ＝ x
    r : (x : X) → x ● e ＝ x
    lr : l e ＝ r e

    inv-l : (x : X) → is-equiv (λ v → x ● v)
    inv-r : (x : X) → is-equiv (λ v → v ● x)

2Group : (𝓤 : Universe) → 𝓤 ⁺ ̇
2Group 𝓤 = Σ X ꞉ 𝓤 ̇ , 2Group-structure X

\end{code}
