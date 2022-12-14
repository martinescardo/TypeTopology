--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu

October 2022
--------------------------------------------------------------------------------

Groups are categorical groups.

The key point in the proof is that the extra axioms, namely the
pentagon and the associativity involving the idenity, are
automatically true since the carrier of a group is a set, hence the
path identifications hold automatically.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module 2Groups.Groups where

open import MLTT.Spartan
open import UF.Subsingletons
open import Groups.Type
open import UF.Groupoids
open import 2Groups.Type 

open Cat-Group-structure

Group-structure-is-cat-group : (X : Group 𝓤)
                              → Cat-Group-structure ⟨ X ⟩
Group-structure-is-cat-group X .isMonoidalGrpd ._⊗_ = multiplication X
Group-structure-is-cat-group X .isMonoidalGrpd .e = unit X
Group-structure-is-cat-group X .isMonoidalGrpd .is-monoidal-grpd = record
                                                                     { is-grpd = sets-are-groupoids (group-is-set X)
                                                                     ; is-assoc = assoc X
                                                                     ; has-pentagon = group-is-set X _ _
                                                                     ; unit-left = Groups.Type.unit-left X
                                                                     ; unit-right = Groups.Type.unit-right X
                                                                     ; has-assoc-neutral = group-is-set X  _ _
                                                                     }
Group-structure-is-cat-group X .isCatGroup =
  record { ⊗-inv = λ x → inv X x , (inv-right X x) , (inv-left X x ⁻¹)
         ; ⊗-inv-axioms = λ _ → (group-is-set X _ _) , (group-is-set X _ _) }


Group-is-2-Group : Group 𝓤 → 2-Group 𝓤
Group-is-2-Group X = ⟨ X ⟩ , Group-structure-is-cat-group  X
\end{code}
