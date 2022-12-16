Jon Sterling, started 27th Sep 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF.PropTrunc

module Machines.Duploid (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Lower-FunExt

open import Machines.DeductiveSystem
open import Machines.Preduploid pt

module _ {𝓤 𝓥} (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓

 module _ (A : ob) where
  upshift-data : 𝓤 ⊔ 𝓥 ̇
  upshift-data = Σ ⇑A ꞉ ob , ⇑A ⊢ A

  downshift-data : 𝓤 ⊔ 𝓥 ̇
  downshift-data = Σ ⇓A ꞉ ob , A ⊢ ⇓A

 module _ {A : ob} where
  upshift-axioms : upshift-data A → 𝓤 ⊔ 𝓥 ̇
  upshift-axioms (⇑A , force) =
   is-negative ⇑A ×
   (Σ delay ꞉ A ⊢ ⇑A ,
    are-inverse force delay
    × is-linear force)

  downshift-axioms : downshift-data A → 𝓤 ⊔ 𝓥 ̇
  downshift-axioms (⇓A , wrap) =
   is-positive ⇓A ×
   (Σ unwrap ꞉ ⇓A ⊢ A ,
    are-inverse wrap unwrap
    × is-thunkable wrap)

  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
   private
    fe2 : funext 𝓥 𝓥
    fe2 = lower-funext 𝓥 𝓤 fe1

   upshift-axioms-is-prop : {ush : _} → is-prop (upshift-axioms ush)
   upshift-axioms-is-prop (n0 , d0 , i0 , _) (_ , _ , i1 , _) =
    to-×-＝
     (is-negative-is-prop fe0 fe1 _ _)
     (to-Σ-＝
      (thunkable-inverse-is-unique i1 i0 (n0 _ _) ,
       to-×-＝
        (are-inverse-is-prop _ _)
        (is-linear-is-prop fe0 fe2 _ _)))

   downshift-axioms-is-prop : {dsh : _} → is-prop (downshift-axioms dsh)
   downshift-axioms-is-prop (p0 , u0 , i0 , _) (_ , _ , i1 , _) =
    to-×-＝
     (is-positive-is-prop fe0 fe1 _ _)
     (to-Σ-＝
      (linear-inverse-is-unique i1 i0 (p0 _ _) ,
       to-×-＝
        (are-inverse-is-prop _ _)
        (is-thunkable-is-prop fe0 fe2 _ _)))


 module _ (A : ob) where
  has-upshift : 𝓤 ⊔ 𝓥 ̇
  has-upshift = Σ ush ꞉ upshift-data A , upshift-axioms ush

  has-downshift : 𝓤 ⊔ 𝓥 ̇
  has-downshift = Σ dsh ꞉ downshift-data A , downshift-axioms dsh


 has-all-shifts : 𝓤 ⊔ 𝓥 ̇
 has-all-shifts = (A : ob) → has-upshift A × has-downshift A


 -- This is not necessarily a proposition, because we do not yet know how to
 -- state the property that a deductive system is univalent.

 duploid-structure : 𝓤 ⊔ 𝓥 ̇
 duploid-structure =
  preduploid-axioms 𝓓
  × has-all-shifts

\end{code}
