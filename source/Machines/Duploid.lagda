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

module _ (𝓓 : deductive-system 𝓤 𝓥) where
 open deductive-system 𝓓
 open polarities 𝓓
 open ⊢-properties 𝓓

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
    is-inverse force delay
    × is-linear force)

  downshift-axioms : downshift-data A → 𝓤 ⊔ 𝓥 ̇
  downshift-axioms (⇓A , wrap) =
   is-positive ⇓A ×
   (Σ unwrap ꞉ ⇓A ⊢ A ,
    is-inverse wrap unwrap
    × is-thunkable wrap)


  module upshift-data (ush : upshift-data A) where
   upshift : ob
   upshift = pr₁ ush

   force : upshift ⊢ A
   force = pr₂ ush

  module downshift-data (dsh : downshift-data A) where
   downshift : ob
   downshift = pr₁ dsh

   wrap : A ⊢ downshift
   wrap = pr₂ dsh

  module upshift-axioms {ush : upshift-data A} (ax : upshift-axioms ush) where
   open upshift-data ush

   upshift-negative : is-negative upshift
   upshift-negative = pr₁ ax

   delay : A ⊢ upshift
   delay = pr₁ (pr₂ ax)

   force-delay-inverse : is-inverse force delay
   force-delay-inverse = pr₁ (pr₂ (pr₂ ax))

   force-linear : is-linear force
   force-linear = pr₂ (pr₂ (pr₂ ax))

  module downshift-axioms {dsh : downshift-data A} (ax : downshift-axioms dsh) where
   open downshift-data dsh

   downshift-positive : is-positive downshift
   downshift-positive = pr₁ ax

   unwrap : downshift ⊢ A
   unwrap = pr₁ (pr₂ ax)

   wrap-unwrap-inverse : is-inverse wrap unwrap
   wrap-unwrap-inverse = pr₁ (pr₂ (pr₂ ax))

   wrap-thunkable : is-thunkable wrap
   wrap-thunkable = pr₂ (pr₂ (pr₂ ax))


  module _ (fe0 : funext 𝓤 (𝓤 ⊔ 𝓥)) (fe1 : funext 𝓥 (𝓤 ⊔ 𝓥)) where
   private
    fe2 : funext 𝓥 𝓥
    fe2 = lower-funext 𝓥 𝓤 fe1

   upshift-axioms-is-prop : {ush : _} → is-prop (upshift-axioms ush)
   upshift-axioms-is-prop ax0 ax1 =
    let module ax0 = upshift-axioms ax0 in
    let module ax1 = upshift-axioms ax1 in
    to-×-＝
     (being-negative-is-prop fe0 fe1 _ _)
     (to-Σ-＝
      (thunkable-inverse-is-unique
        ax1.force-delay-inverse
        ax0.force-delay-inverse
        (ax0.upshift-negative _ _) ,
       to-×-＝
        (being-inverse-is-prop _ _ _)
        (being-linear-is-prop fe0 fe2 _ _)))

   downshift-axioms-is-prop : {dsh : _} → is-prop (downshift-axioms dsh)
   downshift-axioms-is-prop ax0 ax1 =
    let module ax0 = downshift-axioms ax0 in
    let module ax1 = downshift-axioms ax1 in
    to-×-＝
     (being-positive-is-prop fe0 fe1 _ _)
     (to-Σ-＝
      (linear-inverse-is-unique
        ax1.wrap-unwrap-inverse
        ax0.wrap-unwrap-inverse
        (ax0.downshift-positive _ _) ,
       to-×-＝
        (being-inverse-is-prop _ _ _)
        (being-thunkable-is-prop fe0 fe2 _ _)))

 module _ (A : ob) where
  has-upshift : 𝓤 ⊔ 𝓥 ̇
  has-upshift = Σ ush ꞉ upshift-data A , upshift-axioms ush

  has-downshift : 𝓤 ⊔ 𝓥 ̇
  has-downshift = Σ dsh ꞉ downshift-data A , downshift-axioms dsh

  module has-upshift (h : has-upshift) where
   open upshift-data (pr₁ h) public
   open upshift-axioms (pr₂ h) public

  module has-downshift (h : has-downshift) where
   open downshift-data (pr₁ h) public
   open downshift-axioms (pr₂ h) public

 has-all-shifts : 𝓤 ⊔ 𝓥 ̇
 has-all-shifts = (A : ob) → has-upshift A × has-downshift A

 -- This is not necessarily a proposition, because we do not yet know how to
 -- state the property that a deductive system is univalent.

 duploid-structure : 𝓤 ⊔ 𝓥 ̇
 duploid-structure =
  preduploid-axioms 𝓓
  × has-all-shifts

 module duploid-structure (str : duploid-structure) where
  underlying-preduploid : preduploid 𝓤 𝓥
  underlying-preduploid = 𝓓 , pr₁ str

  module _ (A : ob) where
   private
    A-has-shifts = pr₂ str A
    module ⇑A = has-upshift A (pr₁ A-has-shifts)
    module ⇓A = has-downshift A (pr₂ A-has-shifts)

   ⇑_ = ⇑A.upshift
   ⇓_ = ⇓A.downshift

  module _ {A : ob} where
   private
    A-has-shifts = pr₂ str A
    module ⇑A = has-upshift A (pr₁ A-has-shifts)
    module ⇓A = has-downshift A (pr₂ A-has-shifts)

   open ⇑A hiding (upshift)
   open ⇓A hiding (downshift)

duploid : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
duploid 𝓤 𝓥 = Σ 𝓓 ꞉ deductive-system 𝓤 𝓥 , duploid-structure 𝓓

module duploid (𝓓 : duploid 𝓤 𝓥) where
 open duploid-structure (pr₁ 𝓓) (pr₂ 𝓓) public
 open preduploid underlying-preduploid public

\end{code}
