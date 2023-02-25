Jon Sterling, started 25th Feb 2023

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
import Duploids.Duploid

module Duploids.EffectfulShiftAdjunction
 (fe : Fun-Ext)
 (pt : propositional-truncations-exist)
 (𝓓 : Duploids.Duploid.duploid fe pt 𝓤 𝓥)
 where

open import UF.Base
open import UF.Retracts
open import UF.Subsingletons

open import Categories.Category fe
open import Categories.Functor fe
open import Categories.NaturalTransformation fe
open import Categories.Adjunction fe
open import Duploids.Preduploid
open import Duploids.Duploid fe pt

private module 𝓓 = duploid 𝓓
open duploid-extras 𝓓
open duploid-notation 𝓓
open functor-of-precategories

open import Duploids.Categories fe pt 𝓓.underlying-preduploid
open import Duploids.ShiftFunctors fe pt 𝓓

[⇑-⇓] : functor 𝓟 𝓟
[⇑-⇓] = composite-functor.fun [⇑] [⇓]

[⇓-⇑] : functor 𝓝 𝓝
[⇓-⇑] = composite-functor.fun [⇓] [⇑]

1[𝓝] : functor 𝓝 𝓝
1[𝓝] = identity-functor.fun 𝓝

1[𝓟] : functor 𝓟 𝓟
1[𝓟] = identity-functor.fun 𝓟

open adjunction-of-precategories 𝓝 𝓟
open natural-transformation

module unit where
 str : transf _ _ 1[𝓝] [⇓-⇑]
 str M = 𝓌 >> 𝒹

 abstract
  ax : is-natural _ _ 1[𝓝] [⇓-⇑] str
  ax M N f =
   f >> (𝓌 >> 𝒹 {𝓓.⇓ (pr₁ N)}) ＝⟨ 𝒹[⇓]-linear _ _ _ _ ⁻¹ ⟩
   (f >> 𝓌) >> 𝒹 ＝⟨ ap (_>> 𝒹) lem ⟩
   ((𝓌 >> 𝒹) >> (𝒻 >> (𝓊 >> (f >> 𝓌)))) >> 𝒹 ＝⟨ 𝒹[⇓]-linear _ _ _ _ ⟩
   (𝓌 >> 𝒹) >> ((𝒻 >> (𝓊 >> (f >> 𝓌))) >> 𝒹) ＝⟨ ap ((𝓌 >> 𝒹) >>_) (𝒹[⇓]-linear _ _ _ _) ⟩
   (𝓌 >> 𝒹) >> (𝒻 >> ((𝓊 >> (f >> 𝓌)) >> 𝒹)) ∎

   where
    𝒹[⇓]-linear : {Z : _} → 𝓓.is-linear (𝒹 {𝓓.⇓ Z})
    𝒹[⇓]-linear = 𝓓.⇓-positive _ _ _

    lem : (f >> 𝓌) ＝ (𝓌 >> 𝒹) >> (𝒻 >> (𝓊 >> (f >> 𝓌)))
    lem =
     f >> 𝓌 ＝⟨ lem-𝓌[𝓊-] ⁻¹ ⟩
     𝓌 >> (𝓊 >> (f >> 𝓌)) ＝⟨ ap (𝓌 >>_) (lem-𝒹[𝒻-] ⁻¹) ⟩
     𝓌 >> (𝒹 >> (𝒻 >> (𝓊 >> (f >> 𝓌)))) ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⁻¹ ⟩
     (𝓌 >> 𝒹) >> (𝒻 >> (𝓊 >> (f >> 𝓌))) ∎

 unit : nat-transf _ _ 1[𝓝] [⇓-⇑]
 unit = make str ax

module counit where
 str : transf _ _ [⇑-⇓] 1[𝓟]
 str P = 𝓊 >> 𝒻

 abstract
  ax : is-natural _ _ [⇑-⇓] 1[𝓟] str
  ax P Q f =
   (𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> (𝓊 >> 𝒻) ＝⟨ 𝓓.force-linear _ _ _ _ ⁻¹ ⟩
   ((𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> 𝓊) >> 𝒻 ＝⟨ ap (_>> 𝒻) lem1 ⟩
   (𝓊 >> (𝒻 >> (f >> 𝒹))) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
   𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝒻) ＝⟨ ap (𝓊 >>_) lem2 ⟩
   𝓊 >> (𝒻 >> f) ＝⟨ f-lin _ _ _ _ ⁻¹ ⟩
   (𝓊 >> 𝒻) >> f ∎

   where
    f-lin : 𝓓.is-linear f
    f-lin = pr₂ P (pr₁ Q) f

    lem1 : (𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> 𝓊 ＝ (𝓊 >> (𝒻 >> (f >> 𝒹)))
    lem1 =
     (𝓊 >> ((𝒻 >> (f >> 𝒹)) >> 𝓌)) >> 𝓊 ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⟩
     𝓊 >> (((𝒻 >> (f >> 𝒹)) >> 𝓌) >> 𝓊) ＝⟨ ap (𝓊 >>_) lem-[-𝓌]𝓊 ⟩
     𝓊 >> (𝒻 >> (f >> 𝒹)) ∎

    lem2 : (𝒻 >> (f >> 𝒹)) >> 𝒻 ＝ 𝒻 >> f
    lem2 =
     (𝒻 >> (f >> 𝒹)) >> 𝒻 ＝⟨ 𝓓.force-linear _ _ _ _ ⟩
     𝒻 >> ((f >> 𝒹) >> 𝒻) ＝⟨ ap (𝒻 >>_) lem-[-𝒹]𝒻 ⟩
     𝒻 >> f ∎

 counit : nat-transf _ _ [⇑-⇓] 1[𝓟]
 counit = make str ax

str : adjunction-structure [⇓] [⇑]
pr₁ str = unit.unit
pr₂ str = counit.counit

abstract
 ax : adjunction-axioms [⇓] [⇑] str
 pr₁ ax =
  to-nat-transf-＝ 𝓝 𝓟 [⇓] [⇓]
   (dfunext fe λ M →
    (𝓓.idn _ >> (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌))) >> ((𝓓.idn _) >> ((𝓊 >> 𝒻) >> 𝓓.idn _))
     ＝⟨ ap (_>> (𝓓.idn _ >> ((𝓊 >> 𝒻) >> 𝓓.idn _))) (𝓓.idn-L _ _ _) ⟩
    (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> ((𝓓.idn _) >> ((𝓊 >> 𝒻) >> 𝓓.idn _))
     ＝⟨ ap ((𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >>_) lem1 ⟩
    (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> (𝓊 >> 𝒻)
     ＝⟨ 𝓓.force-linear _ _ _ _ ⁻¹ ⟩
    ((𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> 𝓊) >> 𝒻
     ＝⟨ ap (_>> 𝒻) lem0 ⟩
    𝒹 >> 𝒻
     ＝⟨ pr₂ 𝓓.force-delay-inverse ⟩
    𝓓.idn _ ∎)

  where
   lem0 : {A : _} → (𝓊 {A} >> ((𝓌 >> 𝒹) >> 𝓌)) >> 𝓊 ＝ 𝒹
   lem0 =
    (𝓊 >> ((𝓌 >> 𝒹) >> 𝓌)) >> 𝓊 ＝⟨ 𝓓.unwrap-linear _ _ _ _ ⟩
    (𝓊 >> (((𝓌 >> 𝒹) >> 𝓌) >> 𝓊)) ＝⟨ ap (𝓊 >>_) lem-[-𝓌]𝓊 ⟩
    (𝓊 >> (𝓌 >> 𝒹)) ＝⟨ lem-𝓊[𝓌-] ⟩
    𝒹 ∎

   lem1 : {A B : _} {f : A 𝓓.⊢ B} → (𝓓.idn _ >> (f >> 𝓓.idn _)) ＝ f
   lem1 =
    𝓓.idn _ >> (_ >> 𝓓.idn _) ＝⟨ 𝓓.idn-L _ _ _ ⟩
    _ >> 𝓓.idn _ ＝⟨ 𝓓.idn-R _ _ _ ⟩
    _ ∎

 pr₂ ax =
  to-nat-transf-＝ 𝓟 𝓝 [⇑] [⇑]
   (dfunext fe λ P →
    (𝓓.idn _ >> (𝓌 >> 𝒹)) >> (𝓓.idn _ >> ((𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)) >> 𝓓.idn _))
     ＝⟨ ap (_>> (𝓓.idn _ >> ((𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)) >> 𝓓.idn _))) (𝓓.idn-L _ _ _) ⟩
    (𝓌 >> 𝒹) >> (𝓓.idn _ >> ((𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)) >> 𝓓.idn _))
     ＝⟨ ap ((𝓌 >> 𝒹) >>_) (lem0 ((𝓊 >> 𝒻) >> 𝒹)) ⟩
    (𝓌 >> 𝒹) >> (𝒻 >> ((𝓊 >> 𝒻) >> 𝒹))
     ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⟩
    𝓌 >> (𝒹 >> (𝒻 >> ((𝓊 >> 𝒻) >> 𝒹)))
     ＝⟨ ap (𝓌 >>_) lem-𝒹[𝒻-] ⟩
    𝓌 >> ((𝓊 >> 𝒻) >> 𝒹)
     ＝⟨ 𝓓.wrap-thunkable _ _ _ _ ⁻¹ ⟩
    (𝓌 >> (𝓊 >> 𝒻)) >> 𝒹
     ＝⟨ ap (_>> 𝒹) lem-𝓌[𝓊-] ⟩
    𝒻 >> 𝒹
     ＝⟨ pr₁ 𝓓.force-delay-inverse ⟩
    𝓓.idn _ ∎ )
  where
   lem0
    : {U V : _} (f : 𝓓.⇓ (𝓓.⇑ U) 𝓓.⊢ V)
    → (𝓓.idn _ >> ((𝒻 >> f) >> 𝓓.idn _)) ＝ (𝒻 >> f)
   lem0 f =
    𝓓.idn _ >> ((𝒻 >> f) >> 𝓓.idn _)
     ＝⟨ 𝓓.idn-L _ _ _ ⟩
    (𝒻 >> f) >> 𝓓.idn _
     ＝⟨ 𝓓.idn-R _ _ _ ⟩
    𝒻 >> f ∎

adj : adjunction [⇓] [⇑]
adj = make str ax

\end{code}
