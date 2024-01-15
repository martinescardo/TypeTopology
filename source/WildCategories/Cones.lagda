Jon Sterling and Mike Shulman, September 2023.

Arguments due to Mike Shulman, typed into Agda by Jon Sterling.

The results of this module are as follows:

1. Let P : Δ I → Id[C] be an incoherent cone over the identity functor on a
   wild category C. If the “generic point” P[I] : I → I is the identity map,
   then I is an initial object of C.

2. Let P : Δ I → Id[C] be a incoherent cone over the identity functor on a
   wild category C. If the generic point p[I] : I → I admits a splitting
   I → J → I, then J is the initial object of C.

3. Let P : Δ I → Id[C] be a “semicoherent cone”. Then the generic point
   p[I] : I → I has the structure of a quasi-idempotent in the sense of Shulman.

It follows therefore that a wild category in which all quasi-idempotents split
has an initial object when it possesses a semicoherent cone over the identity
functor.

\begin{code}
{-# OPTIONS --safe --without-K #-}

module WildCategories.Cones where

open import MLTT.Spartan
open import UF.Base
open import UF.Subsingletons

open import WildCategories.Base
open import WildCategories.Idempotents

module _ {𝓤 𝓥} (C : WildCategory 𝓤 𝓥) where
 open WildCategory C

 record IncohIdnCone : 𝓤 ⊔ 𝓥 ̇ where
  field
   apex : ob
   cone : (x : ob) → hom apex x
   nat
    : {x y : ob} (f : hom x y)
    → f << cone x ＝ cone y

  gen : hom apex apex
  gen = cone apex

  gen# : (gen << cone apex) ＝ cone apex
  gen# = nat gen

  has-coherent-generic-point : 𝓥 ̇
  has-coherent-generic-point = gen ＝ idn apex

 record SemicohIdnCone : 𝓤 ⊔ 𝓥 ̇ where
  field
   apex : ob
   cone : (x : ob) → hom apex x
   nat
    : {x y : ob} (f : hom x y)
    → f << cone x ＝ cone y
   coh
    : {x y z : ob} (f : hom x y) (g : hom y z) (h : hom x z)
    → (K : g << f ＝ h)
    → ap (_<< cone x) K ∙ nat h
    ＝ assoc (cone x) f g ⁻¹ ∙ ap (g <<_) (nat f) ∙ nat g

  underlying-incoh-cone : IncohIdnCone
  underlying-incoh-cone = record { apex = apex ; cone = cone ; nat = nat }

  open IncohIdnCone underlying-incoh-cone public hiding (apex; cone; nat)


 module _ (P : IncohIdnCone) where
  private
   module P = IncohIdnCone P

  apex-is-initial : P.has-coherent-generic-point → is-initial-object C P.apex
  pr₁ (apex-is-initial coh x) = P.cone x
  pr₂ (apex-is-initial coh x) f =
   P.cone x ＝⟨ P.nat f ⁻¹ ⟩
   f << P.gen ＝⟨ ap (f <<_) coh ⟩
   f << idn P.apex ＝⟨ lunit f ⟩
   f ∎

 module _ (P : IncohIdnCone) where
  private
   module P = IncohIdnCone P

  module _ (gen-split : Splitting C _ P.gen) where
   private
    module gen-split = Splitting gen-split

   S : IncohIdnCone
   IncohIdnCone.apex S = gen-split.mid
   IncohIdnCone.cone S x = P.cone x << gen-split.sec
   IncohIdnCone.nat S f =
    assoc gen-split.sec (P.cone _) f
    ∙ ap (_<< gen-split.sec) (P.nat f)

   private
    module S = IncohIdnCone S

   coh : S.has-coherent-generic-point
   coh = ap (_<< gen-split.sec) H ∙ gen-split.sec-is-section
    where
     H : P.cone gen-split.mid ＝ gen-split.ret
     H =
      P.cone gen-split.mid
       ＝⟨ P.nat gen-split.ret ⁻¹ ⟩
      gen-split.ret << P.gen
       ＝⟨ ap (gen-split.ret <<_) (gen-split.splitting ⁻¹) ⟩
      gen-split.ret << (gen-split.sec << gen-split.ret)
       ＝⟨ assoc gen-split.ret gen-split.sec gen-split.ret ⟩
      (gen-split.ret << gen-split.sec) << gen-split.ret
       ＝⟨ ap (_<< gen-split.ret) gen-split.sec-is-section ⟩
      idn _ << gen-split.ret
       ＝⟨ runit gen-split.ret ⟩
      gen-split.ret ∎

   initiality : has-initial-object C
   pr₁ initiality = S.apex
   pr₂ initiality = apex-is-initial S coh


 module _ (P : SemicohIdnCone) where
  private
   module P = SemicohIdnCone P
   gen-gen# = ap (P.gen <<_) P.gen#
   gen#-gen = ap (_<< P.gen) P.gen#

  open QuasiIdempotence

  gen-qidem : QuasiIdempotence C P.apex P.gen
  Q0 gen-qidem = P.gen#
  Q1 gen-qidem = cancel-right _ _ P.gen# H2

   where
    H0 : gen#-gen ∙ P.gen# ＝ assoc P.gen P.gen P.gen ⁻¹ ∙ gen-gen# ∙ P.gen#
    H0 = P.coh P.gen P.gen P.gen P.gen#

    H1 : assoc P.gen P.gen P.gen ∙ (gen#-gen ∙ P.gen#) ＝ gen-gen# ∙ P.gen#
    H1 =
     assoc P.gen P.gen P.gen ∙ (gen#-gen ∙ P.gen#)
      ＝⟨ ap (assoc P.gen P.gen P.gen ∙_) H0 ⟩
     assoc P.gen P.gen P.gen ∙ (assoc P.gen P.gen P.gen ⁻¹ ∙ gen-gen# ∙ P.gen#)
      ＝⟨ ap (assoc P.gen P.gen P.gen ∙_) (∙assoc (assoc P.gen P.gen P.gen ⁻¹) (gen-gen#) P.gen#) ⟩
     assoc P.gen P.gen P.gen ∙ (assoc P.gen P.gen P.gen ⁻¹ ∙ (gen-gen# ∙ P.gen#))
      ＝⟨ ∙assoc (assoc P.gen P.gen P.gen) (assoc P.gen P.gen P.gen ⁻¹) (gen-gen# ∙ P.gen#) ⁻¹ ⟩
     (assoc P.gen P.gen P.gen ∙ assoc P.gen P.gen P.gen ⁻¹) ∙ (gen-gen# ∙ P.gen#)
      ＝⟨ ap (_∙ (gen-gen# ∙ P.gen#)) (right-inverse (assoc P.gen P.gen P.gen) ⁻¹) ⟩
     refl ∙ (gen-gen# ∙ P.gen#)
      ＝⟨ refl-left-neutral ⟩
     gen-gen# ∙ P.gen# ∎

    H2 : assoc _ _ _ ∙ gen#-gen ∙ P.gen# ＝ gen-gen# ∙ P.gen#
    H2 = ∙assoc (assoc _ _ _ ) (gen#-gen) P.gen# ∙ H1

\end{code}
