Jon Sterling, started 24th March 2023

Based on the comments of Martín Escardó on the HoTT Mailing List:
https://groups.google.com/g/homotopytypetheory/c/FfiZj1vrkmQ/m/GJETdy0AAgAJ

This module defines a "semistrict" version of the identity type, i.e. one for
which the composition is definitionally associative and unital but for which the
interchange laws are weak.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SemistrictIdentity where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.IdentitySystems

module _ {A : 𝓤 ̇ } where
 _＝s_ : (x y : A) → 𝓤 ̇
 x ＝s y = (z : A) → z ＝ x → z ＝ y

 refl-s : {x : A} → x ＝s x
 refl-s z p = p

 _∙s_ : {x y z : A} (p : x ＝s y) (q : y ＝s z) → x ＝s z
 (p ∙s q) _  = q _ ∘ p _
 infixl 10 _∙s_

 module _ {x y : A} (p : x ＝s y) where
  refl-s-left-unit : refl-s ∙s p ＝ p
  refl-s-left-unit = refl

  refl-s-right-unit : p ∙s refl-s ＝ p
  refl-s-right-unit = refl

 module _ {u v w x : A} (p : u ＝s v) (q : v ＝s w) (r : w ＝s x) where
  ∙s-assoc : p ∙s (q ∙s r) ＝ (p ∙s q) ∙s r
  ∙s-assoc = refl

 module _ {x y : A} where
  to-＝s : x ＝ y → x ＝s y
  to-＝s p z q = q ∙ p

  from-＝s : x ＝s y → x ＝ y
  from-＝s p = p _ refl

  module _ (fe : funext 𝓤 𝓤) where
   to-＝s-is-equiv : is-equiv to-＝s
   pr₁ (pr₁ to-＝s-is-equiv) = from-＝s
   pr₂ (pr₁ to-＝s-is-equiv) q =
    dfunext fe λ z →
    dfunext fe (lem z)
    where
     lem : (z : A) (p : z ＝ x) → p ∙ q x refl ＝ q z p
     lem .x refl = refl-left-neutral
   pr₁ (pr₂ to-＝s-is-equiv) = from-＝s
   pr₂ (pr₂ to-＝s-is-equiv) refl = refl

   to-＝s-equiv : (x ＝ y) ≃ (x ＝s y)
   pr₁ to-＝s-equiv = to-＝s
   pr₂ to-＝s-equiv = to-＝s-is-equiv

 ＝s-id-sys : funext 𝓤 𝓤 → Unbiased-Id-Sys 𝓤 A
 ＝s-id-sys fe = from-path-characterization.id-sys _＝s_ (to-＝s-equiv fe)

\end{code}
