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
 _＝ₛ_ : (x y : A) → 𝓤 ̇
 x ＝ₛ y = (z : A) → z ＝ x → z ＝ y

 refl-s : {x : A} → x ＝ₛ x
 refl-s z p = p

 _∙ₛ_ : {x y z : A} (p : x ＝ₛ y) (q : y ＝ₛ z) → x ＝ₛ z
 (p ∙ₛ q) _  = q _ ∘ p _
 infixl 10 _∙ₛ_

 module _ {x y : A} (p : x ＝ₛ y) where
  refl-s-left-unit : refl-s ∙ₛ p ＝ p
  refl-s-left-unit = refl

  refl-s-right-unit : p ∙ₛ refl-s ＝ p
  refl-s-right-unit = refl

 module _ {u v w x : A} (p : u ＝ₛ v) (q : v ＝ₛ w) (r : w ＝ₛ x) where
  ∙ₛ-assoc : p ∙ₛ (q ∙ₛ r) ＝ (p ∙ₛ q) ∙ₛ r
  ∙ₛ-assoc = refl

 module _ {x y : A} where
  to-＝ₛ : x ＝ y → x ＝ₛ y
  to-＝ₛ p z q = q ∙ p

  from-＝ₛ : x ＝ₛ y → x ＝ y
  from-＝ₛ p = p _ refl

  module _ (fe : funext 𝓤 𝓤) where
   to-＝ₛ-is-equiv : is-equiv to-＝ₛ
   pr₁ (pr₁ to-＝ₛ-is-equiv) = from-＝ₛ
   pr₂ (pr₁ to-＝ₛ-is-equiv) q =
    dfunext fe λ z →
    dfunext fe (lem z)
    where
     lem : (z : A) (p : z ＝ x) → p ∙ q x refl ＝ q z p
     lem .x refl = refl-left-neutral
   pr₁ (pr₂ to-＝ₛ-is-equiv) = from-＝ₛ
   pr₂ (pr₂ to-＝ₛ-is-equiv) refl = refl

   to-＝ₛ-equiv : (x ＝ y) ≃ (x ＝ₛ y)
   pr₁ to-＝ₛ-equiv = to-＝ₛ
   pr₂ to-＝ₛ-equiv = to-＝ₛ-is-equiv

 ＝ₛ-id-sys : funext 𝓤 𝓤 → Unbiased-Id-Sys 𝓤 A
 ＝ₛ-id-sys fe = from-path-characterization.id-sys _＝ₛ_ (to-＝ₛ-equiv fe)

\end{code}
