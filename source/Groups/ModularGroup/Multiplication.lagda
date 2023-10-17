Lane Biocini, 21 January 2026

Group multiplication defined via generator iteration: x · y applies
the generator sequence of x to y. Formally, x · y = PSL2Z-gen-iter y s r x.

This definition makes E the left identity definitionally (E · y = y),
while the right identity (x · E = x) and associativity require proof
by induction on the Cayley graph structure.

The key lemmas ·-s-left and ·-r-left establish that the generators
act as left multiplication: (s x) · y = s (x · y) and (r x) · y = r (x · y).
Associativity then follows by generator induction.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Groups.ModularGroup.Multiplication where

open import MLTT.Spartan
open import UF.Base
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Base
open import Groups.ModularGroup.Properties
open import Groups.ModularGroup.Induction

_·_ : PSL2Z → PSL2Z → PSL2Z
x · y = PSL2Z-gen-iter y s r x

infixl 30 _·_

·-s-left : (x y : PSL2Z) → (s x) · y ＝ s (x · y)
·-s-left = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (y : PSL2Z) → (s E) · y ＝ s (E · y)
  base-E y = refl

  base-S : (y : PSL2Z) → (s S) · y ＝ s (S · y)
  base-S y = s² y ⁻¹

  ind-s : (re : R-edge)
        → ((y : PSL2Z) → (s (θ re)) · y ＝ s ((θ re) · y))
        → (y : PSL2Z) → (s (s∙ re)) · y ＝ s ((s∙ re) · y)
  ind-s re ih y =
   s (s∙ re) · y         ＝⟨ refl ⟩
   (θ re) · y            ＝⟨ s² ((θ re) · y) ⁻¹ ⟩
   s (s ((θ re) · y))    ＝⟨ refl ⟩
   s ((s∙ re) · y)       ∎

  ind-r : (d : R-sgn) (se : S-edge)
        → ((y : PSL2Z) → (s (η se)) · y ＝ s ((η se) · y))
        → (y : PSL2Z) → (s (θ step d se)) · y ＝ s ((θ step d se) · y)
  ind-r d se ih y = refl

·-r-left : (x y : PSL2Z) → (r x) · y ＝ r (x · y)
·-r-left = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (y : PSL2Z) → (r E) · y ＝ r (E · y)
  base-E y = refl

  base-S : (y : PSL2Z) → (r S) · y ＝ r (S · y)
  base-S y = refl

  ind-s : (re : R-edge)
        → ((y : PSL2Z) → (r (θ re)) · y ＝ r ((θ re) · y))
        → (y : PSL2Z) → (r (s∙ re)) · y ＝ r ((s∙ re) · y)
  ind-s re ih y = refl

  ind-r : (d : R-sgn) (se : S-edge)
        → ((y : PSL2Z) → (r (η se)) · y ＝ r ((η se) · y))
        → (y : PSL2Z) → (r (θ step d se)) · y ＝ r ((θ step d se) · y)
  ind-r cw  e₀ ih y = refl
  ind-r cw  e₁ ih y = refl
  ind-r cw  (cross re) ih y = refl
  ind-r ccw e₀ ih y = r³ y ⁻¹
  ind-r ccw e₁ ih y = r³ (s y) ⁻¹
  ind-r ccw (cross re) ih y = r³ (s ((θ re) · y)) ⁻¹

·-r²-left : (x y : PSL2Z) → (r² x) · y ＝ r² (x · y)
·-r²-left x y =
 (r² x) · y       ＝⟨ ·-r-left (r x) y ⟩
 r ((r x) · y)    ＝⟨ ap r (·-r-left x y) ⟩
 r² (x · y)       ∎

·-E-right : (x : PSL2Z) → x · E ＝ x
·-E-right = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : E · E ＝ E
  base-E = refl

  base-S : S · E ＝ S
  base-S = refl

  ind-s : (re : R-edge) → (θ re) · E ＝ θ re → (s∙ re) · E ＝ s∙ re
  ind-s re p = ·-s-left (θ re) E ∙ ap s p

  ind-r : (d : R-sgn) (se : S-edge)
        → (η se) · E ＝ η se → (ρ d se) · E ＝ ρ d se
  ind-r cw se p =
   (r∙ se) · E       ＝⟨ ap (_· E) (r-η se ⁻¹) ⟩
   (r (η se)) · E    ＝⟨ ·-r-left (η se) E ⟩
   r ((η se) · E)    ＝⟨ ap r p ⟩
   r (η se)          ＝⟨ r-η se ⟩
   r∙ se             ∎
  ind-r ccw se p =
   (r²∙ se) · E      ＝⟨ ap (_· E) (r²-η se ⁻¹) ⟩
   (r² (η se)) · E   ＝⟨ ·-r²-left (η se) E ⟩
   r² ((η se) · E)   ＝⟨ ap r² p ⟩
   r² (η se)         ＝⟨ r²-η se ⟩
   r²∙ se            ∎

·-assoc : (x y z : PSL2Z) → (x · y) · z ＝ x · (y · z)
·-assoc = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (y z : PSL2Z) → (E · y) · z ＝ E · (y · z)
  base-E y z = refl

  base-S : (y z : PSL2Z) → (S · y) · z ＝ S · (y · z)
  base-S y z = ·-s-left y z

  ind-s : (re : R-edge)
        → ((y z : PSL2Z) → ((θ re) · y) · z ＝ (θ re) · (y · z))
        → (y z : PSL2Z) → ((s∙ re) · y) · z ＝ (s∙ re) · (y · z)
  ind-s re ih y z =
   ((s∙ re) · y) · z          ＝⟨ ap (_· z) (·-s-left (θ re) y) ⟩
   (s ((θ re) · y)) · z       ＝⟨ ·-s-left ((θ re) · y) z ⟩
   s (((θ re) · y) · z)       ＝⟨ ap s (ih y z) ⟩
   s ((θ re) · (y · z))       ＝⟨ ·-s-left (θ re) (y · z) ⁻¹ ⟩
   (s∙ re) · (y · z)          ∎

  ind-r : (d : R-sgn) (se : S-edge)
        → ((y z : PSL2Z) → ((η se) · y) · z ＝ (η se) · (y · z))
        → (y z : PSL2Z) → ((ρ d se) · y) · z ＝ (ρ d se) · (y · z)
  ind-r cw se ih y z =
   ((r∙ se) · y) · z          ＝⟨ ap (λ x → (x · y) · z) (r-η se ⁻¹) ⟩
   ((r (η se)) · y) · z       ＝⟨ ap (_· z) (·-r-left (η se) y) ⟩
   (r ((η se) · y)) · z       ＝⟨ ·-r-left ((η se) · y) z ⟩
   r (((η se) · y) · z)       ＝⟨ ap r (ih y z) ⟩
   r ((η se) · (y · z))       ＝⟨ ·-r-left (η se) (y · z) ⁻¹ ⟩
   (r (η se)) · (y · z)       ＝⟨ ap (_· (y · z)) (r-η se) ⟩
   (r∙ se) · (y · z)          ∎
  ind-r ccw se ih y z =
   ((r²∙ se) · y) · z         ＝⟨ ap (λ x → (x · y) · z) (r²-η se ⁻¹) ⟩
   ((r² (η se)) · y) · z      ＝⟨ ap (_· z) (·-r²-left (η se) y) ⟩
   (r² ((η se) · y)) · z      ＝⟨ ·-r²-left ((η se) · y) z ⟩
   r² (((η se) · y) · z)      ＝⟨ ap r² (ih y z) ⟩
   r² ((η se) · (y · z))      ＝⟨ ·-r²-left (η se) (y · z) ⁻¹ ⟩
   (r² (η se)) · (y · z)      ＝⟨ ap (_· (y · z)) (r²-η se) ⟩
   (r²∙ se) · (y · z)         ∎

\end{code}
