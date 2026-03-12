Lane Biocini
21 January 2026

Group inverse for PSL2Z. Since s² = 1 and r³ = 1, we have s⁻¹ = s
and r⁻¹ = r². The inverse of an arbitrary element is computed by
reversing its generator sequence and replacing each generator with
its inverse:

  inv(s x) = (inv x) · S
  inv(r x) = (inv x) · R²

The key results are:
  - inv is involutive: inv (inv x) = x
  - Left inverse: (inv x) · x = E
  - Right inverse: x · (inv x) = E
  - Anti-homomorphism: inv (x · y) = inv y · inv x

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Groups.ModularGroup.Inverse where

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Base
open import Groups.ModularGroup.Properties
open import Groups.ModularGroup.Induction
open import Groups.ModularGroup.Multiplication

_·S : PSL2Z → PSL2Z
_·S = PSL2Z-gen-iter S s r

_·R² : PSL2Z → PSL2Z
_·R² = PSL2Z-gen-iter R² s r

_·R : PSL2Z → PSL2Z
_·R = PSL2Z-gen-iter R s r

inv-η : S-edge → PSL2Z
inv-θ : R-edge → PSL2Z

inv-η e₀         = E
inv-η e₁         = S
inv-η (cross re) = (inv-θ re) ·S

inv-θ (r+ se) = (inv-η se) ·R²
inv-θ (r- se) = (inv-η se) ·R

inv : PSL2Z → PSL2Z
inv (η se) = inv-η se
inv (θ re) = inv-θ re

private
  inv-E : inv E ＝ E
  inv-E = refl

  inv-S : inv S ＝ S
  inv-S = refl

  inv-R : inv R ＝ R²
  inv-R = refl

  inv-R² : inv R² ＝ R
  inv-R² = refl

\end{code}

Right-multiplication by generators satisfies involution/cancellation properties.

\begin{code}

·S-·S : (x : PSL2Z) → (x ·S) ·S ＝ x
·S-·S = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (E ·S) ·S ＝ E
  base-E = refl

  base-S : (S ·S) ·S ＝ S
  base-S = refl

  ind-s : (re : R-edge)
        → ((θ re) ·S) ·S ＝ θ re
        → ((s∙ re) ·S) ·S ＝ s∙ re
  ind-s re p =
   ap (_·S) (·-s-left (θ re) S) ∙ ·-s-left ((θ re) ·S) S ∙ ap s p

  ind-r : (d : R-sgn) (se : S-edge)
        → ((η se) ·S) ·S ＝ η se
        → ((ρ d se) ·S) ·S ＝ ρ d se
  ind-r cw se p =
   ((r∙ se) ·S) ·S       ＝⟨ ap (λ x → (x ·S) ·S) (r-η se ⁻¹) ⟩
   ((r (η se)) ·S) ·S    ＝⟨ ap (_·S) (·-r-left (η se) S) ⟩
   (r ((η se) ·S)) ·S    ＝⟨ ·-r-left ((η se) ·S) S ⟩
   r (((η se) ·S) ·S)    ＝⟨ ap r p ⟩
   r (η se)              ＝⟨ r-η se ⟩
   r∙ se                 ∎
  ind-r ccw se p =
   ((r²∙ se) ·S) ·S      ＝⟨ ap (λ x → (x ·S) ·S) (r²-η se ⁻¹) ⟩
   ((r² (η se)) ·S) ·S   ＝⟨ ap (_·S) (·-r²-left (η se) S) ⟩
   (r² ((η se) ·S)) ·S   ＝⟨ ·-r²-left ((η se) ·S) S ⟩
   r² (((η se) ·S) ·S)   ＝⟨ ap r² p ⟩
   r² (η se)             ＝⟨ r²-η se ⟩
   r²∙ se                ∎

·R-·R² : (x : PSL2Z) → (x ·R) ·R² ＝ x
·R-·R² = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (E ·R) ·R² ＝ E
  base-E = r³ E

  base-S : (S ·R) ·R² ＝ S
  base-S = r³ (s E)

  ind-s : (re : R-edge)
        → ((θ re) ·R) ·R² ＝ θ re → ((s∙ re) ·R) ·R² ＝ s∙ re
  ind-s re p =
   ap (_·R²) (·-s-left (θ re) R) ∙ ·-s-left ((θ re) ·R) R² ∙ ap s p

  ind-r : (d : R-sgn) (se : S-edge)
        → ((η se) ·R) ·R² ＝ η se → ((ρ d se) ·R) ·R² ＝ ρ d se
  ind-r cw se p =
   ((r∙ se) ·R) ·R²      ＝⟨ ap (λ x → (x ·R) ·R²) (r-η se ⁻¹) ⟩
   ((r (η se)) ·R) ·R²   ＝⟨ ap (_·R²) (·-r-left (η se) R) ⟩
   (r ((η se) ·R)) ·R²   ＝⟨ ·-r-left ((η se) ·R) R² ⟩
   r (((η se) ·R) ·R²)   ＝⟨ ap r p ⟩
   r (η se)              ＝⟨ r-η se ⟩
   r∙ se                 ∎
  ind-r ccw se p =
   ((r²∙ se) ·R) ·R²     ＝⟨ ap (λ x → (x ·R) ·R²) (r²-η se ⁻¹) ⟩
   ((r² (η se)) ·R) ·R²  ＝⟨ ap (_·R²) (·-r²-left (η se) R) ⟩
   (r² ((η se) ·R)) ·R²  ＝⟨ ·-r²-left ((η se) ·R) R² ⟩
   r² (((η se) ·R) ·R²)  ＝⟨ ap r² p ⟩
   r² (η se)             ＝⟨ r²-η se ⟩
   r²∙ se                ∎

·R²-·R : (x : PSL2Z) → (x ·R²) ·R ＝ x
·R²-·R = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (E ·R²) ·R ＝ E
  base-E = r³ E

  base-S : (S ·R²) ·R ＝ S
  base-S = r³ (s E)

  ind-s : (re : R-edge)
        → ((θ re) ·R²) ·R ＝ θ re → ((s∙ re) ·R²) ·R ＝ s∙ re
  ind-s re p =
   ap (_·R) (·-s-left (θ re) R²) ∙ ·-s-left ((θ re) ·R²) R ∙ ap s p

  ind-r : (d : R-sgn) (se : S-edge)
        → ((η se) ·R²) ·R ＝ η se → ((ρ d se) ·R²) ·R ＝ ρ d se
  ind-r cw se p =
   ((r∙ se) ·R²) ·R      ＝⟨ ap (λ x → (x ·R²) ·R) (r-η se ⁻¹) ⟩
   ((r (η se)) ·R²) ·R   ＝⟨ ap (_·R) (·-r-left (η se) R²) ⟩
   (r ((η se) ·R²)) ·R   ＝⟨ ·-r-left ((η se) ·R²) R ⟩
   r (((η se) ·R²) ·R)   ＝⟨ ap r p ⟩
   r (η se)              ＝⟨ r-η se ⟩
   r∙ se                 ∎
  ind-r ccw se p =
   ((r²∙ se) ·R²) ·R     ＝⟨ ap (λ x → (x ·R²) ·R) (r²-η se ⁻¹) ⟩
   ((r² (η se)) ·R²) ·R  ＝⟨ ap (_·R) (·-r²-left (η se) R²) ⟩
   (r² ((η se) ·R²)) ·R  ＝⟨ ·-r²-left ((η se) ·R²) R ⟩
   r² (((η se) ·R²) ·R)  ＝⟨ ap r² p ⟩
   r² (η se)             ＝⟨ r²-η se ⟩
   r²∙ se                ∎

R²-R²-is-R : R² · R² ＝ R
R²-R²-is-R = ap r (r³ E)

·R²-·R² : (x : PSL2Z) → (x ·R²) ·R² ＝ x ·R
·R²-·R² x = ·-assoc x R² R² ∙ ap (x ·_) R²-R²-is-R

·R-·R : (x : PSL2Z) → (x ·R) ·R ＝ x ·R²
·R-·R x = ·-assoc x R R

\end{code}

Left inverse property: (inv x) · x = E

\begin{code}

·-inv-left-η : (se : S-edge) → (inv-η se) · (η se) ＝ E
·-inv-left-θ : (re : R-edge) → (inv-θ re) · (θ re) ＝ E

·-inv-left-η e₀ = refl  -- E · E = E
·-inv-left-η e₁ = s² E   -- S · S = E
·-inv-left-η (cross re) =
 ((inv-θ re) ·S) · s (θ re)                 ＝⟨ ·-assoc (inv-θ re) S (s (θ re)) ⟩
 (inv-θ re) · (S · s (θ re))                ＝⟨ ap ((inv-θ re) ·_) (s² (θ re)) ⟩
 (inv-θ re) · (θ re)                        ＝⟨ ·-inv-left-θ re ⟩
 E                                          ∎

·-inv-left-θ (r+ se) =
 ((inv-η se) ·R²) · (θ (r+ se))     ＝⟨ ap (((inv-η se) ·R²) ·_) (r-η se ⁻¹) ⟩
 ((inv-η se) ·R²) · r (η se)        ＝⟨ ·-assoc (inv-η se) R² (r (η se)) ⟩
 (inv-η se) · (R² · r (η se))       ＝⟨ I ⟩
 (inv-η se) · ((R² · R) · (η se))   ＝⟨ II ⟩
 (inv-η se) · (η se)                ＝⟨ ·-inv-left-η se ⟩
 E                                  ∎
 where
  I  = ap ((inv-η se) ·_) (·-assoc R² R (η se) ⁻¹)
  II = ap (λ z → (inv-η se) · (z · (η se))) (r³ E)

·-inv-left-θ (r- se) =
 ((inv-η se) ·R) · (θ (r- se))      ＝⟨ ap (((inv-η se) ·R) ·_) (r²-η se ⁻¹) ⟩
 ((inv-η se) ·R) · r² (η se)        ＝⟨ ·-assoc (inv-η se) R (r² (η se)) ⟩
 (inv-η se) · (R · r² (η se))       ＝⟨ I ⟩
 (inv-η se) · ((R · R²) · (η se))   ＝⟨ II ⟩
 (inv-η se) · (η se)                ＝⟨ ·-inv-left-η se ⟩
 E                                  ∎
 where
  I  = ap ((inv-η se) ·_) (·-assoc R R² (η se) ⁻¹)
  II = ap (λ z → (inv-η se) · (z · (η se))) (r³ E)

·-inv-left : (x : PSL2Z) → (inv x) · x ＝ E
·-inv-left (η se) = ·-inv-left-η se
·-inv-left (θ re) = ·-inv-left-θ re

\end{code}

Right inverse property: x · (inv x) = E

\begin{code}

·-inv-right-η : (se : S-edge) → (η se) · (inv-η se) ＝ E
·-inv-right-θ : (re : R-edge) → (θ re) · (inv-θ re) ＝ E

·-inv-right-η e₀ = refl  -- E · E = E
·-inv-right-η e₁ = s² E   -- S · S = E
·-inv-right-η (cross re) =
 s (θ re) · ((inv-θ re) ·S)         ＝⟨ ·-s-left (θ re) ((inv-θ re) ·S) ⟩
 s ((θ re) · ((inv-θ re) ·S))       ＝⟨ ap s (·-assoc (θ re) (inv-θ re) S ⁻¹) ⟩
 s (((θ re) · (inv-θ re)) · S)      ＝⟨ ap (λ z → s (z · S)) (·-inv-right-θ re) ⟩
 E                                  ∎

·-inv-right-θ (r+ se) =
 (θ (r+ se)) · ((inv-η se) ·R²)     ＝⟨ ap (_· ((inv-η se) ·R²)) (r-η se ⁻¹) ⟩
 r (η se) · ((inv-η se) ·R²)        ＝⟨ ·-r-left (η se) ((inv-η se) ·R²) ⟩
 r ((η se) · ((inv-η se) ·R²))      ＝⟨ ap r (·-assoc (η se) (inv-η se) R² ⁻¹) ⟩
 r (((η se) · (inv-η se)) · R²)     ＝⟨ I ⟩
 r R²                               ＝⟨ r-R² ⟩
 E                                  ∎
 where
  I = ap (λ z → r (z · R²)) (·-inv-right-η se)

·-inv-right-θ (r- se) =
 (θ (r- se)) · ((inv-η se) ·R)     ＝⟨ ap (_· ((inv-η se) ·R)) (r²-η se ⁻¹) ⟩
 r² (η se) · ((inv-η se) ·R)       ＝⟨ ·-r²-left (η se) ((inv-η se) ·R) ⟩
 r² ((η se) · ((inv-η se) ·R))     ＝⟨ ap r² (·-assoc (η se) (inv-η se) R ⁻¹) ⟩
 r² (((η se) · (inv-η se)) · R)    ＝⟨ I ⟩
 r² R                              ＝⟨ ap r r-R ∙ r-R² ⟩
 E                                 ∎
 where
  I = ap (λ z → r² (z · R)) (·-inv-right-η se)

·-inv-right : (x : PSL2Z) → x · (inv x) ＝ E
·-inv-right (η se) = ·-inv-right-η se
·-inv-right (θ re) = ·-inv-right-θ re

\end{code}

We prove that inverse is involutive, and that it is antihomomorphic with
respect to right composition with generators to establish the composition
rule of inverses.

\begin{code}

inv-involute : (x : PSL2Z) → inv (inv x) ＝ x
inv-involute x =
 inv (inv x)                      ＝⟨ ·-E-right (inv (inv x)) ⁻¹ ⟩
 (inv (inv x)) · E                ＝⟨ ap ((inv (inv x)) ·_) (·-inv-left x ⁻¹) ⟩
 (inv (inv x)) · ((inv x) · x)    ＝⟨ ·-assoc (inv (inv x)) (inv x) x ⁻¹ ⟩
 ((inv (inv x)) · (inv x)) · x    ＝⟨ ap (_· x) (·-inv-left (inv x)) ⟩
 x                                ∎

inv-s : (x : PSL2Z) → inv (s x) ＝ (inv x) · S
inv-s (η e₀) = refl
inv-s (η e₁) = refl
inv-s (sr∙ se) = ·S-·S (inv-θ (r+ se)) ⁻¹
inv-s (sr²∙ se) = ·S-·S (inv-θ (r- se)) ⁻¹
inv-s (r∙ se) = refl
inv-s (r²∙ se) = refl

inv-r : (x : PSL2Z) → inv (r x) ＝ (inv x) · R²
inv-r (η e₀)    = refl
inv-r (η e₁)    = refl
inv-r (sr∙ se)  = refl
inv-r (sr²∙ se) = refl
inv-r (r∙ se)   = ap inv (r-θ-r+ se) ∙ ·R²-·R² (inv-η se) ⁻¹
inv-r (r²∙ se)  = ap inv (r-θ-r- se) ∙ ·R-·R² (inv-η se) ⁻¹

inv-r² : (x : PSL2Z) → inv (r² x) ＝ (inv x) · R
inv-r² (η e₀)    = refl
inv-r² (η e₁)    = refl
inv-r² (sr∙ se)  = refl
inv-r² (sr²∙ se) = refl
inv-r² (r∙ se)   = ap inv (r²-θ-r+ se) ∙ ·R²-·R (inv-η se) ⁻¹
inv-r² (r²∙ se)  = ap inv (r²-θ-r- se) ∙ ·R-·R (inv-η se) ⁻¹

inv-product : (x y : PSL2Z) → inv (x · y) ＝ (inv y) · (inv x)
inv-product =
 PSL2Z-ind
  {P = λ x → (y : PSL2Z) → inv (x · y) ＝ (inv y) · (inv x)}
  base-E base-S ind-s ind-r
 where
  base-E : (y : PSL2Z) → inv (E · y) ＝ (inv y) · (inv E)
  base-E y = ·-E-right (inv y) ⁻¹

  base-S : (y : PSL2Z) → inv (S · y) ＝ (inv y) · (inv S)
  base-S y = inv-s y

  ind-s : (re : R-edge)
        → ((y : PSL2Z) → inv ((θ re) · y) ＝ (inv y) · (inv (θ re)))
        → (y : PSL2Z) → inv ((s∙ re) · y) ＝ (inv y) · (inv (s∙ re))
  ind-s re ih y =
   inv ((s∙ re) · y)              ＝⟨ ap inv (·-s-left (θ re) y) ⟩
   inv (s ((θ re) · y))           ＝⟨ inv-s ((θ re) · y) ⟩
   (inv ((θ re) · y)) · S         ＝⟨ ap (_· S) (ih y) ⟩
   ((inv y) · (inv (θ re))) · S   ＝⟨ ·-assoc (inv y) (inv (θ re)) S ⟩
   (inv y) · ((inv (θ re)) · S)   ＝⟨ ap ((inv y) ·_) (inv-s (θ re) ⁻¹) ⟩
   (inv y) · (inv (s∙ re))        ∎

  ind-r : (d : R-sgn) (se : S-edge)
        → ((y : PSL2Z) → inv ((η se) · y) ＝ (inv y) · (inv (η se)))
        → (y : PSL2Z) → inv ((ρ d se) · y) ＝ (inv y) · (inv (ρ d se))
  ind-r cw se ih y =
   inv ((r∙ se) · y)              ＝⟨ ap (inv ∘ (_· y)) (r-η se ⁻¹) ⟩
   inv ((r (η se)) · y)           ＝⟨ ap inv (·-r-left (η se) y) ⟩
   inv (r ((η se) · y))           ＝⟨ inv-r ((η se) · y) ⟩
   (inv ((η se) · y)) · R²        ＝⟨ ap (_· R²) (ih y) ⟩
   ((inv y) · (inv (η se))) · R²  ＝⟨ ·-assoc (inv y) (inv (η se)) R² ⟩
   (inv y) · ((inv (η se)) · R²)  ＝⟨ ap ((inv y) ·_) (inv-r (η se) ⁻¹) ⟩
   (inv y) · (inv (r (η se)))     ＝⟨ ap ((inv y) ·_) (ap inv (r-η se)) ⟩
   (inv y) · (inv (r∙ se))        ∎
  ind-r ccw se ih y =
   inv ((r²∙ se) · y)             ＝⟨ ap (inv ∘ (_· y)) (r²-η se ⁻¹) ⟩
   inv ((r² (η se)) · y)          ＝⟨ ap inv (·-r²-left (η se) y) ⟩
   inv (r² ((η se) · y))          ＝⟨ inv-r² ((η se) · y) ⟩
   (inv ((η se) · y)) · R         ＝⟨ ap (_· R) (ih y) ⟩
   ((inv y) · (inv (η se))) · R   ＝⟨ ·-assoc (inv y) (inv (η se)) R ⟩
   (inv y) · ((inv (η se)) · R)   ＝⟨ ap ((inv y) ·_) (inv-r² (η se) ⁻¹) ⟩
   (inv y) · (inv (r² (η se)))    ＝⟨ ap ((inv y) ·_) (ap inv (r²-η se)) ⟩
   (inv y) · (inv (r²∙ se))       ∎

\end{code}
