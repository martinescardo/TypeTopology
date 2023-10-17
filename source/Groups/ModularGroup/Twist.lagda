Lane Biocini
21 January 2026

The twist automorphism of PSL(2,ℤ): the unique non-trivial element of
Out(PSL(2,ℤ)) ≅ ℤ/2ℤ. Geometrically, it corresponds to complex
conjugation on the upper half-plane action.

Algebraically, twist swaps r ↔ r² while fixing s:
  twist(s x) = s(twist x)
  twist(r x) = r²(twist x)

Unlike the group inverse (which reverses word order), twist preserves
word order but inverts each generator individually. It is involutive
and respects multiplication, making it a group automorphism.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Groups.ModularGroup.Twist where

open import MLTT.Spartan
open import UF.FunExt
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Base
open import Groups.ModularGroup.Properties
open import Groups.ModularGroup.Induction
open import Groups.ModularGroup.Multiplication

twist-η : S-edge → PSL2Z
twist-θ : R-edge → PSL2Z

twist-η e₀         = E
twist-η e₁         = S
twist-η (cross re) = s (twist-θ re)

twist-θ (r+ se) = r² (twist-η se)
twist-θ (r- se) = r (twist-η se)

twist : PSL2Z → PSL2Z
twist (η se) = twist-η se
twist (θ re) = twist-θ re

twist-s : (x : PSL2Z) → twist (s x) ＝ s (twist x)
twist-s (η e₀)    = refl
twist-s (η e₁)    = refl
twist-s (sr∙ se)  = s² (r (r (twist-η se))) ⁻¹
twist-s (sr²∙ se) = s² (r (twist-η se)) ⁻¹
twist-s (r∙ se)   = refl
twist-s (r²∙ se)  = refl

twist-r : (x : PSL2Z) → twist (r x) ＝ r² (twist x)
twist-r (η e₀)    = refl
twist-r (η e₁)    = refl
twist-r (sr∙ se)  = refl
twist-r (sr²∙ se) = refl
twist-r (r∙ se)   = r³ (r (twist-η se)) ⁻¹
twist-r (r²∙ se)  = r³ (twist-η se) ⁻¹

twist-r² : (x : PSL2Z) → twist (r² x) ＝ r (twist x)
twist-r² (η e₀)          = refl
twist-r² (η e₁)          = refl
twist-r² (sr∙ se)        = refl
twist-r² (sr²∙ se)       = refl
twist-r² (r∙ se)         = r³ (twist-η se) ⁻¹
twist-r² (r²∙ e₀)        = refl
twist-r² (r²∙ e₁)        = refl
twist-r² (r²∙ (cross x)) = refl

twist-involute : (x : PSL2Z) → twist (twist x) ＝ x
twist-involute (η e₀)    = refl
twist-involute (η e₁)    = refl
twist-involute (sr∙ se)  =
  twist (s (r² (twist-η se))) ＝⟨ twist-s (r² (twist-η se)) ⟩
  s (twist (r² (twist-η se))) ＝⟨ ap s (twist-r² (twist-η se)) ⟩
  s (r (twist (twist-η se)))  ＝⟨ ap (s ∘ r) (twist-involute (η se)) ⟩
  s (r (η se))                ＝⟨ sr-η se ⟩
  sr∙ se                      ∎
twist-involute (sr²∙ se) =
  twist (twist (sr²∙ se))     ＝⟨ twist-s (r (twist-η se)) ⟩
  s (twist (r (twist-η se)))  ＝⟨ ap s (twist-r (twist-η se)) ⟩
  s (r² (twist (twist-η se))) ＝⟨ ap (s ∘ r²) (twist-involute (η se)) ⟩
  s (r² (η se))               ＝⟨ sr²-η se ⟩
  sr²∙ se                     ∎
twist-involute (r∙ se) =
  twist (r² (twist-η se))     ＝⟨ twist-r² (twist-η se) ⟩
  r (twist (twist-η se))      ＝⟨ ap r (twist-involute (η se)) ⟩
  r (η se)                    ＝⟨ r-η se ⟩
  r∙ se                       ∎
twist-involute (r²∙ se)  =
  twist (twist (r²∙ se))      ＝⟨ twist-r (twist-η se) ⟩
  r² (twist (twist-η se))     ＝⟨ ap r² (twist-involute (η se)) ⟩
  r² (η se)                   ＝⟨ r²-η se ⟩
  r²∙ se                      ∎

twist-product : (x y : PSL2Z) → twist (x · y) ＝ twist x · twist y
twist-product = PSL2Z-ind base-E base-S ind-s ind-r
 where
  base-E : (y : PSL2Z) → twist (E · y) ＝ twist E · twist y
  base-E y = refl

  base-S : (y : PSL2Z) → twist (S · y) ＝ twist S · twist y
  base-S y = twist-s y

  ind-s : (re : R-edge)
        → ((y : PSL2Z) → twist ((θ re) · y) ＝ twist (θ re) · twist y)
        → (y : PSL2Z) → twist ((s∙ re) · y) ＝ twist (s∙ re) · twist y
  ind-s re ih y =
   twist ((s∙ re) · y)            ＝⟨ ap twist (·-s-left (θ re) y) ⟩
   twist (s ((θ re) · y))         ＝⟨ twist-s ((θ re) · y) ⟩
   s (twist ((θ re) · y))         ＝⟨ ap s (ih y) ⟩
   s (twist (θ re) · twist y)     ＝⟨ ·-s-left (twist (θ re)) (twist y) ⁻¹ ⟩
   (s (twist (θ re))) · twist y   ＝⟨ ap (_· twist y) (twist-s (θ re) ⁻¹) ⟩
   twist (s∙ re) · twist y        ∎

  ind-r : (d : R-sgn) (se : S-edge)
        → ((y : PSL2Z) → twist ((η se) · y) ＝ twist (η se) · twist y)
        → (y : PSL2Z) → twist ((ρ d se) · y) ＝ twist (ρ d se) · twist y
  ind-r cw se ih y =
   twist ((r∙ se) · y)            ＝⟨ ap (twist ∘ (_· y)) (r-η se ⁻¹) ⟩
   twist ((r (η se)) · y)         ＝⟨ ap twist (·-r-left (η se) y) ⟩
   twist (r ((η se) · y))         ＝⟨ twist-r ((η se) · y) ⟩
   r² (twist ((η se) · y))        ＝⟨ ap r² (ih y) ⟩
   r² (twist (η se) · twist y)    ＝⟨ ·-r²-left (twist (η se)) (twist y) ⁻¹ ⟩
   (r² (twist (η se))) · twist y  ＝⟨ ap (_· twist y) (twist-r (η se) ⁻¹) ⟩
   twist (r (η se)) · twist y     ＝⟨ ap (_· twist y) (ap twist (r-η se)) ⟩
   twist (r∙ se) · twist y        ∎
  ind-r ccw se ih y =
   twist ((r²∙ se) · y)           ＝⟨ ap (twist ∘ (_· y)) (r²-η se ⁻¹) ⟩
   twist ((r² (η se)) · y)        ＝⟨ ap twist (·-r²-left (η se) y) ⟩
   twist (r² ((η se) · y))        ＝⟨ twist-r² ((η se) · y) ⟩
   r (twist ((η se) · y))         ＝⟨ ap r (ih y) ⟩
   r (twist (η se) · twist y)     ＝⟨ ·-r-left (twist (η se)) (twist y) ⁻¹ ⟩
   (r (twist (η se))) · twist y   ＝⟨ ap (_· twist y) (twist-r² (η se) ⁻¹) ⟩
   twist (r² (η se)) · twist y    ＝⟨ ap (_· twist y) (ap twist (r²-η se)) ⟩
   twist (r²∙ se) · twist y       ∎

module _ (fe : funext 𝓤₀ 𝓤₀) where
 twist-gen-iter : twist ＝ PSL2Z-gen-iter E s r²
 twist-gen-iter = dfunext fe lemma
  where
   iter : PSL2Z → PSL2Z
   iter = PSL2Z-gen-iter E s r²

   lemma : (x : PSL2Z) → twist x ＝ iter x
   lemma =
    PSL2Z-η s r² twist iter refl twist-s PSL2Z-gen-iter-s twist-r
     PSL2Z-gen-iter-r

 twist-iter : twist ＝ PSL2Z-iter E S s r² r
 twist-iter = dfunext fe lemma
  where
   iter : PSL2Z → PSL2Z
   iter = PSL2Z-iter E S s r² r

   lemma-η : (se : S-edge) → twist-η se ＝ iter (η se)
   lemma-θ : (re : R-edge) → twist-θ re ＝ iter (θ re)

   lemma-η e₀         = refl
   lemma-η e₁         = refl
   lemma-η (cross re) = ap s (lemma-θ re)

   lemma-θ (r+ se) = ap r² (lemma-η se)
   lemma-θ (r- se) = ap r (lemma-η se)

   lemma : (x : PSL2Z) → twist x ＝ iter x
   lemma (η se) = lemma-η se
   lemma (θ re) = lemma-θ re

\end{code}
