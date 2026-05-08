Lane Biocini
21 January 2026

PSL2Z packaged as a Group in the sense of Groups.Type. This module
collects the group-theoretic characterizations: 𝓜 denotes PSL(2,ℤ)
as a group, and we establish:

  - The standard presentation relations S² = E and R³ = E
  - twist : 𝓜 ≅ 𝓜 (the outer automorphism)
  - transpose : 𝓜 ≅ 𝓜ᵒᵖ (opposite group isomorphism)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Groups.ModularGroup.Group where

open import MLTT.Spartan
open import UF.Equiv
open import Groups.Type hiding (inv) renaming (_≅_ to _≣_)
open import Groups.Opposite
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Properties
open import Groups.ModularGroup.Multiplication

open import Groups.ModularGroup.Inverse
open import Groups.ModularGroup.Twist
open import Groups.ModularGroup.Transposition

PSL2Z-group-axioms : group-axioms PSL2Z _·_
PSL2Z-group-axioms = PSL2Z-is-set
                   , ·-assoc
                   , E
                   , (λ _ → refl)
                   , ·-E-right
                   , λ x → inv x
                         , ·-inv-left x
                         , ·-inv-right x

𝓜 : Group 𝓤₀
𝓜 = PSL2Z , (_·_ , PSL2Z-group-axioms)

\end{code}

The generators S and R satisfy the standard presentation relations.

\begin{code}

S-order-2 : S · S ＝ E
S-order-2 = s² E

R-order-3 : R · (R · R) ＝ E
R-order-3 = r³ E

R²-·-R : R² · R ＝ E
R²-·-R = ·-assoc R R R ∙ R-order-3

R-·-R² : R · R² ＝ E
R-·-R² = R-order-3

\end{code}

Twist is an automorphism of 𝓜 (swaps r ↔ r²).

\begin{code}

twist-is-equiv : is-equiv twist
twist-is-equiv = involutions-are-equivs twist twist-involute

twist-auto : 𝓜 ≣ 𝓜
twist-auto = twist , twist-is-equiv , (λ {x} {y} → twist-product x y)

\end{code}

Transposition gives an isomorphism to the opposite group.

\begin{code}

transpose-is-op-hom : is-hom 𝓜 (𝓜 ᵒᵖ) _ᵀ
transpose-is-op-hom {x} {y} = transpose-product x y

transpose-is-equiv : is-equiv _ᵀ
transpose-is-equiv = involutions-are-equivs _ᵀ transpose-involutive

transpose-op-iso : 𝓜 ≣ 𝓜 ᵒᵖ
transpose-op-iso =
 _ᵀ , transpose-is-equiv , (λ {x} {y} → transpose-is-op-hom {x} {y})

\end{code}
