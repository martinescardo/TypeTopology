```agda

{-- OPTIONS --allow-unsolved-metas --}

open import MLTT.Spartan hiding (_+_)

open import Naturals.Addition
open import Notation.Order
open import DedekindReals.Integers.Integers
open import DedekindReals.Integers.Addition renaming (_+_ to _ℤ+_ ; _-_ to _ℤ-_)
open import DedekindReals.Integers.Multiplication renaming (_*_ to _ℤ*_)
open import DedekindReals.Integers.Order renaming (max₃ to ℤmax₃ ; min₃ to ℤmin₃)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons
open import UF.Powerset hiding (𝕋)

module Todd.TBRMultiplication
 (pt : propositional-truncations-exist)
 (fe : FunExt)
 (pe : PropExt)
 (sq : set-quotients-exist)
 where

open import Todd.TernaryBoehmReals pt fe pe sq
open import Todd.TBRDyadicReals pt fe pe sq
open import Todd.RationalsDyadic fe 
open import Todd.DyadicReals pe pt fe
open import Todd.TBRFunctions pt fe pe sq
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp

```

Multiplication of Dedekind Reals is defined as in the HoTT book, section 11.2.1.
Notice that this is heavily related to interval multiplication.

```agda

_ℝd*_ : ℝ-d → ℝ-d → ℝ-d
((Lx , Rx) , _) ℝd* ((Ly , Ry) , _) = (Lz , Rz) , {!!}
 where
  Lz Rz : 𝓟 ℤ[1/2]
  Lz p = (∃ (a , b , c , d) ꞉ ℤ[1/2] × ℤ[1/2] × ℤ[1/2] × ℤ[1/2] , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × p < min₄ (a ℤ[1/2]* c) (a ℤ[1/2]* d) (b ℤ[1/2]* c) (b ℤ[1/2]* d)) , ∃-is-prop
  Rz q = (∃ (a , b , c , d) ꞉ ℤ[1/2] × ℤ[1/2] × ℤ[1/2] × ℤ[1/2] , a ∈ Lx × b ∈ Rx × c ∈ Ly × d ∈ Ry × max₄ (a ℤ[1/2]* c) (a ℤ[1/2]* d) (b ℤ[1/2]* c) (b ℤ[1/2]* d) < q) , ∃-is-prop

--Not 100% sure on this one
_T*_ : 𝕋 → 𝕋 → 𝕋
(x , b) T* (y , b') = z , {!!}
 where
  z : ℤ → ℤ
  z q = (upRight ^ (k + abs j)) (x (q ℤ+ pos k) ℤ* y (q ℤ+ pos k))
   where
    k-setup₁ : ℤ
    k-setup₁ = (pos 2 ℤ* x q ℤ+ pos 2 ℤ* y q ℤ+ pos 7) /2'
    k-setup₂ : ℤ
    k-setup₂ = k-setup₁ ℤ- q
    k : ℕ
    k = abs (k-setup₂ ℤ- q) + 2 -- to account for ceillog 2, add extra 1
    l₁ l₂ r₁ r₂ : ℤ
    l₁ = x (q ℤ+ pos k)
    l₂ = l₁ ℤ+ pos 2
    r₁ = y (q ℤ+ pos k)
    r₂ = r₁ ℤ+ pos 2
    j : ℤ
    j = difference _ℤ*_ l₁ r₁

tbr-multiplication-agrees : (x y : 𝕋) → (⟦ x ⟧ ℝd* ⟦ y ⟧) ＝ ⟦ x 𝕋* y ⟧
tbr-multiplication-agrees x y = {!!}

mult-codeℕ : Vec (ℤ × ℕ) 2 → ℤ × ℕ
mult-codeℕ ((a , b) ∷ (c , d) ∷ [])
 = a ℤ* c , b + d

mult-codeℤ : Vec (ℤ × ℤ) 2 → ℤ × ℤ
mult-codeℤ = fun-codeℕ→codeℤ mult-codeℕ

open FunctionCollection

Mult : FunctionCollection 2
F  Mult (x ∷ y ∷ []) = x ℝd* y
F* Mult (x ∷ y ∷ []) = x 𝕋* y
γ  Mult (x ∷ y ∷ []) = tbr-multiplication-agrees x y
I  Mult              = mult-codeℤ
ζ  Mult (x₁ ∷ y₁ ∷ []) (x₂ ∷ y₂ ∷ []) ε = {!!}

```
