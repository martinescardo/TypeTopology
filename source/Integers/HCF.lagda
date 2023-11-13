Andrew Sneap, 27 April 2021

This file arises as a result of using an equivalence relation to facilitate
proofs of property of rational numbers. We can prove that two fractions which
are in lowest terms, and satisfy an equivalence relation are equal. This proof
relies on Bezout's lemma, particularly the version of Bezout's lemma which
involves the highest common factor of integers. This files defines such a
highest common factor, and proves the required property.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.Subsingletons
open import Integers.Type
open import Integers.Addition
open import Integers.Negation
open import Integers.Division
open import Integers.Multiplication
open import Integers.Abs
open import Naturals.Division renaming (_∣_ to _ℕ∣_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.HCF

module Integers.HCF where

ℤ-is-common-divisor : (d x y : ℤ) → 𝓤₀ ̇
ℤ-is-common-divisor d x y = (d ∣ x) × (d ∣ y)

ℤ-is-common-divisor-is-prop : (d x y : ℤ)
                            → not-zero d
                            → is-prop (ℤ-is-common-divisor d x y)
ℤ-is-common-divisor-is-prop d x y nz = ×-is-prop γ₁ γ₂
 where
  γ₁ : is-prop (d ∣ x)
  γ₁ = (d ℤ∣ x -is-prop) nz

  γ₂ : is-prop (d ∣ y)
  γ₂ = (d ℤ∣ y -is-prop) nz

ℤ-is-hcf : (d : ℕ) → (x y : ℤ) → 𝓤₀ ̇
ℤ-is-hcf d x y = ℤ-is-common-divisor (pos d) x y
               × ((f : ℕ) → ℤ-is-common-divisor (pos f) x y → pos f ∣ pos d)

ℤ-HCF : (a b : ℕ)
      → Σ h ꞉ ℕ , (is-hcf h a b)
      × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ (pos a) * x + (pos b) * y)
ℤ-HCF = course-of-values-induction
         (λ a → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b
                        × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos a * x + pos b * y))
          step
 where
  step : (n : ℕ)
       → ((a : ℕ) → a < n → (b : ℕ)
        → Σ h ꞉ ℕ , is-hcf h a b
        × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos a * x + pos b * y))
       → (b : ℕ)
       → Σ h ꞉ ℕ , is-hcf h n b
       × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos n * x + pos b * y)
  step 0 IH b = b , hcf-zero-left , (pos 0 , pos 1) , ℤ+-comm (pos b) (pos 0)
  step (succ n) IH b = γ (division b n)
   where
    γ : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (b ＝ q ℕ* succ n ℕ+ r) × (r < succ n)
      → Σ h ꞉ ℕ , is-hcf h (succ n) b
      × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos (succ n) * x + pos b * y)
    γ (q , r , e₀ , l) = γ' (IH r l (succ n))
     where
      γ' : Σ h ꞉ ℕ , is-hcf h r (succ n)
         × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos r * x + pos (succ n) * y)

         → Σ h ꞉ ℕ , is-hcf h (succ n) b
         × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos (succ n) * x + pos b * y)
      γ' (h , (((α , αₚ) , β , βₚ) , γ) , (x , y) , e₁) = γ''
       where
        I-lemma : h ℕ* (q ℕ* β ℕ+ α) ＝ b
        I-lemma = h ℕ* (q ℕ* β ℕ+ α)      ＝⟨ i     ⟩
                  h ℕ* (q ℕ* β) ℕ+ h ℕ* α ＝⟨ ii    ⟩
                  h ℕ* (q ℕ* β) ℕ+ r      ＝⟨ iii   ⟩
                  h ℕ* q ℕ* β ℕ+ r        ＝⟨ iv    ⟩
                  q ℕ* h ℕ* β ℕ+ r        ＝⟨ v     ⟩
                  q ℕ* (h ℕ* β) ℕ+ r      ＝⟨ vi    ⟩
                  q ℕ* succ n ℕ+ r        ＝⟨ e₀ ⁻¹ ⟩
                  b                       ∎
         where
          i   = distributivity-mult-over-addition h (q ℕ* β) α
          ii  = ap (λ z → h ℕ* (q ℕ* β) ℕ+ z) αₚ
          iii = ap (_ℕ+ r) (mult-associativity h q β) ⁻¹
          iv  = ap (λ z → z ℕ* β ℕ+ r) (mult-commutativity h q)
          v   = ap (_ℕ+ r) (mult-associativity q h β)
          vi  = ap (λ z → q ℕ* z ℕ+ r) βₚ

        I : h ℕ∣ b
        I = (q ℕ* β ℕ+ α) , I-lemma

        II : (f : ℕ) → is-common-divisor f (succ n) b → f ℕ∣ h
        II f ((μ , μₚ) , ν , νₚ) = γ f (ψ₁ , ψ₂)
         where
          ψ : f ℕ* ν ＝ f ℕ* (q ℕ* μ) ℕ+ r
          ψ = f ℕ* ν             ＝⟨ νₚ  ⟩
              b                  ＝⟨ e₀  ⟩
              q ℕ* succ n ℕ+ r   ＝⟨ i   ⟩
              q ℕ* (f ℕ* μ) ℕ+ r ＝⟨ ii  ⟩
              q ℕ* f ℕ* μ ℕ+ r   ＝⟨ iii ⟩
              f ℕ* q ℕ* μ ℕ+ r   ＝⟨ iv  ⟩
              f ℕ* (q ℕ* μ) ℕ+ r ∎
           where
            i   = ap (λ z → q ℕ* z ℕ+ r) (μₚ ⁻¹)
            ii  = ap (_ℕ+ r) (mult-associativity q f μ ⁻¹)
            iii = ap (λ z → z ℕ* μ ℕ+ r) (mult-commutativity q f)
            iv  = ap (_ℕ+ r ) (mult-associativity f q μ)

          ψ₁ : f ℕ∣ r
          ψ₁ = factor-of-sum-consequence f ν (q ℕ* μ) r ψ

          ψ₂ : f ℕ∣ succ n
          ψ₂ = μ , μₚ

        III : Σ (x' , y') ꞉ ℤ × ℤ , pos h ＝ pos (succ n) * x' + pos b * y'
        III = (y + (- pos q * x) , x) , V
         where
          n' = pos (succ n)
          q' = pos q
          r' = pos r

          IV : pos b ＝ q' * n' + r'
          IV = pos b                  ＝⟨ ap pos e₀ ⟩
               pos (q ℕ* succ n ℕ+ r) ＝⟨ i         ⟩
               pos (q ℕ* succ n) + r' ＝⟨ ii        ⟩
               q' * n' + r'           ∎
           where
            i = distributivity-pos-addition (q ℕ* (succ n)) r ⁻¹
            ii = ap (_+ r') (pos-multiplication-equiv-to-ℕ q (succ n)) ⁻¹

          V : pos h ＝ n' * (y + (- q' * x)) + pos b * x
          V = pos h                                            ＝⟨ e₁   ⟩
              r' * x + n' * y                                  ＝⟨ i    ⟩
              n' * y + r' * x                                  ＝⟨ refl ⟩
              n' * (y + pos 0) + r' * x                        ＝⟨ ii   ⟩
              n' * (y + (q' * x + (- q' * x))) + r' * x        ＝⟨ iii  ⟩
              n' * (y + ((- q' * x) + q' * x)) + r' * x        ＝⟨ iv   ⟩
              n' * (y + (- q' * x) + q' * x) + r' * x          ＝⟨ v    ⟩
              n' * (y + (- q' * x) + x * q') + r' * x          ＝⟨ vi   ⟩
              n' * (y + (- q' * x)) + n' * (x * q') + r' * x   ＝⟨ vii  ⟩
              n' * (y + (- q' * x)) + (x * q') * n' + r' * x   ＝⟨ viii ⟩
              n' * (y + (- q' * x)) + x * (q' * n') + r' * x   ＝⟨ ix   ⟩
              n' * (y + (- q' * x)) + (q' * n') * x + r' * x   ＝⟨ xi   ⟩
              n' * (y + (- q' * x)) + ((q' * n') * x + r' * x) ＝⟨ xii  ⟩
              n' * (y + (- q' * x)) + (q' * n' + r') * x       ＝⟨ xiii ⟩
              n' * (y + (- q' * x)) + pos b * x                ∎
           where
            iiₐₚ : pos 0 ＝ q' * x + (- q' * x)
            iiₐₚ = ℤ-sum-of-inverse-is-zero (q' * x) ⁻¹
            iiiₐₚ : q' * x - q' * x ＝ (- q' * x) + q' * x
            iiiₐₚ = ℤ+-comm (q' * x) (- q' * x)
            ivₐₚ : y + ((- q' * x) + q' * x) ＝ y - q' * x + q' * x
            ivₐₚ = ℤ+-assoc y (- q' * x) (q' * x) ⁻¹
            vₐₚ : q' * x ＝ x * q'
            vₐₚ = ℤ*-comm q' x
            viₐₚ : n' * (y - q' * x + x * q') ＝ n' * (y - q' * x) + n' * (x * q')
            viₐₚ = distributivity-mult-over-ℤ' (y + (- q' * x)) (x * q') n'
            viiₐₚ : n' * (x * q') ＝ x * q' * n'
            viiₐₚ = ℤ*-comm n' (x * q')
            viiiₐₚ : x * q' * n' ＝ x * (q' * n')
            viiiₐₚ = ℤ*-assoc x q' n'
            ixₐₚ : x * (q' * n') ＝ q' * n' * x
            ixₐₚ = ℤ*-comm x (q' * n')
            xiiₐₚ : q' * n' * x + r' * x ＝ (q' * n' + r') * x
            xiiₐₚ = distributivity-mult-over-ℤ (q' * n') r' x ⁻¹

            i    = ℤ+-comm (r' * x) (n' * y)
            ii   = ap (λ z → n' * (y + z) + r' * x) iiₐₚ
            iii  = ap (λ z → n' * (y + z) + r' * x) iiiₐₚ
            iv   = ap (λ z → n' * z + r' * x) ivₐₚ
            v    = ap (λ z → n' * (y + (- q' * x) + z) + r' * x) vₐₚ
            vi   = ap (_+ r' * x) viₐₚ
            vii  = ap (λ z → n' * (y + (- q' * x)) + z + r' * x ) viiₐₚ
            viii = ap (λ z → n' * (y + (- q' * x)) + z + r' * x ) viiiₐₚ
            ix   = ap (λ z → n' * (y + (- q' * x)) + z + r' * x ) ixₐₚ
            xi   = ℤ+-assoc (n' * (y + (- q' * x))) (q' * n' * x) (r' * x)
            xii  = ap (λ z → n' * (y + (- q' * x)) + z) xiiₐₚ
            xiii = ap (λ z → n' * (y + (- q' * x)) + z * x) (IV ⁻¹)

        γ'' : Σ h ꞉ ℕ , is-hcf h (succ n) b
            × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ pos (succ n) * x + pos b * y)
        γ'' = h , (((β , βₚ) , I) , II) , III

ℤ-HCF' : (a b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b
ℤ-HCF' a b = I (ℤ-HCF a b)
 where
  I : Σ h ꞉ ℕ , is-hcf h a b
    × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ (pos a) * x + (pos b) * y)
    → Σ h ꞉ ℕ , is-hcf h a b
  I (h , is-hcf , _) = h , is-hcf

coprime-bezout : (a b : ℕ)
               → coprime a b
               → Σ (x , y) ꞉ ℤ × ℤ , pos 1 ＝ pos a * x + pos b * y
coprime-bezout a b = I (ℤ-HCF a b)
 where
  I : Σ h ꞉ ℕ , (is-hcf h a b)
    × (Σ (x , y) ꞉ ℤ × ℤ , pos h ＝ (pos a) * x + (pos b) * y)
    → coprime a b
    → Σ (x , y) ꞉ ℤ × ℤ , pos 1 ＝ pos a * x + pos b * y
  I (h , is-hcf , (x , y) , α) h' = (x , y) , (III ⁻¹ ∙ α)
   where
    II : h ＝ 1
    II = hcf-unique a b (h , is-hcf) (1 , h')

    III : pos h ＝ pos 1
    III = ap pos II

coprime-with-division : (a b c : ℕ) → coprime a b → a ℕ∣ b ℕ* c → a ℕ∣ c
coprime-with-division a b c coprime (α , αₚ) = I (coprime-bezout a b coprime)
 where
  a' = pos a
  b' = pos b
  c' = pos c

  I : Σ (x , y) ꞉ ℤ × ℤ , pos 1 ＝ a' * x + b' * y → a ℕ∣ c
  I ((x , y) , e₁) = pos-div-to-nat-div a c IV
   where
    II : a' * (x * c') + (b' * c') * y ＝ c'
    II = a' * (x * c') + (b' * c') * y ＝⟨ i   ⟩
         a' * x * c' + y * (b' * c')   ＝⟨ ii  ⟩
         a' * x * c' + y * b' * c'     ＝⟨ iii ⟩
         (a' * x + y * b') * c'        ＝⟨ iv  ⟩
         (a' * x + b' * y) * c'        ＝⟨ v   ⟩
         pos 1 * c'                    ＝⟨ vi  ⟩
         c'                            ∎
     where
      i   = ap₂ _+_ (ℤ*-assoc a' x c' ⁻¹) (ℤ*-comm (b' * c') y)
      ii  = ap (λ - → a' * x * c' + -) (ℤ*-assoc y b' c' ⁻¹)
      iii = distributivity-mult-over-ℤ (a' * x) (y * b') c' ⁻¹
      iv  = ap (λ - → (a' * x + -) * c') (ℤ*-comm y b')
      v   = ap (_* c') (e₁ ⁻¹)
      vi  = ℤ-mult-left-id c'

    III : a' ∣ a' * (x * c') + (b' * c') * y
    III = ℤ-∣-respects-addition-of-multiples a' a' (b' * c') (x * c') y i ii
     where
      i : a' ∣ a'
      i = pos 1 , refl

      ii : a' ∣ (b' * c')
      ii = pos α , δ
       where
        δ : a' * pos α ＝ b' * c'
        δ = a' * pos α    ＝⟨ pos-multiplication-equiv-to-ℕ a α    ⟩
            pos (a ℕ* α)  ＝⟨ ap pos αₚ                            ⟩
            pos (b ℕ* c)  ＝⟨ pos-multiplication-equiv-to-ℕ b c ⁻¹ ⟩
            b' * c' ∎

    IV : a' ∣ c'
    IV = transport (a' ∣_) II III

\end{code}
