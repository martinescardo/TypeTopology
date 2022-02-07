Andrew Sneap - 27th April 2021

I link to this module within the Integers section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (_+_) --TypeTopology

open import NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology
open import NaturalsOrder --TypeTopology
open import OrderNotation --TypeTopology
open import UF-Base --TypeTopology
open import UF-Subsingletons --TypeTopology

open import IntegersB
open import IntegersAddition
open import IntegersNegation

open import IntegersDivision
open import IntegersMultiplication
open import IntegersAbs
open import NaturalsDivision renaming (_∣_ to _ℕ∣_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_) 
open import HCF

module IntegersHCF where

ℤ-is-common-divisor : (d x y : ℤ) → 𝓤₀ ̇
ℤ-is-common-divisor d x y = (d ∣ x) × (d ∣ y)

ℤ-is-common-divisor-is-prop : (d x y : ℤ) → not-zero d → is-prop (ℤ-is-common-divisor d x y)
ℤ-is-common-divisor-is-prop d x y nz p q = ×-is-prop ((d ℤ∣ x -is-prop) nz) ((d ℤ∣ y -is-prop) nz) p q

ℤ-is-hcf : (d : ℕ) → (x y : ℤ) → 𝓤₀ ̇
ℤ-is-hcf d x y = ℤ-is-common-divisor (pos d) x y × ((f : ℕ) → ℤ-is-common-divisor (pos f) x y → pos f ∣ pos d)

ℤ-HCF : (a b : ℕ) → Σ h ꞉ ℕ , (is-hcf h a b) × (Σ (x , y) ꞉ ℤ × ℤ , (pos h ≡ ((pos a) * x) + ((pos b) * y)))
ℤ-HCF = course-of-values-induction (λ a → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos a * x + pos b * y)) step 
 where
  step : (n : ℕ)
       → (((a : ℕ) → a < n → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos a * x + pos b * y)))
       → (b : ℕ)
       → Σ h ꞉ ℕ , is-hcf h n b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos n * x + pos b * y)
  step 0 IH b = b , (((0 , refl) , 1 , refl) , (λ x → pr₂)) , ((pos 0) , pos 1) , ℤ+-comm (pos b) (pos 0)
  step (succ n) IH b = I (division b n)
   where
    I : (Σ q ꞉ ℕ , Σ r ꞉ ℕ , (b ≡ q ℕ* succ n ℕ+ r) × (r < succ n))
      → Σ h ꞉ ℕ , is-hcf h (succ n) b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos (succ n) * x + pos b * y)
    I (q , r , e₀ , l) = II (IH r l (succ n)) 
     where
      II : Σ h ꞉ ℕ , is-hcf h r (succ n) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos r * x + pos (succ n) * y)
         → Σ h ꞉ ℕ , is-hcf h (succ n) b × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ pos (succ n) * x + pos b * y)
      II (h , (((α , αₚ) , β , βₚ) , γ) , (x , y) , e₁) = h , ((((β , βₚ) , i) , ii) , iii)
       where
        i : h ℕ∣ b
        i = (q ℕ* β ℕ+ α) , e₂
         where
          e₂ : h ℕ* (q ℕ* β ℕ+ α) ≡ b
          e₂ = h ℕ* (q ℕ* β ℕ+ α)       ≡⟨ distributivity-mult-over-nat h (q ℕ* β) α      ⟩ 
               h ℕ* (q ℕ* β) ℕ+ h ℕ* α ≡⟨ ap (λ z → h ℕ* (q ℕ* β) ℕ+ z) αₚ                 ⟩
               h ℕ* (q ℕ* β) ℕ+ r      ≡⟨ ap (_ℕ+ r) (mult-associativity h q β) ⁻¹       ⟩
               h ℕ* q ℕ* β ℕ+ r        ≡⟨ ap (λ z → z ℕ* β ℕ+ r) (mult-commutativity h q) ⟩
               q ℕ* h ℕ* β ℕ+ r        ≡⟨ ap (_ℕ+ r) (mult-associativity q h β)          ⟩
               q ℕ* (h ℕ* β) ℕ+ r      ≡⟨ ap (λ z → q ℕ* z ℕ+ r) βₚ                       ⟩
               q ℕ* succ n ℕ+ r        ≡⟨ e₀ ⁻¹ ⟩
               b                        ∎

        ii : (f : ℕ) → is-common-divisor f (succ n) b → f ℕ∣ h
        ii f ((μ , μₚ) , ν , νₚ) = γ f ((hcflemma f ν (q ℕ* μ) r e₃) , μ , μₚ)
         where
          e₃ : f ℕ* ν ≡ f ℕ* (q ℕ* μ) ℕ+ r
          e₃ = f ℕ* ν              ≡⟨ νₚ                                             ⟩
               b                   ≡⟨ e₀                                             ⟩
               q ℕ* succ n ℕ+ r   ≡⟨ ap (λ z → q ℕ* z ℕ+ r) (μₚ ⁻¹)                  ⟩
               q ℕ* (f ℕ* μ) ℕ+ r ≡⟨ ap (_ℕ+ r) (mult-associativity q f μ ⁻¹)       ⟩
               q ℕ* f ℕ* μ ℕ+ r   ≡⟨ ap (λ z → z ℕ* μ ℕ+ r) (mult-commutativity q f) ⟩
               f ℕ* q ℕ* μ ℕ+ r   ≡⟨ ap (_ℕ+ r ) (mult-associativity f q μ)         ⟩
               f ℕ* (q ℕ* μ) ℕ+ r ∎

        iii : Σ (x' , y') ꞉ ℤ × ℤ , pos h ≡ pos (succ n) * x' + pos b * y'
        iii = (y + (- pos q * x) , x) , e₄
         where
          e₅ : pos b ≡ pos q * pos (succ n) + (pos r)
          e₅ = pos b ≡⟨ ap pos e₀ ⟩
               pos (q ℕ* succ n ℕ+ r)     ≡⟨ pos-addition-equiv-to-ℕ (q ℕ* (succ n)) r ⁻¹ ⟩
               pos (q ℕ* succ n) + pos r  ≡⟨ ap (_+ pos r) (pos-multiplication-equiv-to-ℕ q (succ n)) ⁻¹ ⟩
               pos q * pos (succ n) + pos r ∎
               
          e₄ : pos h ≡ pos (succ n) * (y + (- pos q * x)) + pos b * x
          e₄ = pos h                                                                          ≡⟨ e₁ ⟩
               pos r * x + pos (succ n) * y                                                   ≡⟨ ℤ+-comm (pos r * x) (pos (succ n) * y) ⟩
               pos (succ n) * y + pos r * x                                                   ≡⟨ refl ⟩
               pos (succ n) * (y + pos 0) + pos r * x                                         ≡⟨ ap (λ z → pos (succ n) * (y + z) + pos r * x) (ℤ-sum-of-inverse-is-zero (pos q * x) ⁻¹) ⟩
               pos (succ n) * (y + (pos q * x + (- pos q * x))) + pos r * x                   ≡⟨ ap (λ z → pos (succ n) * (y + z) + pos r * x) (ℤ+-comm (pos q * x) (- pos q * x)) ⟩
               pos (succ n) * (y + ((- pos q * x) + pos q * x)) + pos r * x                   ≡⟨ ap (λ z → pos (succ n) * z + pos r * x) (ℤ+-assoc y (- pos q * x) (pos q * x) ⁻¹) ⟩
               pos (succ n) * (y + (- pos q * x) + (pos q) * x) + pos r * x                   ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x) + z) + pos r * x) (ℤ*-comm (pos q) x) ⟩
               pos (succ n) * (y + (- pos q * x) + x * pos q) + pos r * x                     ≡⟨ ap (_+ pos r * x) (distributivity-mult-over-ℤ' (y + (- pos q * x)) (x * pos q) (pos (succ n))) ⟩
               pos (succ n) * (y + (- pos q * x)) + pos (succ n) * (x * pos q) + pos r * x    ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z + pos r * x ) (ℤ*-comm (pos (succ n)) (x * pos q)) ⟩
               pos (succ n) * (y + (- pos q * x)) + (x * pos q) * pos (succ n) + pos r * x    ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z + pos r * x ) (ℤ*-assoc x (pos q) (pos (succ n))) ⟩ 
               pos (succ n) * (y + (- pos q * x)) + x * (pos q * pos (succ n)) + pos r * x    ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z + pos r * x ) (ℤ*-comm x (pos q * pos (succ n))) ⟩
               pos (succ n) * (y + (- pos q * x)) + (pos q * pos (succ n)) * x + pos r * x    ≡⟨ ℤ+-assoc (pos (succ n) * (y + (- pos q * x))) ((pos q + pos q * pos n) * x) (pos r * x) ⟩
               pos (succ n) * (y + (- pos q * x)) + ((pos q * pos (succ n)) * x + pos r * x)  ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z) (distributivity-mult-over-ℤ (pos q * pos (succ n)) (pos r) x ⁻¹) ⟩
               pos (succ n) * (y + (- pos q * x)) + (pos q * pos (succ n) + pos r) * x        ≡⟨ ap (λ z → pos (succ n) * (y + (- pos q * x)) + z * x) (e₅ ⁻¹) ⟩
               pos (succ n) * (y + (- pos q * x)) + pos b * x ∎

ℤ-HCF' : (a b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b
ℤ-HCF' a b = I (ℤ-HCF a b)
 where
  I : (Σ h ꞉ ℕ , (is-hcf h a b) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ ((pos a) * x) + ((pos b) * y))) → Σ h ꞉ ℕ , is-hcf h a b
  I (h , is-hcf , bezout) = h , is-hcf


coprime-bezout : (a b : ℕ) → coprime a b → Σ (x , y) ꞉ ℤ × ℤ , pos 1 ≡ pos a * x + pos b * y
coprime-bezout a b = I (ℤ-HCF a b)
 where
  I : Σ h ꞉ ℕ , (is-hcf h a b) × (Σ (x , y) ꞉ ℤ × ℤ , pos h ≡ ((pos a) * x) + ((pos b) * y)) → coprime a b → Σ (x , y) ꞉ ℤ × ℤ , pos 1 ≡ pos a * x + pos b * y
  I (h , is-hcf , (x , y) , bezout) h' = (x , y) , (III ⁻¹ ∙ bezout)
   where
    II : h ≡ 1
    II = hcf-unique a b (h , is-hcf) (1 , h')
    
    III : pos h ≡ pos 1
    III = ap pos II

coprime-with-division : (a b c : ℕ) → coprime a b → a ℕ∣ b ℕ* c → a ℕ∣ c
coprime-with-division a b c coprime (α , αₚ) = I (coprime-bezout a b coprime)
 where
  I : Σ (x , y) ꞉ ℤ × ℤ , pos 1 ≡ pos a * x + pos b * y → a ℕ∣ c
  I ((x , y) , e₁) = pos-div-to-nat-div a c IV
   where 
    II : pos a * (x * pos c) + (pos b * pos c) * y ≡ pos c
    II = pos a * (x * pos c) + (pos b * pos c) * y ≡⟨ ap₂ _+_ (ℤ*-assoc (pos a) x (pos c) ⁻¹) (ℤ*-comm (pos b * pos c) y) ⟩
         pos a * x * pos c + y * (pos b * pos c)   ≡⟨ ap (λ - → pos a * x * pos c + -) (ℤ*-assoc y (pos b) (pos c) ⁻¹) ⟩
         pos a * x * pos c + y * pos b * pos c     ≡⟨ distributivity-mult-over-ℤ (pos a * x) (y * pos b) (pos c) ⁻¹ ⟩
         (pos a * x + y * pos b) * pos c           ≡⟨ ap (λ - → (pos a * x + -) * pos c) (ℤ*-comm y (pos b)) ⟩
         (pos a * x + pos b * y) * pos c           ≡⟨ ap (_* pos c) (e₁ ⁻¹) ⟩
         pos 1 * pos c                             ≡⟨ ℤ-mult-left-id (pos c) ⟩
         pos c                                     ∎

    III : pos a ∣ pos a * (x * pos c) + (pos b * pos c) * y
    III = ℤ-∣-respects-addition-of-multiples (pos a) (pos a) (pos b * pos c) (x * pos c) y i ii
     where
      i : pos a ∣ pos a
      i = pos 1 , refl

      ii : pos a ∣ (pos b * pos c)
      ii = pos α , δ
       where
        δ : pos a * pos α ≡ pos b * pos c
        δ = pos a * pos α ≡⟨ pos-multiplication-equiv-to-ℕ a α ⟩
            pos (a ℕ* α)  ≡⟨ ap pos αₚ ⟩
            pos (b ℕ* c)  ≡⟨ pos-multiplication-equiv-to-ℕ b c ⁻¹ ⟩
            pos b * pos c ∎

    IV : pos a ∣ pos c
    IV = transport (pos a ∣_) II III

\end{code}
