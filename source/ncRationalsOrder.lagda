Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalNumbers-Properties --Type Topology
open import OrderNotation
open import UF-Base --TypeTopology
open import UF-Subsingletons --TypeTopology

open import IntegersAbs
open import IntegersAddition renaming (_+_ to _ℤ+_)
open import IntegersB
open import IntegersMultiplication renaming (_*_ to _ℤ*_)
open import IntegersOrder 
open import MoreNaturalProperties
open import NaturalsAddition renaming (_+_ to _ℕ+_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import ncRationals
open import ncRationalsOperations

_ℚₙ≤_ _ℚₙ≥_ : ℚₙ → ℚₙ → 𝓤₀ ̇
(x , a) ℚₙ≤ (y , b) = (x ℤ* pos (succ b)) ≤ (y ℤ* pos (succ a))
p ℚₙ≥ q = q ℚₙ≤ p

ℚₙ≤-is-prop : (p q : ℚₙ) → is-prop (p ℚₙ≤ q)
ℚₙ≤-is-prop (x , a) (y , b) = ℤ≤-is-prop (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

_ℚₙ<_ _ℚₙ>_ : ℚₙ → ℚₙ → 𝓤₀ ̇
(x , a) ℚₙ< (y , b) = (x ℤ* pos (succ b)) < (y ℤ* pos (succ a))
p ℚₙ> q = q ℚₙ< p

ℚₙ<-coarser-than-≤ : (p q : ℚₙ) → p ℚₙ< q → p ℚₙ≤ q
ℚₙ<-coarser-than-≤ (x , a) (y , b) l = <-is-≤ (x ℤ* pos (succ b)) (y ℤ* pos (succ a)) l

ℚₙ<-is-prop : (p q : ℚₙ) → is-prop (p ℚₙ< q)
ℚₙ<-is-prop (x , a) (y , b) = ℤ<-is-prop (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

ℚₙ<-trans : (p q r : ℚₙ) → p ℚₙ< q → q ℚₙ< r → p ℚₙ< r
ℚₙ<-trans (x , a) (y , b) (z , c) α β = ordering-right-cancellable (x ℤ* c') (z ℤ* a') b' ⋆ I
 where
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)
  
  I : x ℤ* c' ℤ* b' < z ℤ* a' ℤ* b'
  I = ℤ<-trans ((x ℤ* c') ℤ* b') ((y ℤ* a') ℤ* c') ((z ℤ* a') ℤ* b') i ii
   where
    i : x ℤ* c' ℤ* b' < y ℤ* a' ℤ* c'
    i = transport (_< ((y ℤ* a') ℤ* c')) ϕ θ
     where
      ϕ : x ℤ* b' ℤ* c' ≡ x ℤ* c' ℤ* b'
      ϕ = ℤ-mult-rearrangement x b' c'

      θ : x ℤ* b' ℤ* c' < y ℤ* a' ℤ* c'
      θ = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') c' ⋆ α
    ii : y ℤ* a' ℤ* c' < z ℤ* a' ℤ* b'
    ii = transport₂ _<_ γ₁ γ₂ γ₃
     where
      γ₁ : y ℤ* c' ℤ* a' ≡ y ℤ* a' ℤ* c'
      γ₁ = ℤ-mult-rearrangement y c' a'

      γ₂ : z ℤ* b' ℤ* a' ≡ z ℤ* a' ℤ* b'
      γ₂ = ℤ-mult-rearrangement z b' a'

      γ₃ : y ℤ* c' ℤ* a' < z ℤ* b' ℤ* a'
      γ₃ = positive-multiplication-preserves-order (y ℤ* c') (z ℤ* b') a' ⋆ β

ℚₙ<-addition-preserves-order : (p q r : ℚₙ) → p ℚₙ< q → (p + r) ℚₙ< (q + r)
ℚₙ<-addition-preserves-order (x , a) (y , b) (z , c) (n , e) = pred (succ c ℕ* succ c ℕ* succ n) , III
 where
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)
  n' = pos (succ n)

  I : ¬ (succ c ℕ* succ c ℕ* succ n ≡ 0)
  I α = positive-not-zero n (mult-left-cancellable (succ n) 0 c ii)
   where
    i : succ c ℕ* (succ c ℕ* succ n) ≡ succ c ℕ* (succ c ℕ* 0)
    i = succ c ℕ* (succ c ℕ* succ n) ≡⟨ mult-associativity (succ c) (succ c) (succ n) ⁻¹ ⟩
        succ c ℕ* succ c ℕ* succ n   ≡⟨ α ⟩
        0                            ≡⟨ zero-right-is-zero (succ c) ⁻¹ ⟩
        succ c ℕ* 0                  ≡⟨ ap (succ c ℕ*_) (zero-right-is-zero (succ c) ⁻¹) ⟩
        succ c ℕ* (succ c ℕ* 0)      ∎
    ii : succ c ℕ* succ n ≡ succ c ℕ* 0
    ii = mult-left-cancellable (succ c ℕ* succ n) (succ c ℕ* 0) c i
  
  II : succℤ (pos (pred (succ c ℕ* succ c ℕ* succ n))) ≡ c' ℤ* c' ℤ* n' 
  II = succℤ (pos (pred (succ c ℕ* succ c ℕ* succ n))) ≡⟨ by-definition ⟩
      pos (succ (pred (succ c ℕ* succ c ℕ* succ n)))  ≡⟨ ap pos (succ-pred' (succ c ℕ* succ c ℕ* succ n) I)⟩
      pos (succ c ℕ* succ c ℕ* succ n)                ≡⟨ pos-multiplication-equiv-to-ℕ (succ c ℕ* succ c) (succ n) ⁻¹ ⟩
      pos (succ c ℕ* succ c) ℤ* pos (succ n)          ≡⟨ ap (_ℤ* pos (succ n)) (pos-multiplication-equiv-to-ℕ (succ c) (succ c) ⁻¹) ⟩
      pos (succ c) ℤ* pos (succ c) ℤ* pos (succ n)    ≡⟨ by-definition ⟩
      c' ℤ* c' ℤ* n' ∎
      
  III : succℤ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c)))) ℤ+ pos (pred (succ c ℕ* succ c ℕ* succ n)) ≡ (y ℤ* c' ℤ+ z ℤ* b') ℤ* pos (succ (pred (succ a ℕ* succ c)))
  III = succℤ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c)))) ℤ+ pos (pred (succ c ℕ* succ c ℕ* succ n)) ≡⟨ ℤ-left-succ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c)))) (pos (pred (succ c ℕ* succ c ℕ* succ n))) ⟩
      succℤ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ pos (pred (succ c ℕ* succ c ℕ* succ n))) ≡⟨ ℤ-right-succ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c)))) (pos (pred (succ c ℕ* succ c ℕ* succ n))) ⁻¹ ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ succℤ (pos (pred (succ c ℕ* succ c ℕ* succ n))) ≡⟨ ap ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+_) II ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ c' ℤ* c' ℤ* n'            ≡⟨ ap (λ - → ((x ℤ* c' ℤ+ z ℤ* a') ℤ* -) ℤ+  c' ℤ* c' ℤ* n') (denom-setup b c ) ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n'                                      ≡⟨ ap (λ - → - ℤ+ c' ℤ* c' ℤ* n') (distributivity-mult-over-ℤ (x ℤ* c') (z ℤ* a') (b' ℤ* c')) ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n'                          ≡⟨ ℤ+-assoc ( x ℤ* c' ℤ* (b' ℤ* c')) (z ℤ* a' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n' ) ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ (z ℤ* a' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n')                        ≡⟨ ap (x ℤ* c' ℤ* (b' ℤ* c') ℤ+_) (ℤ+-comm (z ℤ* a' ℤ* (b' ℤ* c')) ( c' ℤ* c' ℤ* n')) ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ (c' ℤ* c' ℤ* n' ℤ+ z ℤ* a' ℤ* (b' ℤ* c'))                        ≡⟨ ℤ+-assoc (x ℤ* c' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n') (z ℤ* a' ℤ* (b' ℤ* c')) ⁻¹ ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                          ≡⟨ ap₂ (λ α β → α ℤ+ β ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-mult-rearrangement x c' (b' ℤ* c')) (ℤ*-comm (c' ℤ* c') n') ⟩
      x ℤ* (b' ℤ* c') ℤ* c' ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                        ≡⟨ ap (λ - → - ℤ* c'  ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ*-assoc x b' c' ⁻¹) ⟩
      x ℤ* b' ℤ* c' ℤ* c' ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                          ≡⟨ ap (λ - → - ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ*-assoc (x ℤ* b') c' c') ⟩
      x ℤ* b' ℤ* (c' ℤ* c') ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                        ≡⟨ ap (λ - → - ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (distributivity-mult-over-ℤ ( x ℤ* b') n' (c' ℤ* c') ⁻¹) ⟩
      (x ℤ* b' ℤ+ n') ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                    ≡⟨ ap (λ - → - ℤ+ z ℤ* a' ℤ* (b' ℤ* c') ) (ℤ*-assoc ((x ℤ* b' ℤ+ n')) c' c' ⁻¹) ⟩
      (x ℤ* b' ℤ+ n') ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                      ≡⟨ ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-right-succ (x ℤ* b') (pos n)) ⟩
      (succℤ (x ℤ* b' ℤ+ pos n)) ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                           ≡⟨ ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-left-succ (x ℤ* b') (pos n) ⁻¹) ⟩
      (succℤ (x ℤ* b') ℤ+ pos n) ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                           ≡⟨ ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) e ⟩
      y ℤ* a' ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                              ≡⟨ ap₂ (λ α β → α ℤ* c' ℤ+ β) (ℤ-mult-rearrangement y a' c') (ℤ*-assoc z a' (b' ℤ* c')) ⟩
      y ℤ* c' ℤ* a' ℤ* c' ℤ+ z ℤ* (a' ℤ* (b' ℤ* c'))                                            ≡⟨ ap₂ (λ α β → α ℤ+ z ℤ* β) (ℤ*-assoc (y ℤ* c') a' c') (ℤ-mult-rearrangement''' a' b' c') ⟩
      y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* (b' ℤ* (a' ℤ* c'))                                          ≡⟨ ap (λ - → y ℤ* c' ℤ* (a' ℤ* c') ℤ+ -) (ℤ*-assoc z b' (a' ℤ* c') ⁻¹) ⟩
      y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                                            ≡⟨ distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') (a' ℤ* c') ⁻¹ ⟩
      (y ℤ* c' ℤ+ z ℤ* b') ℤ* (pos (succ a) ℤ* pos (succ c))                                    ≡⟨ ap (λ - → (y ℤ* c' ℤ+ z ℤ* b') ℤ* -) (denom-setup a c ⁻¹)  ⟩
      (y ℤ* c' ℤ+ z ℤ* b') ℤ* pos (succ (pred (succ a ℕ* succ c)))                              ∎

ℚₙ<-adding : (p q r s : ℚₙ) → p ℚₙ< q → r ℚₙ< s → p + r ℚₙ< q + s
ℚₙ<-adding p q r s l₁ l₂ = ℚₙ<-trans (p + r) (q + r) (q + s) I III
 where
  I : (p + r) ℚₙ< (q + r)
  I = ℚₙ<-addition-preserves-order p q r l₁ 

  II : (r + q) ℚₙ< (s + q)
  II = ℚₙ<-addition-preserves-order r s q l₂

  III : (q + r) ℚₙ< (q + s)
  III = transport₂ _ℚₙ<_ (ℚₙ+-comm r q) (ℚₙ+-comm s q) II

ℚₙ<-adding-zero : (p q : ℚₙ) → (pos 0 , 0) ℚₙ< p → (pos 0 , 0) ℚₙ< q → (pos 0 , 0) ℚₙ< (p + q)
ℚₙ<-adding-zero p q l₁ l₂ = ℚₙ<-adding (pos 0 , 0) p (pos 0 , 0) q l₁ l₂

ℚₙ-pos-multiplication-preserves-order : (p q : ℚₙ) → (pos 0 , 0) ℚₙ< p → (pos 0 , 0) ℚₙ< q → (pos 0 , 0) ℚₙ< (p * q)
ℚₙ-pos-multiplication-preserves-order (x , a) (y , b) (n₁ , e₁) (n₂ , e₂) = pred (succ n₁ ℕ* succ n₂) , I
 where
  α : pos (succ n₁) ≡ x
  α = pos (succ n₁)                                 ≡⟨ ℤ-zero-left-neutral (pos (succ n₁)) ⁻¹ ⟩
      pos 0 ℤ+ pos (succ n₁)                        ≡⟨ by-definition ⟩
      pos 0 ℤ+ succℤ (pos n₁)                       ≡⟨ ℤ-right-succ (pos 0) (pos n₁)  ⟩
      succℤ (pos 0 ℤ+ pos n₁)                       ≡⟨ ℤ-left-succ (pos 0) (pos n₁) ⁻¹ ⟩
      succℤ (pos 0) ℤ+ pos n₁                       ≡⟨ ap (λ - → succℤ - ℤ+ pos n₁) (ℤ-zero-left-is-zero (pos (succ a)) ⁻¹) ⟩
      succℤ (pos 0 ℤ* pos (succ a)) ℤ+ pos n₁       ≡⟨ e₁ ⟩
      x ∎

  β : pos (succ n₂) ≡ y
  β = pos (succ n₂)                           ≡⟨ ℤ-zero-left-neutral (pos (succ n₂)) ⁻¹ ⟩
      pos 0 ℤ+ pos (succ n₂)                  ≡⟨ by-definition ⟩
      pos 0 ℤ+ succℤ (pos n₂)                 ≡⟨ ℤ-right-succ (pos 0) (pos n₂) ⟩
      succℤ (pos 0 ℤ+ pos n₂)                 ≡⟨ ℤ-left-succ (pos 0) (pos n₂) ⁻¹ ⟩
      succℤ (pos 0) ℤ+ pos n₂                 ≡⟨ ap (λ - → succℤ - ℤ+ pos n₂) (ℤ-zero-left-is-zero (pos (succ b)) ⁻¹) ⟩
      succℤ (pos 0 ℤ* pos (succ b)) ℤ+ pos n₂ ≡⟨ e₂ ⟩
      y ∎
  
  I : succℤ (pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b)))) ℤ+ pos (pred (succ n₁ ℕ* succ n₂)) ≡ x ℤ* y ℤ* pos 1
  I = succℤ (pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b)))) ℤ+ pos (pred (succ n₁ ℕ* succ n₂)) ≡⟨ ap (λ - → succℤ - ℤ+  pos (pred (succ n₁ ℕ* succ n₂))) (ℤ-zero-left-is-zero (pos (succ (pred (succ a ℕ* succ b))))) ⟩
      succℤ (pos 0) ℤ+ pos (pred (succ n₁ ℕ* succ n₂)) ≡⟨ ℤ-left-succ (pos 0) (pos (pred (succ n₁ ℕ* succ n₂))) ⟩
      succℤ (pos 0 ℤ+ pos (pred (succ n₁ ℕ* succ n₂))) ≡⟨ ap succℤ (ℤ-zero-left-neutral (pos (pred (succ n₁ ℕ* succ n₂)))) ⟩
      succℤ (pos (pred (succ n₁ ℕ* succ n₂)))          ≡⟨ by-definition ⟩ 
      pos (succ (pred (succ n₁ ℕ* succ n₂)))           ≡⟨ ap pos (succ-pred' (succ n₁ ℕ* succ n₂) (ℕ-positive-multiplication-not-zero n₁ n₂)) ⟩
      pos (succ n₁ ℕ* succ n₂)                         ≡⟨ pos-multiplication-equiv-to-ℕ (succ n₁) (succ n₂) ⁻¹ ⟩
      pos (succ n₁) ℤ* pos (succ n₂)                   ≡⟨ ap₂ _ℤ*_ α β ⟩
      x ℤ* y                                           ≡⟨ ℤ-mult-right-id (x ℤ* y) ⟩
      x ℤ* y ℤ* pos 1 ∎

ℚₙ≤-pos-multiplication-preserves-order : (p q : ℚₙ) → (pos 0 , 0) ℚₙ≤ p → (pos 0 , 0) ℚₙ≤ q → (pos 0 , 0) ℚₙ≤ (p * q)
ℚₙ≤-pos-multiplication-preserves-order (x , a) (y , b) (n₁ , e₁) (n₂ , e₂) = n₁ ℕ* n₂ , I
 where
  I : pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ pos (n₁ ℕ* n₂) ≡ x ℤ* y ℤ* pos 1
  I = pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ pos (n₁ ℕ* n₂)        ≡⟨ ap₂ _ℤ+_ (ℤ-zero-left-is-zero (pos (succ (pred (succ a ℕ* succ b))))) (pos-multiplication-equiv-to-ℕ n₁ n₂ ⁻¹) ⟩
      pos 0 ℤ+ pos n₁ ℤ* pos n₂                                              ≡⟨ ℤ-zero-left-neutral (pos n₁ ℤ* pos n₂) ⟩
      pos n₁ ℤ* pos n₂                                                       ≡⟨ ap₂ _ℤ*_ (ℤ-zero-left-neutral (pos n₁) ⁻¹) (ℤ-zero-left-neutral (pos n₂) ⁻¹) ⟩
      (pos 0 ℤ+ pos n₁) ℤ* (pos 0 ℤ+ pos n₂) ≡⟨ ap₂ _ℤ*_ (ap (_ℤ+ pos n₁) (ℤ-zero-left-is-zero (pos (succ a)) ⁻¹ )) (ap (_ℤ+ pos n₂) (ℤ-zero-left-is-zero (pos (succ b)) ⁻¹)) ⟩
      (pos 0 ℤ* pos (succ a) ℤ+ pos n₁) ℤ* (pos 0 ℤ* pos (succ b) ℤ+ pos n₂) ≡⟨ ap₂ _ℤ*_ e₁ e₂ ⟩
      x ℤ* pos 1 ℤ* (y ℤ* pos 1)                                             ≡⟨ ap (_ℤ* (y ℤ* pos 1)) (ℤ-mult-right-id x) ⟩
      x ℤ* (y ℤ* pos 1)                                                      ≡⟨ ℤ*-assoc x y (pos 1) ⟩
      x ℤ* y ℤ* pos 1 ∎

0ℚₙ≤1 : (pos 0 , 0) ℚₙ≤ (pos 1 , 0)
0ℚₙ≤1 = 1 , refl

1ℚₙ≤1 : (pos 1 , 0) ℚₙ≤ (pos 1 , 0)
1ℚₙ≤1 = 0 , refl

2/3ℚₙ≤1 : (pos 2 , 2) ℚₙ≤ (pos 1 , 0)
2/3ℚₙ≤1 = 1 , refl

negative-not-greater-than-zero : (x a : ℕ) → ¬ ((pos 0 , 0) ℚₙ<( negsucc x , a)) 
negative-not-greater-than-zero x a (n , l) = neg-not-positive (I ⁻¹)
 where
  I : pos (succ n) ≡ negsucc x ℤ* pos 1
  I = pos (succ n) ≡⟨ ℤ-zero-left-neutral (pos (succ n)) ⁻¹ ⟩
      pos 0 ℤ+ pos (succ n) ≡⟨ ap (_ℤ+ pos (succ n)) (ℤ-zero-left-is-zero (pos (succ a)) ⁻¹) ⟩
      pos 0 ℤ* pos (succ a) ℤ+ pos (succ n) ≡⟨ ℤ-right-succ (pos 0 ℤ* pos (succ a)) (pos n) ⟩
      succℤ (pos 0 ℤ* pos (succ a) ℤ+ pos n) ≡⟨ ℤ-left-succ (pos 0 ℤ* pos (succ a)) (pos n) ⁻¹ ⟩
      succℤ (pos 0 ℤ* pos (succ a)) ℤ+ pos n ≡⟨ l ⟩
      negsucc x ℤ* pos 1 ∎




