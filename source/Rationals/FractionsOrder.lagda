Andrew Sneap, November 2021

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Properties
open import Notation.Order
open import UF.Base
open import UF.Subsingletons

open import Integers.Abs
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Type
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Rationals.Fractions
open import Rationals.FractionsOperations

module Rationals.FractionsOrder where

_𝔽≤_ _𝔽≥_ : 𝔽 → 𝔽 → 𝓤₀ ̇
(x , a) 𝔽≤ (y , b) = x ℤ* pos (succ b) ≤ y ℤ* pos (succ a)
p 𝔽≥ q = q 𝔽≤ p

𝔽≤-is-prop : (p q : 𝔽) → is-prop (p 𝔽≤ q)
𝔽≤-is-prop (x , a) (y , b) = ℤ≤-is-prop (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

_𝔽<_ _𝔽>_ : 𝔽 → 𝔽 → 𝓤₀ ̇
(x , a) 𝔽< (y , b) = x ℤ* pos (succ b) < y ℤ* pos (succ a)
p 𝔽> q = q 𝔽< p

𝔽<-coarser-than-≤ : (p q : 𝔽) → p 𝔽< q → p 𝔽≤ q
𝔽<-coarser-than-≤ (x , a) (y , b) l = γ
 where
  γ : (x , a) 𝔽≤ (y , b)
  γ = <-is-≤ (x ℤ* pos (succ b)) (y ℤ* pos (succ a)) l

𝔽<-is-prop : (p q : 𝔽) → is-prop (p 𝔽< q)
𝔽<-is-prop (x , a) (y , b) = ℤ<-is-prop (x ℤ* pos (succ b)) (y ℤ* pos (succ a))

𝔽<-trans : (p q r : 𝔽) → p 𝔽< q → q 𝔽< r → p 𝔽< r
𝔽<-trans (x , a) (y , b) (z , c) α β = γ
 where
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  I : x ℤ* c' ℤ* b' < z ℤ* a' ℤ* b'
  I = ℤ<-trans (x ℤ* c' ℤ* b') (y ℤ* a' ℤ* c') (z ℤ* a' ℤ* b') i ii
   where
    i : x ℤ* c' ℤ* b' < y ℤ* a' ℤ* c'
    i = transport (_< y ℤ* a' ℤ* c') ϕ θ
     where
      ϕ : x ℤ* b' ℤ* c' ＝ x ℤ* c' ℤ* b'
      ϕ = ℤ-mult-rearrangement x b' c'

      θ : x ℤ* b' ℤ* c' < y ℤ* a' ℤ* c'
      θ = positive-multiplication-preserves-order (x ℤ* b') (y ℤ* a') c' ⋆ α

    ii : y ℤ* a' ℤ* c' < z ℤ* a' ℤ* b'
    ii = transport₂ _<_ γ₁ γ₂ γ₃
     where
      γ₁ : y ℤ* c' ℤ* a' ＝ y ℤ* a' ℤ* c'
      γ₁ = ℤ-mult-rearrangement y c' a'

      γ₂ : z ℤ* b' ℤ* a' ＝ z ℤ* a' ℤ* b'
      γ₂ = ℤ-mult-rearrangement z b' a'

      γ₃ : y ℤ* c' ℤ* a' < z ℤ* b' ℤ* a'
      γ₃ = positive-multiplication-preserves-order (y ℤ* c') (z ℤ* b') a' ⋆ β

  γ : x ℤ* c' < z ℤ* a'
  γ = ordering-right-cancellable (x ℤ* c') (z ℤ* a') b' ⋆ I

𝔽<-addition-preserves-order : (p q r : 𝔽) → p 𝔽< q → p + r 𝔽< q + r
𝔽<-addition-preserves-order (x , a) (y , b) (z , c) (n , e)
 = pred (succ c ℕ* succ c ℕ* succ n) , III
 where
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)
  n' = pos (succ n)

  sa = succ a
  sb = succ b
  sn = succ n
  sc = succ c

  I : ¬ (sc ℕ* sc ℕ* sn ＝ 0)
  I α = positive-not-zero n (mult-left-cancellable sn 0 c ii)
   where
    i : sc ℕ* (sc ℕ* sn) ＝ sc ℕ* (sc ℕ* 0)
    i = sc ℕ* (sc ℕ* sn) ＝⟨ mult-associativity sc sc sn ⁻¹      ⟩
        sc ℕ* sc ℕ* sn   ＝⟨ α                                   ⟩
        0                ＝⟨ zero-right-base sc ⁻¹               ⟩
        sc ℕ* 0          ＝⟨ ap (sc ℕ*_) (zero-right-base sc ⁻¹) ⟩
        sc ℕ* (sc ℕ* 0)  ∎

    ii : sc ℕ* sn ＝ sc ℕ* 0
    ii = mult-left-cancellable (sc ℕ* sn) (sc ℕ* 0) c i

  II : succℤ (pos (pred (sc ℕ* sc ℕ* sn))) ＝ c' ℤ* c' ℤ* n'
  II = succℤ (pos (pred (sc ℕ* sc ℕ* sn))) ＝⟨ refl ⟩
      pos (succ (pred (sc ℕ* sc ℕ* sn)))   ＝⟨ i    ⟩
      pos (sc ℕ* sc ℕ* sn)                 ＝⟨ ii   ⟩
      pos (sc ℕ* sc) ℤ* pos sn             ＝⟨ iii  ⟩
      pos (sc) ℤ* pos (sc) ℤ* pos sn       ＝⟨ refl ⟩
      c' ℤ* c' ℤ* n'                       ∎
   where
    i   = ap pos (succ-pred' (sc ℕ* sc ℕ* sn) I)
    ii  = pos-multiplication-equiv-to-ℕ (sc ℕ* sc) sn ⁻¹
    iii = ap (_ℤ* pos sn) (pos-multiplication-equiv-to-ℕ sc sc ⁻¹)

  III : succℤ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc)))) ℤ+ pos (pred (sc ℕ* sc ℕ* sn))
      ＝ (y ℤ* c' ℤ+ z ℤ* b') ℤ* pos (succ (pred (sa ℕ* sc)))
  III = succℤ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc)))) ℤ+ pos (pred (sc ℕ* sc ℕ* sn)) ＝⟨ i     ⟩
      succℤ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc))) ℤ+ pos (pred (sc ℕ* sc ℕ* sn)))   ＝⟨ ii    ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc))) ℤ+ succℤ (pos (pred (sc ℕ* sc ℕ* sn)))   ＝⟨ iii   ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc))) ℤ+ c' ℤ* c' ℤ* n'                        ＝⟨ iv    ⟩
      (x ℤ* c' ℤ+ z ℤ* a') ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n'                                          ＝⟨ v     ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n'                              ＝⟨ vi    ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ (z ℤ* a' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n')                            ＝⟨ vii   ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ (c' ℤ* c' ℤ* n' ℤ+ z ℤ* a' ℤ* (b' ℤ* c'))                            ＝⟨ viii  ⟩
      x ℤ* c' ℤ* (b' ℤ* c') ℤ+ c' ℤ* c' ℤ* n' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                              ＝⟨ ix    ⟩
      x ℤ* (b' ℤ* c') ℤ* c' ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                            ＝⟨ xi    ⟩
      x ℤ* b' ℤ* c' ℤ* c' ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                              ＝⟨ xii   ⟩
      x ℤ* b' ℤ* (c' ℤ* c') ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                            ＝⟨ xiii  ⟩
      (x ℤ* b' ℤ+ n') ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                        ＝⟨ xiv   ⟩
      (x ℤ* b' ℤ+ n') ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                          ＝⟨ xv    ⟩
      (succℤ (x ℤ* b' ℤ+ pos n)) ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                               ＝⟨ xvi   ⟩
      (succℤ (x ℤ* b') ℤ+ pos n) ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                               ＝⟨ xvii  ⟩
      y ℤ* a' ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                                                  ＝⟨ xviii ⟩
      y ℤ* c' ℤ* a' ℤ* c' ℤ+ z ℤ* (a' ℤ* (b' ℤ* c'))                                                ＝⟨ xix   ⟩
      y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* (b' ℤ* (a' ℤ* c'))                                              ＝⟨ xx    ⟩
      y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                                                ＝⟨ xxi   ⟩
      (y ℤ* c' ℤ+ z ℤ* b') ℤ* (pos (sa) ℤ* pos (sc))                                                ＝⟨ xxii  ⟩
      (y ℤ* c' ℤ+ z ℤ* b') ℤ* pos (succ (pred (sa ℕ* sc)))                                          ∎
   where
    i     = ℤ-left-succ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc)))) (pos (pred (sc ℕ* sc ℕ* sn)))
    ii    = ℤ-right-succ ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc)))) (pos (pred (sc ℕ* sc ℕ* sn))) ⁻¹
    iii   = ap ((x ℤ* c' ℤ+ z ℤ* a') ℤ* pos (succ (pred (sb ℕ* sc))) ℤ+_) II
    iv    = ap (λ - → ((x ℤ* c' ℤ+ z ℤ* a') ℤ* -) ℤ+  c' ℤ* c' ℤ* n') (denom-setup b c)
    v     = ap (λ - → - ℤ+ c' ℤ* c' ℤ* n') (distributivity-mult-over-ℤ (x ℤ* c') (z ℤ* a') (b' ℤ* c'))
    vi    = ℤ+-assoc ( x ℤ* c' ℤ* (b' ℤ* c')) (z ℤ* a' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n')
    vii   = ap (x ℤ* c' ℤ* (b' ℤ* c') ℤ+_) (ℤ+-comm (z ℤ* a' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n'))
    viii  = ℤ+-assoc (x ℤ* c' ℤ* (b' ℤ* c')) (c' ℤ* c' ℤ* n') (z ℤ* a' ℤ* (b' ℤ* c')) ⁻¹
    ix    = ap₂ (λ α β → α ℤ+ β ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-mult-rearrangement x c' (b' ℤ* c')) (ℤ*-comm (c' ℤ* c') n')
    xi    = ap (λ - → - ℤ* c'  ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ*-assoc x b' c' ⁻¹)
    xii   = ap (λ - → - ℤ+ n' ℤ* (c' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ*-assoc (x ℤ* b') c' c')
    xiii  = ap (λ - → - ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (distributivity-mult-over-ℤ ( x ℤ* b') n' (c' ℤ* c') ⁻¹)
    xiv   = ap (λ - → - ℤ+ z ℤ* a' ℤ* (b' ℤ* c') ) (ℤ*-assoc ((x ℤ* b' ℤ+ n')) c' c' ⁻¹)
    xv    = ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-right-succ (x ℤ* b') (pos n))
    xvi   = ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) (ℤ-left-succ (x ℤ* b') (pos n) ⁻¹)
    xvii  = ap (λ - → - ℤ* c' ℤ* c' ℤ+ z ℤ* a' ℤ* (b' ℤ* c')) e
    xviii = ap₂ (λ α β → α ℤ* c' ℤ+ β) (ℤ-mult-rearrangement y a' c') (ℤ*-assoc z a' (b' ℤ* c'))
    xix   = ap₂ (λ α β → α ℤ+ z ℤ* β) (ℤ*-assoc (y ℤ* c') a' c') (ℤ-mult-rearrangement''' a' b' c')
    xx    = ap (λ - → y ℤ* c' ℤ* (a' ℤ* c') ℤ+ -) (ℤ*-assoc z b' (a' ℤ* c') ⁻¹)
    xxi   = distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') (a' ℤ* c') ⁻¹
    xxii  = ap (λ - → (y ℤ* c' ℤ+ z ℤ* b') ℤ* -) (denom-setup a c ⁻¹)

𝔽<-adding : (p q r s : 𝔽) → p 𝔽< q → r 𝔽< s → p + r 𝔽< q + s
𝔽<-adding p q r s l₁ l₂ = 𝔽<-trans (p + r) (q + r) (q + s) I III
 where
  I : (p + r) 𝔽< (q + r)
  I = 𝔽<-addition-preserves-order p q r l₁

  II : (r + q) 𝔽< (s + q)
  II = 𝔽<-addition-preserves-order r s q l₂

  III : (q + r) 𝔽< (q + s)
  III = transport₂ _𝔽<_ (𝔽+-comm r q) (𝔽+-comm s q) II

𝔽<-adding-zero : (p q : 𝔽)
               → (pos 0 , 0) 𝔽< p
               → (pos 0 , 0) 𝔽< q
               → (pos 0 , 0) 𝔽< (p + q)
𝔽<-adding-zero p q l₁ l₂ = 𝔽<-adding (pos 0 , 0) p (pos 0 , 0) q l₁ l₂

𝔽-pos-multiplication-preserves-order : (p q : 𝔽)
                                     → (pos 0 , 0) 𝔽< p
                                     → (pos 0 , 0) 𝔽< q
                                     → (pos 0 , 0) 𝔽< (p * q)
𝔽-pos-multiplication-preserves-order (x , a) (y , b) (c , e₁) (d , e₂)
 = pred (succ c ℕ* succ d) , I
 where
  α : pos (succ c) ＝ x
  α = pos (succ c)                            ＝⟨ i    ⟩
      pos 0 ℤ+ pos (succ c)                   ＝⟨ refl ⟩
      pos 0 ℤ+ succℤ (pos c)                  ＝⟨ ii   ⟩
      succℤ (pos 0 ℤ+ pos c)                  ＝⟨ iii  ⟩
      succℤ (pos 0) ℤ+ pos c                  ＝⟨ iv   ⟩
      succℤ (pos 0 ℤ* pos (succ a)) ℤ+ pos c  ＝⟨ e₁   ⟩
      x                                       ∎
   where
    i   = ℤ-zero-left-neutral (pos (succ c)) ⁻¹
    ii  = ℤ-right-succ (pos 0) (pos c)
    iii = ℤ-left-succ (pos 0) (pos c) ⁻¹
    iv  = ap (λ - → succℤ - ℤ+ pos c) (ℤ-zero-left-base (pos (succ a)) ⁻¹)

  β : pos (succ d) ＝ y
  β = pos (succ d)                           ＝⟨ i    ⟩
      pos 0 ℤ+ pos (succ d)                  ＝⟨ refl ⟩
      pos 0 ℤ+ succℤ (pos d)                 ＝⟨ ii   ⟩
      succℤ (pos 0 ℤ+ pos d)                 ＝⟨ iii  ⟩
      succℤ (pos 0) ℤ+ pos d                 ＝⟨ iv   ⟩
      succℤ (pos 0 ℤ* pos (succ b)) ℤ+ pos d ＝⟨ e₂   ⟩
      y                                      ∎
   where
    i   = ℤ-zero-left-neutral (pos (succ d)) ⁻¹
    ii  = ℤ-right-succ (pos 0) (pos d)
    iii = ℤ-left-succ (pos 0) (pos d) ⁻¹
    iv  = ap (λ - → succℤ - ℤ+ pos d) (ℤ-zero-left-base (pos (succ b)) ⁻¹)

  I : succℤ (pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))))
       ℤ+ pos (pred (succ c ℕ* succ d))
    ＝ x ℤ* y ℤ* pos 1
  I = succℤ (pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))))
       ℤ+ pos (pred (succ c ℕ* succ d))                     ＝⟨ i    ⟩
      succℤ (pos 0) ℤ+ pos (pred (succ c ℕ* succ d))        ＝⟨ ii   ⟩
      succℤ (pos 0 ℤ+ pos (pred (succ c ℕ* succ d)))        ＝⟨ iii  ⟩
      succℤ (pos (pred (succ c ℕ* succ d)))                 ＝⟨ refl ⟩
      pos (succ (pred (succ c ℕ* succ d)))                  ＝⟨ iv   ⟩
      pos (succ c ℕ* succ d)                                ＝⟨ v    ⟩
      pos (succ c) ℤ* pos (succ d)                          ＝⟨ vi   ⟩
      x ℤ* y                                                ＝⟨ vii  ⟩
      x ℤ* y ℤ* pos 1                                       ∎
    where
     iₐₚ : pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))) ＝ pos 0
     iₐₚ = ℤ-zero-left-base (pos (succ (pred (succ a ℕ* succ b))))
     ivₐₚ : ¬ (succ c ℕ* succ d ＝ 0)
     ivₐₚ = ℕ-positive-multiplication-not-zero c d

     i   = ap (λ - → succℤ - ℤ+  pos (pred (succ c ℕ* succ d))) iₐₚ
     ii  = ℤ-left-succ (pos 0) (pos (pred (succ c ℕ* succ d)))
     iii = ap succℤ (ℤ-zero-left-neutral (pos (pred (succ c ℕ* succ d))))
     iv  = ap pos (succ-pred' (succ c ℕ* succ d) ivₐₚ)
     v   = pos-multiplication-equiv-to-ℕ (succ c) (succ d) ⁻¹
     vi  = ap₂ _ℤ*_ α β
     vii = ℤ-mult-right-id (x ℤ* y)

𝔽≤-pos-multiplication-preserves-order : (p q : 𝔽)
                                      → (pos 0 , 0) 𝔽≤ p
                                      → (pos 0 , 0) 𝔽≤ q
                                      → (pos 0 , 0) 𝔽≤ (p * q)
𝔽≤-pos-multiplication-preserves-order (x , a) (y , b) (c , e₁) (d , e₂)
 = c ℕ* d , I
 where
  a' = pos (succ a)
  c' = pos c
  d' = pos d

  I : pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ pos (c ℕ* d)
    ＝ x ℤ* y ℤ* pos 1
  I = pos 0 ℤ* pos (succ (pred (succ a ℕ* succ b))) ℤ+ pos (c ℕ* d) ＝⟨ i    ⟩
      pos 0 ℤ+ pos (c ℕ* d)                                         ＝⟨ ii   ⟩
      pos 0 ℤ+ c' ℤ* d'                                             ＝⟨ iii  ⟩
      c' ℤ* d'                                                      ＝⟨ iv   ⟩
      (pos 0 ℤ+ c') ℤ* d'                                           ＝⟨ v    ⟩
      (pos 0 ℤ+ c') ℤ* (pos 0 ℤ+ d')                                ＝⟨ vi   ⟩
      (pos 0 ℤ* a' ℤ+ c') ℤ* (pos 0 ℤ+ d')                          ＝⟨ vii  ⟩
      (pos 0 ℤ* a' ℤ+ c') ℤ* (pos 0 ℤ* pos (succ b) ℤ+ d')          ＝⟨ viii ⟩
      x ℤ* pos 1 ℤ* (y ℤ* pos 1)                                    ＝⟨ ix   ⟩
      x ℤ* y ℤ* pos 1                                               ∎
       where
        iₐₚ = ℤ-zero-left-base (pos (succ (pred (succ a ℕ* succ b))))
        viiiₐₚ = ℤ-zero-left-base (pos (succ b)) ⁻¹

        i    = ap (_ℤ+ pos (c ℕ* d)) iₐₚ
        ii   = ap (pos 0 ℤ+_) (pos-multiplication-equiv-to-ℕ c d ⁻¹)
        iii  = ℤ-zero-left-neutral (c' ℤ* d')
        iv   = ap (_ℤ* d') (ℤ-zero-left-neutral c' ⁻¹)
        v    = ap ((pos 0 ℤ+ c') ℤ*_) (ℤ-zero-left-neutral d' ⁻¹)
        vi   = ap (λ z → (z ℤ+ c') ℤ* (pos 0 ℤ+ d')) (ℤ-zero-left-base a' ⁻¹)
        vii  = ap (λ z → (pos 0 ℤ* a' ℤ+ c') ℤ* (z ℤ+ d')) viiiₐₚ
        viii = ap₂ _ℤ*_ e₁ e₂
        ix   = ap (_ℤ* (y ℤ* pos 1)) (ℤ-mult-right-id x ⁻¹)

0𝔽≤1 : (pos 0 , 0) 𝔽≤ (pos 1 , 0)
0𝔽≤1 = 1 , refl

1𝔽≤1 : (pos 1 , 0) 𝔽≤ (pos 1 , 0)
1𝔽≤1 = 0 , refl

2/3𝔽≤1 : (pos 2 , 2) 𝔽≤ (pos 1 , 0)
2/3𝔽≤1 = 1 , refl

negative-not-greater-than-zero : (x a : ℕ) → ¬ ((pos 0 , 0) 𝔽< (negsucc x , a))
negative-not-greater-than-zero x a (n , l) = negsucc-not-pos γ
 where
  γ : negsucc x ℤ* pos 1 ＝ pos (succ n)
  γ = negsucc x ℤ* pos 1                      ＝⟨ l ⁻¹ ⟩
      succℤ (pos 0 ℤ* pos (succ a)) ℤ+ pos n  ＝⟨ i    ⟩
      succℤ (pos 0 ℤ* pos (succ a) ℤ+ pos n)  ＝⟨ ii   ⟩
      pos 0 ℤ* pos (succ a) ℤ+ succℤ (pos n)  ＝⟨ iii  ⟩
      pos 0 ℤ+ pos (succ n)                   ＝⟨ iv   ⟩
      pos (succ n)                            ∎
   where
    i   = ℤ-left-succ (pos 0 ℤ* pos (succ a)) (pos n)
    ii  = ℤ-right-succ (pos 0 ℤ* pos (succ a)) (pos n) ⁻¹
    iii = ap (_ℤ+ pos (succ n)) (ℤ-zero-left-base (pos (succ a)))
    iv  = ℤ-zero-left-neutral (pos (succ n))

positive-order-flip : (m n a b : ℕ)
                    → ((pos (succ m)) , a) 𝔽< ((pos (succ n)) , b)
                    → ((pos (succ a)) , m) 𝔽> ((pos (succ b)) , n)
positive-order-flip m n a b l = transport₂ _<_ I II l
 where
  I : pos (succ m) ℤ* pos (succ b) ＝ pos (succ b) ℤ* pos (succ m)
  I = ℤ*-comm (pos (succ m)) (pos (succ b))

  II : pos (succ n) ℤ* pos (succ a) ＝ pos (succ a) ℤ* pos (succ n)
  II = ℤ*-comm (pos (succ n)) (pos (succ a))

\end{code}
