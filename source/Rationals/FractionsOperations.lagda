Andrew Sneap, November 2021

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Properties
open import UF.Base hiding (_≈_)
open import Integers.Type hiding (abs)
open import Integers.Abs
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Rationals.Fractions
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)

module Rationals.FractionsOperations where

\end{code}

The denom-setup function is useful to manipulate denominators into an
easier to work with form.

\begin{code}

denom-setup : (a b : ℕ) →  pos (succ (pred (succ a ℕ* succ b))) ＝ pos (succ a) ℤ* pos (succ b)
denom-setup a b = pos (succ (pred (succ a ℕ* succ b))) ＝⟨ i  ⟩
                  pos (succ a ℕ* succ b)               ＝⟨ ii ⟩
                  pos (succ a) ℤ* pos (succ b)         ∎
 where
  i  = ap pos (succ-pred-multiplication a b ⁻¹)
  ii = pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹

-_ : 𝔽 → 𝔽
-_ (x , a) = ℤ- x , a

_+_ : 𝔽 → 𝔽 → 𝔽
(x , y) + (x' , y')
 = x ℤ* pos (succ y') ℤ+ x' ℤ* pos (succ y) , pred (succ y ℕ* succ y')

infixl 33 _+_

𝔽-zero-right-neutral : (q : 𝔽) → q + (pos 0 , 0) ＝ q
𝔽-zero-right-neutral (x , a)
 = (x , a) + (pos 0 , 0) ＝⟨refl⟩
   x ℤ+ (pos 0 ℤ* pos (succ a)) , a  ＝⟨ i    ⟩
   x ℤ+ pos 0 , a                    ＝⟨refl⟩
   x , a                             ∎
    where
     i =  ap (λ - → x ℤ+ - , a) (ℤ*-comm (pos 0) (pos (succ a)))

𝔽+-comm : (p q : 𝔽) → p + q ＝ q + p
𝔽+-comm (x , a) (y , b) = ap₂ _,_ I II
 where
  I : x ℤ* pos (succ b) ℤ+ y ℤ* pos (succ a)
    ＝ y ℤ* pos (succ a) ℤ+ x ℤ* pos (succ b)
  I = ℤ+-comm (x ℤ* pos (succ b)) (y ℤ* (pos (succ a)))

  II : pred (succ a ℕ* succ b) ＝ pred (succ b ℕ* succ a)
  II = ap pred (mult-commutativity (succ a) (succ b))

𝔽+-assoc : (a b c : 𝔽) → a + b + c ＝ a + (b + c)
𝔽+-assoc (x , a) (y , b) (z , c) = ap₂ _,_ I II
 where
  left : 𝔽
  left = (x , a) + (y , b)

  right : 𝔽
  right = (y , b) + (z , c)

  α δ : ℤ
  α = pr₁ left
  δ = pr₁ right

  β γ : ℕ
  β = pr₂ left
  γ = pr₂ right

  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  I : α ℤ* c' ℤ+ z ℤ* pos (succ (pred (succ a ℕ* succ b)))
    ＝ x ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ δ ℤ* a'
  I = α ℤ* c' ℤ+ z ℤ* pos (succ (pred (succ a ℕ* succ b)))       ＝⟨ i    ⟩
      (x ℤ* b' ℤ+ y ℤ* a') ℤ* c' ℤ+ z ℤ* pos (succ a ℕ* succ b)  ＝⟨ ii   ⟩
      (x ℤ* b' ℤ+ y ℤ* a') ℤ* c' ℤ+ z ℤ* (a' ℤ* b')              ＝⟨ iii  ⟩
      x ℤ* b' ℤ* c' ℤ+ y ℤ* a' ℤ* c' ℤ+ z ℤ* (b' ℤ* a')          ＝⟨ iv   ⟩
      x ℤ* b' ℤ* c' ℤ+ (y ℤ* a' ℤ* c' ℤ+ z ℤ* (b' ℤ* a'))        ＝⟨ v    ⟩
      x ℤ* (b' ℤ* c') ℤ+ (y ℤ* c' ℤ* a' ℤ+ z ℤ* b' ℤ* a')        ＝⟨ vi   ⟩
      x ℤ* (b' ℤ* c') ℤ+ (y ℤ* c' ℤ+ z ℤ* b') ℤ* a'              ＝⟨ vii  ⟩
      x ℤ* pos (succ b ℕ* succ c) ℤ+ (y ℤ* c' ℤ+ z ℤ* b') ℤ* a'  ＝⟨ viii ⟩
      x ℤ* pos (succ (pred (succ b ℕ* succ c))) ℤ+ δ ℤ* a' ∎
       where
        iₐₚ : succ (pred (succ a ℕ* succ b)) ＝ succ a ℕ* succ b
        iₐₚ = succ-pred-multiplication a b ⁻¹
        iiₐₚ : pos (succ a ℕ* succ b) ＝ a' ℤ* b'
        iiₐₚ = pos-multiplication-equiv-to-ℕ (succ a) (succ b) ⁻¹
        iiiₐₚ : z ℤ* (a' ℤ* b') ＝ z ℤ* (b' ℤ* a')
        iiiₐₚ = ap (z ℤ*_) (ℤ*-comm a' b')
        vₐₚ₁ : y ℤ* a' ℤ* c' ＝ y ℤ* c' ℤ* a'
        vₐₚ₁ = ℤ-mult-rearrangement y a' c'
        vₐₚ₂ : z ℤ* (b' ℤ* a') ＝ z ℤ* b' ℤ* a'
        vₐₚ₂ = ℤ*-assoc z b' a' ⁻¹
        viₐₚ : y ℤ* c' ℤ* a' ℤ+ z ℤ* b' ℤ* a' ＝ (y ℤ* c' ℤ+ z ℤ* b') ℤ* a'
        viₐₚ = distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') a' ⁻¹
        viiₐₚ : b' ℤ* c' ＝ pos (succ b ℕ* succ c)
        viiₐₚ = pos-multiplication-equiv-to-ℕ (succ b) (succ c)
        viiiₐₚ : succ b ℕ* succ c ＝ succ (pred (succ b ℕ* succ c))
        viiiₐₚ = succ-pred-multiplication b c

        i    = ap (λ - → α ℤ* c' ℤ+ z ℤ* pos -) iₐₚ
        ii   = ap (λ - → (x ℤ* b' ℤ+ y ℤ* a') ℤ* c' ℤ+ z ℤ* -) iiₐₚ
        iii  = ap₂ _ℤ+_ (distributivity-mult-over-ℤ (x ℤ* b') (y ℤ* a') c') iiiₐₚ
        iv   = ℤ+-assoc (x ℤ* b' ℤ* c') (y ℤ* a' ℤ* c') (z ℤ* (b' ℤ* a'))
        v    = ap₂ _ℤ+_ (ℤ*-assoc x b' c') (ap₂ _ℤ+_ vₐₚ₁ vₐₚ₂)
        vi   = ap (λ - → x ℤ* (b' ℤ* c') ℤ+ - ) viₐₚ
        vii  = ap (λ - → x ℤ* - ℤ+ (y ℤ* c' ℤ+ z ℤ* b') ℤ* a') viiₐₚ
        viii = ap (λ - →  x ℤ* pos - ℤ+ δ ℤ* a') viiiₐₚ

  II : pred (succ (pred (succ a ℕ* (succ b))) ℕ* succ c)
    ＝ pred (succ a ℕ* succ (pred (succ b ℕ+ succ b ℕ* c)))
  II = pred (succ (pred (succ a ℕ* succ b)) ℕ* succ c)      ＝⟨ i   ⟩
       pred (succ a ℕ* succ b ℕ* succ c)                    ＝⟨ ii  ⟩
       pred (succ a ℕ* (succ b ℕ* succ c))                  ＝⟨ iii ⟩
       pred (succ a ℕ* succ (pred (succ b ℕ+ succ b ℕ* c))) ∎
   where
    i   = ap (λ - → pred (- ℕ* succ c)) (succ-pred-multiplication a b ⁻¹)
    ii  = ap pred (mult-associativity (succ a) (succ b) (succ c))
    iii = ap (λ - → pred (succ a ℕ* -)) (succ-pred-multiplication b c)

≈-addition : (p q r : 𝔽) → p ≈ q → (p + r) ≈ (q + r)
≈-addition (x , a) (y , b) (z , c) e₁ = III
 where
  I :  pos (succ (pred (succ b ℕ* succ c))) ＝ pos (succ b) ℤ* pos (succ c)
  I = denom-setup b c

  II : pos (succ a) ℤ* pos (succ c) ＝ pos (succ (pred (succ a ℕ* succ c)))
  II = denom-setup a c ⁻¹

  a' b' c' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  III : (x , a) + (z , c) ≈ (y , b) + (z , c)
  III = (x ℤ* c' ℤ+ (z ℤ* a')) ℤ* pos (succ (pred (succ b ℕ* succ c))) ＝⟨ i    ⟩
        (x ℤ* c' ℤ+ z ℤ* a') ℤ* (b' ℤ* c')                             ＝⟨ ii   ⟩
        x ℤ* c' ℤ* (b' ℤ* c') ℤ+ z ℤ* a' ℤ* (b' ℤ* c')                 ＝⟨ iii  ⟩
        x ℤ* (b' ℤ* c') ℤ* c' ℤ+ z ℤ* (b' ℤ* c') ℤ* a'                 ＝⟨ iv   ⟩
        x ℤ* b' ℤ* c' ℤ* c' ℤ+ z ℤ* b' ℤ* c' ℤ* a'                     ＝⟨ v    ⟩
        y ℤ* a' ℤ* c' ℤ* c' ℤ+ z ℤ* b' ℤ* (c' ℤ* a')                   ＝⟨ vi   ⟩
        y ℤ* c' ℤ* a' ℤ* c' ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                   ＝⟨ vii  ⟩
        y ℤ* c' ℤ* (a' ℤ* c') ℤ+ z ℤ* b' ℤ* (a' ℤ* c')                 ＝⟨ viii ⟩
        (y ℤ* c' ℤ+ z ℤ* b') ℤ* (a' ℤ* c')                             ＝⟨ ix   ⟩
        (y ℤ* c' ℤ+ (z ℤ* b')) ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎
   where
    iiiₐₚ = ℤ-mult-rearrangement z a' (b' ℤ* c')
    ivₐₚ = ap (_ℤ* a') (ℤ*-assoc z b' c' ⁻¹)
    viₐₚ = ap (λ - → z ℤ* b' ℤ* -) (ℤ*-comm c' a')

    i    = ap (λ - → (x ℤ* c' ℤ+ (z ℤ* a')) ℤ* -) I
    ii   = distributivity-mult-over-ℤ (x ℤ* c') (z ℤ* a') (b' ℤ* c')
    iii  = ap₂ _ℤ+_ (ℤ-mult-rearrangement x c' (b' ℤ* c')) iiiₐₚ
    iv   = ap₂ _ℤ+_ (ap (_ℤ* c') (ℤ*-assoc x b' c' ⁻¹)) ivₐₚ
    v    = ap₂ _ℤ+_ (ap (λ - → -  ℤ* c' ℤ* c') e₁) (ℤ*-assoc (z ℤ* b') c' a')
    vi   = ap₂ _ℤ+_ (ap (_ℤ* c') (ℤ-mult-rearrangement y a' c')) viₐₚ
    vii  = ap (_ℤ+ z ℤ* b' ℤ* (a' ℤ* c')) (ℤ*-assoc (y ℤ* c') a' c')
    viii = distributivity-mult-over-ℤ (y ℤ* c') (z ℤ* b') (a' ℤ* c') ⁻¹
    ix   = ap (λ - → (y ℤ* c' ℤ+ (z ℤ* b')) ℤ* -) II

_*_ : 𝔽 → 𝔽 → 𝔽
(x , y) * (x' , y') = x ℤ* x' , pred (succ y ℕ* succ y')

infixl 34 _*_

≈-over-* : (p q r : 𝔽) → p ≈ q → (p * r) ≈ (q * r)
≈-over-* (x , a) (y , b) (z , c) e = I
 where
  a' b' c' : ℤ
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  I : x ℤ* z ℤ* pos (succ (pred (succ b ℕ* succ c)))
    ＝ y ℤ* z ℤ* pos (succ (pred (succ a ℕ* succ c)))
  I = x ℤ* z ℤ* pos (succ (pred (succ b ℕ* succ c))) ＝⟨ i    ⟩
      x ℤ* z ℤ* (b' ℤ* c')                           ＝⟨ ii   ⟩
      x ℤ* z ℤ* b' ℤ* c'                             ＝⟨ iii  ⟩
      x ℤ* b' ℤ* z ℤ* c'                             ＝⟨ iv   ⟩
      y ℤ* a' ℤ* z ℤ* c'                             ＝⟨ v    ⟩
      y ℤ* (a' ℤ* z) ℤ* c'                           ＝⟨ vi   ⟩
      y ℤ* (z ℤ* a') ℤ* c'                           ＝⟨ vii  ⟩
      y ℤ* z ℤ* a' ℤ* c'                             ＝⟨ viii ⟩
      y ℤ* z ℤ* (a' ℤ* c')                           ＝⟨ ix   ⟩
      y ℤ* z ℤ* pos (succ (pred (succ a ℕ* succ c))) ∎
   where
    i    = ap (λ - → x ℤ* z ℤ* -) (denom-setup b c)
    ii   = ℤ*-assoc (x ℤ* z) b' c' ⁻¹
    iii  = ap (_ℤ* c') (ℤ-mult-rearrangement x z b')
    iv   = ap (λ - → - ℤ* z ℤ* c') e
    v    = ap (_ℤ* c') (ℤ*-assoc y a' z )
    vi   = ap (λ - → y ℤ* - ℤ* c') (ℤ*-comm a' z)
    vii  = ap (_ℤ* c') (ℤ*-assoc y z a' ⁻¹)
    viii = ℤ*-assoc (y ℤ* z) a' c'
    ix   = ap (λ - → (y ℤ* z ℤ* -)) (denom-setup a c ⁻¹)

1/3+1/3≈2/3 : (pos 1 , 2) + (pos 1 , 2) ≈ (pos 2 , 2)
1/3+1/3≈2/3 = refl

1/3+2/3≈1 : (pos 1 , 2) + (pos 2 , 2) ≈ (pos 1 , 0)
1/3+2/3≈1 = refl

𝔽-mult-left-id : (q : 𝔽) → (pos 1 , 0) * q ＝ q
𝔽-mult-left-id (x , a) = to-×-＝ γ₁ γ₂
 where
  γ₁ : pos 1 ℤ* x ＝ x
  γ₁ = ℤ-mult-left-id x

  γ₂ : pred (1 ℕ* succ a) ＝ a
  γ₂ = ap pred (mult-commutativity 1 (succ a))

𝔽-zero-left-is-zero : (q : 𝔽) → (pos 0 , 0) * q ≈ (pos 0 , 0)
𝔽-zero-left-is-zero (x , a)
 = pos 0 ℤ* x ℤ* pos 1                      ＝⟨ i   ⟩
   pos 0 ℤ* (x ℤ* pos 1)                    ＝⟨ ii  ⟩
   pos 0                                    ＝⟨ iii ⟩
   pos 0 ℤ* pos (succ (pred (1 ℕ* succ a))) ∎
  where
   i   = ℤ*-assoc (pos 0) x (pos 1)
   ii  = ℤ-zero-left-base (x ℤ* pos 1)
   iii = ℤ-zero-left-base (pos (succ (pred (1 ℕ* succ a)))) ⁻¹

𝔽*-comm : (p q : 𝔽) → p * q ＝ q * p
𝔽*-comm (x , a) (y , b) = ap₂ _,_ I II
 where
  I : x ℤ* y ＝ y ℤ* x
  I = ℤ*-comm x y

  II : pred (succ a ℕ* succ b) ＝ pred (succ b ℕ* succ a)
  II = ap pred (mult-commutativity (succ a) (succ b))

𝔽*-assoc : (p q r : 𝔽) → p * q * r ＝ p * (q * r)
𝔽*-assoc (x , a) (y , b) (z , c) = ap₂ _,_ I II
 where
  I : x ℤ* y ℤ* z ＝ x ℤ* (y ℤ* z)
  I = ℤ*-assoc x y z

  a' b' c' : ℕ
  a' = succ a
  b' = succ b
  c' = succ c

  II : pred (succ (pred (a' ℕ* b')) ℕ* c') ＝ pred (a' ℕ* succ (pred (b' ℕ* c')))
  II = pred (succ (pred (a' ℕ* b')) ℕ* c') ＝⟨ i   ⟩
       pred (a' ℕ* b' ℕ* c')               ＝⟨ ii  ⟩
       pred (a' ℕ* (b' ℕ* c'))             ＝⟨ iii ⟩
       pred (a' ℕ* succ (pred (b' ℕ* c'))) ∎
   where
    i   = ap (λ - → pred (- ℕ* c')) (succ-pred-multiplication a b ⁻¹)
    ii  = ap pred (mult-associativity a' b' c')
    iii = ap (λ - → pred (a' ℕ* -)) (succ-pred-multiplication b c)

𝔽-dist : (p q r : 𝔽) → p * (q + r) ≈ p * q + p * r
𝔽-dist (x , a) (y , b) (z , c) = I
 where
  a' b' c' : ℕ
  a' = succ a
  b' = succ b
  c' = succ c

  a'' b'' c'' k l : ℤ
  a'' = pos a'
  b'' = pos b'
  c'' = pos c'
  k = pos (succ (pred (a' ℕ* c')))
  l = pos (succ (pred (a' ℕ* b')))

  I-lemma : (x y p q : ℤ) → x ℤ* y ℤ* (p ℤ* q) ＝ x ℤ* p ℤ* (y ℤ* q)
  I-lemma x y p q = x ℤ* y ℤ* (p ℤ* q) ＝⟨ ℤ*-assoc (x ℤ* y) p q ⁻¹             ⟩
                    x ℤ* y ℤ* p ℤ* q   ＝⟨ ap (_ℤ* q) (ℤ*-assoc x y p )         ⟩
                    x ℤ* (y ℤ* p) ℤ* q ＝⟨ ap (λ - → x ℤ* - ℤ* q) (ℤ*-comm y p) ⟩
                    x ℤ* (p ℤ* y) ℤ* q ＝⟨ ap (_ℤ* q) (ℤ*-assoc x p y ⁻¹)       ⟩
                    x ℤ* p ℤ* y ℤ* q   ＝⟨ ℤ*-assoc (x ℤ* p) y q                ⟩
                    x ℤ* p ℤ* (y ℤ* q) ∎

  I : _ ＝ _
  I = x ℤ* (y ℤ* c'' ℤ+ z ℤ* b'') ℤ* pos (succ (pred (succ (pred (a' ℕ* b')) ℕ* (succ (pred (a' ℕ* c'))))))  ＝⟨ i    ⟩
      x ℤ* (y ℤ* c'' ℤ+ z ℤ* b'') ℤ* (l ℤ* k)                                                                ＝⟨ ii   ⟩
      x ℤ* (y ℤ* c'' ℤ+ z ℤ* b'') ℤ* (pos (a' ℕ* b') ℤ* pos (a' ℕ* c'))                                      ＝⟨ iii  ⟩
      x ℤ* (y ℤ* c'' ℤ+ z ℤ* b'') ℤ* (a'' ℤ* b'' ℤ* (a'' ℤ* c''))                                            ＝⟨ iv   ⟩
      x ℤ* (y ℤ* c'' ℤ+ z ℤ* b'') ℤ* (a'' ℤ* (b'' ℤ* (a'' ℤ* c'')))                                          ＝⟨ v    ⟩
      x ℤ* (y ℤ* c'' ℤ+ z ℤ* b'') ℤ* a'' ℤ*  (b'' ℤ* (a'' ℤ* c''))                                           ＝⟨ vi   ⟩
      x ℤ* a'' ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* (a'' ℤ* (b'' ℤ* c''))                                          ＝⟨ vii  ⟩
     (x ℤ* a'' ℤ* (y ℤ* c'') ℤ+ x ℤ* a'' ℤ* (z ℤ* b'')) ℤ* (a'' ℤ* (pos (b' ℕ* c')))                         ＝⟨ viii ⟩
     (x ℤ* y ℤ* (a'' ℤ* c'') ℤ+ x ℤ* z ℤ* (a'' ℤ* b'')) ℤ* (a'' ℤ* (pos (b' ℕ* c')))                         ＝⟨ ix   ⟩
     (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* (a'' ℤ* (pos (b' ℕ* c')))                                             ＝⟨ xi   ⟩
     (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* pos (a' ℕ* (b' ℕ* c'))                                                ＝⟨ xii  ⟩
     (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* pos (a' ℕ* succ (pred (b' ℕ* c')))                                    ＝⟨ xiii ⟩
     (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* pos (succ (pred (a' ℕ* succ (pred (b' ℕ* c')))))                      ∎
   where
    i    = ap (λ β → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* β ) (denom-setup (pred (a' ℕ* b')) (pred (a' ℕ* c')))
    ii   = ap₂ (λ α β → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* (pos α ℤ* pos β)) (succ-pred-multiplication a b ⁻¹) (succ-pred-multiplication a c ⁻¹)
    iii  = ap₂ (λ α β → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* (α ℤ* β) ) (pos-multiplication-equiv-to-ℕ a' b' ⁻¹) (pos-multiplication-equiv-to-ℕ a' c' ⁻¹)
    iv   = ap (λ α → x ℤ* (y ℤ* c'' ℤ+ (z ℤ* b'')) ℤ* α ) (ℤ*-assoc a'' b'' ( a'' ℤ* c'') )
    v    = ℤ*-assoc (x ℤ* (  y ℤ* c'' ℤ+ (z ℤ* b'')  )) a'' ( b'' ℤ*   (a'' ℤ* c'')) ⁻¹
    vi   = ap₂ (λ α β → α ℤ* β) (ℤ-mult-rearrangement x ( y ℤ* c'' ℤ+ (z ℤ* b'')) a'') (ℤ-mult-rearrangement''' b'' a'' c'')
    vii  = ap₂ (λ α β → α ℤ* (a'' ℤ* β)) (distributivity-mult-over-ℤ' (y ℤ* c'') (z ℤ* b'') (x ℤ* a'')) (pos-multiplication-equiv-to-ℕ b' c')
    viii = ap₂ (λ α β → (α ℤ+ β) ℤ* ((a'' ℤ* (pos (b' ℕ* c'))))) (I-lemma x a'' y c'') (I-lemma x a'' z b'')
    ix   = ap₂ (λ α β → (x ℤ* y ℤ* α ℤ+ x ℤ* z ℤ* β) ℤ* ((a'' ℤ* (pos (b' ℕ* c'))))) (denom-setup a c ⁻¹) (denom-setup a b ⁻¹)
    xi   = ap (λ α → (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* α) (pos-multiplication-equiv-to-ℕ a' (b' ℕ* c'))
    xii  = ap  (λ α → (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* (pos (a' ℕ* α))) (succ-pred-multiplication b c)
    xiii = ap (λ α → (x ℤ* y ℤ* k ℤ+ (x ℤ* z ℤ* l)) ℤ* pos α) (succ-pred-multiplication a (pred (b' ℕ* c')))

abs : 𝔽 → 𝔽
abs (x , a) = absℤ x , a

𝔽-abs-0 : pos 0 , 0 ＝ abs (pos 0 , 0)
𝔽-abs-0 = by-definition

𝔽-abs-neg-equals-pos : (q : 𝔽) → abs q ≈ abs (- q)
𝔽-abs-neg-equals-pos (x , a) = ap (_ℤ* (pos (succ a))) (absℤ-removes-neg-sign x)

𝔽-subtraction-dist-over-mult : (p q : 𝔽) → (- p) * q ≈ (- (p * q))
𝔽-subtraction-dist-over-mult (x , a) (y , b) = γ
 where
  I : (ℤ- x) ℤ* y ＝ ℤ- (x ℤ* y)
  I = negation-dist-over-mult' x y

  γ : _
  γ = ap (_ℤ* pos (succ (pred (succ a ℕ* succ b)))) I

𝔽-minus-dist : ((x , a) (y , b) : 𝔽)
             → (ℤ- x , a) + (ℤ- y , b) ≈ (- ((x , a) + (y , b)))
𝔽-minus-dist (x , a) (y , b) = γ
 where
  pa = (pos ∘ succ) a
  pb = (pos ∘ succ) b

  γ' : (ℤ- x) ℤ* pb ℤ+ (ℤ- y) ℤ* pa ＝ ℤ- (x ℤ* pb ℤ+ y ℤ* pa)
  γ' = (ℤ- x) ℤ* pb ℤ+ (ℤ- y) ℤ* pa ＝⟨ i   ⟩
       (ℤ- x ℤ* pb) ℤ+ (ℤ- y) ℤ* pa ＝⟨ ii  ⟩
       (ℤ- x ℤ* pb) ℤ+ (ℤ- y ℤ* pa) ＝⟨ iii ⟩
       ℤ- (x ℤ* pb ℤ+ y ℤ* pa)      ∎
   where
    i   = ap (_ℤ+ (ℤ- y) ℤ* pa) (negation-dist-over-mult' x pb)
    ii  = ap ((ℤ- x ℤ* pb) ℤ+_) (negation-dist-over-mult' y pa)
    iii = negation-dist (x ℤ* pb) (y ℤ* pa)

  γ : ((ℤ- x , a) + (ℤ- y , b)) ≈ (- ((x , a) + (y , b)))
  γ = ap (_ℤ* pos (succ (pred (succ a ℕ* succ b)))) γ'

𝔽+-inverse : ((x , a) : 𝔽) → ((ℤ- x , a) + (x , a)) ≈ (pos 0 , 0)
𝔽+-inverse (x , a) = γ
 where
  pa = (pos ∘ succ) a

  γ : ((ℤ- x , a) + (x , a)) ≈ (pos 0 , 0)
  γ = ((ℤ- x) ℤ* pa ℤ+ x ℤ* pa) ℤ* pos 1            ＝⟨ i   ⟩
      ((ℤ- x) ℤ* pa ℤ+ x ℤ* pa)                     ＝⟨ ii  ⟩
      ((ℤ- x) ℤ+ x) ℤ* pa                           ＝⟨ iii ⟩
      (x ℤ+ (ℤ- x)) ℤ* pa                           ＝⟨ iv  ⟩
      pos 0 ℤ* pa                                   ＝⟨ v   ⟩
      pos 0                                         ＝⟨ vi  ⟩
      pos 0 ℤ* pos (succ (pred (succ a ℕ* succ a))) ∎
   where
    i   = ℤ-mult-right-id ((ℤ- x) ℤ* pa ℤ+ (x ℤ* pa))
    ii  = distributivity-mult-over-ℤ (ℤ- x) x pa ⁻¹
    iii = ap (_ℤ* pa) (ℤ+-comm (ℤ- x) x)
    iv  = ap (_ℤ* pa) (ℤ-sum-of-inverse-is-zero x)
    v   = ℤ-zero-left-base pa
    vi  = ℤ-zero-left-base (pos (succ (pred (succ a ℕ* succ a)))) ⁻¹

𝔽+-inverse' : ((x , a) : 𝔽) → ((x , a) + (ℤ- x , a)) ≈ (pos 0 , 0)
𝔽+-inverse' (x , a) = γ
 where
  I : (x , a) + (ℤ- x , a) ＝ (ℤ- x , a) + (x , a)
  I = 𝔽+-comm (x , a) (ℤ- x , a)

  II : ((x , a) + (ℤ- x , a)) ≈ ((x , a) + (ℤ- x , a))
  II = ≈-refl ((x , a) + (ℤ- x , a))

  III : ((x , a) + (ℤ- x , a)) ≈ ((ℤ- x , a) + (x , a))
  III = transport (((x , a) + (ℤ- x , a)) ≈_) I II

  IV : ((ℤ- x , a) + (x , a)) ≈ (pos 0 , 0)
  IV = 𝔽+-inverse (x , a)

  γ : ((x , a) + (ℤ- x , a)) ≈ (pos 0 , 0)
  γ = ≈-trans ((x , a) + (ℤ- x , a)) ((ℤ- x , a) + (x , a)) (pos 0 , 0) III IV

𝔽-add-same-denom : ((x , a) (y , a) : 𝔽) → (((x , a) + (y , a)) ≈ (x ℤ+ y , a))
𝔽-add-same-denom (x , a) (y , b) = γ
 where
  γ : _
  γ = (x ℤ* pos (succ b) ℤ+ y ℤ* pos (succ b)) ℤ* pos (succ b)   ＝⟨ i   ⟩
      (x ℤ+ y) ℤ* pos (succ b) ℤ* pos (succ b)                   ＝⟨ ii  ⟩
      (x ℤ+ y) ℤ* (pos (succ b) ℤ* pos (succ b))                 ＝⟨ iii ⟩
      (x ℤ+ y) ℤ* pos (succ (pred (succ b ℕ* succ b)))           ∎
   where
    i = ap (_ℤ* pos (succ b)) (distributivity-mult-over-ℤ x y (pos (succ b)) ⁻¹)
    ii = ℤ*-assoc (x ℤ+ y ) (pos (succ b)) (pos (succ b))
    iii = ap ((x ℤ+ y) ℤ*_) (denom-setup b b ⁻¹)

\end{code}
