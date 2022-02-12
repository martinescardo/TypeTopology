Andrew Sneap - 26th November 2021

In this file I define the free rationals. They are rationals they may not be in the lowest terms, with (a , b) : ℤ × ℕ were ℤ is the numerator, and b represents a denominator of b+1, ruling out the possibility of a zero-denominator.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import UF-Base hiding (_≈_) --TypeTopology
open import UF-FunExt --TypeTopology

open import IntegersB
open import IntegersAddition renaming (_+_ to _ℤ+_)
open import IntegersMultiplication renaming (_*_ to _ℤ*_)
open import IntegersNegation renaming (-_ to ℤ-_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import NaturalNumbers-Properties
open import ncRationals
open import ncRationalsOperations renaming (-_ to ℚₙ-_ ; _+_ to _ℚₙ+_ ; _*_ to _ℚₙ*_)
open import Rationals
open import RationalsAddition
open import RationalsMultiplication

-_ : ℚ → ℚ
- ((x , a) , p) = toℚ (ℚₙ- (x , a))

infix 32 -_

_-_ : ℚ → ℚ → ℚ
p - q = p + (- q)

infixl 32 _-_

ℚ-minus-zero-is-zero : 0ℚ ≡ - 0ℚ 
ℚ-minus-zero-is-zero = refl

toℚ-neg : Fun-Ext → ((x , a) : ℚₙ) → (- toℚ (x , a)) ≡ toℚ (ℚₙ- (x , a)) 
toℚ-neg fe (x , a) = IV
 where
  p : ℚ
  p = toℚ (x , a)

  x' : ℤ
  x' = pr₁ (pr₁ p)
  a' : ℕ
  a' = pr₂ (pr₁ p)

  helper : (ℤ- x' , a') ≈ (ℤ- x , a) → toℚ (ℤ- x' , a') ≡ toℚ (ℤ- x , a)
  helper = pr₁ (equiv-equality fe (ℤ- x' , a') (ℤ- x , a))

  I : (x , a) ≈ (x' , a')
  I = ≈-toℚ (x , a)

  II : (x' , a') ≈ (x , a)
  II = ≈-sym (x , a) (x' , a') I

  III : x' ℤ* pos (succ a) ≡ x ℤ* pos (succ a') → (ℤ- x' , a') ≈ (ℤ- x , a)
  III e = (ℤ- x') ℤ* pos (succ a)   ≡⟨ subtraction-dist-over-mult' x' (pos (succ a)) ⟩
          ℤ- (x' ℤ* pos (succ a))   ≡⟨ ap ℤ-_ e ⟩
          ℤ- (x ℤ* pos (succ a'))   ≡⟨ subtraction-dist-over-mult' x (pos (succ a')) ⁻¹ ⟩
          (ℤ- x) ℤ* pos (succ a') ∎

  IV : (- toℚ (x , a)) ≡ toℚ (ℤ- x , a) 
  IV = (- toℚ (x , a))       ≡⟨ refl ⟩
        (- p)                ≡⟨ refl ⟩
        toℚ (ℤ- x' , a')     ≡⟨ helper (III II) ⟩
        toℚ (ℤ- x , a)  ∎

ℚ-minus-dist : Fun-Ext → (p q : ℚ) → (- p) + (- q) ≡ - (p + q)
ℚ-minus-dist fe ((x , a) , p) ((y , b) , q) = II
 where
  pnc : Σ p' ꞉ ℚₙ , ((x , a) , p) ≡ toℚ p'
  pnc = q-has-qn fe ((x , a) , p)

  qnc : Σ q' ꞉ ℚₙ , ((y , b) , q) ≡ toℚ q'
  qnc = q-has-qn fe ((y , b) , q)

  p' q' : ℚₙ
  p' = pr₁ pnc
  q' = pr₁ qnc

  x' y' : ℤ
  x' = pr₁ p'
  y' = pr₁ q'

  a' b' : ℕ
  a' = pr₂ p'
  b' = pr₂ q'

  pqnc : Σ pq ꞉ ℚₙ , (toℚ (p' ℚₙ+ q')) ≡ toℚ pq
  pqnc = q-has-qn fe (toℚ (p' ℚₙ+ q'))

  pq : ℚₙ
  pq = pr₁ pqnc

  z : ℤ
  z = pr₁ pq

  c : ℕ
  c = pr₂ pq

  I : ((ℤ- x , a) ℚₙ+ (ℤ- y , b)) ≈ (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b')) → toℚ ((ℤ- x , a) ℚₙ+ (ℤ- y , b)) ≡ toℚ (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b')) 
  I = lr-implication (equiv-equality fe ((ℤ- x , a) ℚₙ+ (ℤ- y , b)) (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b')))

  II : (- ((x , a) , p)) + (- ((y , b) , q)) ≡ - (((x , a) , p) + ((y , b) , q))
  II = ((- ((x , a) , p)) + (- ((y , b) , q)))                                                      ≡⟨ refl ⟩
       (toℚ ((ℤ- x) , a) + toℚ ((ℤ- y) , b))                                                        ≡⟨ toℚ-+ fe (ℤ- x , a) (ℤ- y , b) ⁻¹  ⟩
       toℚ ((ℤ- x , a) ℚₙ+ (ℤ- y , b))                                                              ≡⟨ I refl ⟩
       toℚ (((ℤ- x') , a') ℚₙ+ ((ℤ- y') , b'))                                                      ≡⟨ ap₂ (λ α β → toℚ (α ℤ+ β ,  pred (succ a' ℕ* succ b'))) (subtraction-dist-over-mult' x' (pos (succ b'))) (subtraction-dist-over-mult' y' (pos (succ a'))) ⟩
       toℚ (((ℤ- x' ℤ* pos (succ b')) ℤ+ (ℤ- y' ℤ* pos (succ a'))) , ( pred (succ a' ℕ* succ b'))) ≡⟨ ap (λ - → toℚ (- , pred (succ a' ℕ* succ b'))) (negation-dist (x' ℤ* pos (succ b')) (y' ℤ* pos (succ a'))) ⟩
       toℚ ((ℤ- (x' ℤ* pos (succ b') ℤ+ y' ℤ* pos (succ a'))) , ( pred (succ a' ℕ* succ b')))        ≡⟨ toℚ-neg fe ((x' ℤ* pos (succ b') ℤ+ y' ℤ* pos (succ a') , pred (succ a' ℕ* succ b'))) ⁻¹ ⟩
       (- toℚ (x' ℤ* pos (succ b') ℤ+ y' ℤ* pos (succ a') , pred (succ a' ℕ* succ b')))            ≡⟨ refl ⟩
       (- toℚ (p' ℚₙ+ q'))                                                                          ≡⟨ refl ⟩
       (- (((x , a) , p) + ((y , b) , q))) ∎

ℚ+-inverse-lemma : ((x , a) : ℚₙ) → ((ℤ- x , a) ℚₙ+ (x , a)) ≈ (pos zero , zero)
ℚ+-inverse-lemma (x , a) = I
 where
  I : ((ℤ- x , a) ℚₙ+ (x , a)) ≈ (pos zero , zero)
  I = ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a))) ℤ* pos 1 ≡⟨ ℤ-mult-right-id ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a))) ⟩
      ((ℤ- x) ℤ* pos (succ a) ℤ+ (x ℤ* pos (succ a)))          ≡⟨ distributivity-mult-over-ℤ (ℤ- x) x (pos (succ a)) ⁻¹ ⟩
      ((ℤ- x) ℤ+ x) ℤ* pos (succ a)                            ≡⟨ ap (λ - → - ℤ* pos (succ a)) (ℤ+-comm (ℤ- x) x)  ⟩
      (x ℤ+ (ℤ- x)) ℤ* pos (succ a)                            ≡⟨ ap (λ - → - ℤ* pos (succ a)) (ℤ-sum-of-inverse-is-zero x) ⟩
      pos 0 ℤ* pos (succ a)                                    ≡⟨ ℤ-zero-left-is-zero (pos (succ a)) ⟩
      pos 0                                                    ≡⟨ ℤ-zero-left-is-zero (pos (succ (pred (succ a ℕ* succ a)))) ⁻¹  ⟩
      pos zero ℤ* pos (succ (pred (succ a ℕ* succ a)))         ∎

ℚ-inverse-sum-to-zero : Fun-Ext → (q : ℚ) → q + (- q) ≡ 0ℚ
ℚ-inverse-sum-to-zero fe ((x , a) , p) = γ
 where
  -qnc : Σ (x' , y') ꞉ ℚₙ , toℚ (ℤ- x , a) ≡ toℚ (x' , y') 
  -qnc = q-has-qn fe (toℚ (ℤ- x , a))

  x' : ℤ
  x' = pr₁ (pr₁ -qnc)

  y' : ℕ
  y' = pr₂ (pr₁ -qnc)

  I : ((x , a) ℚₙ+ (x' , y')) ≈ (pos 0 , 0) → toℚ ((x , a) ℚₙ+ (x' , y')) ≡ toℚ (pos 0 , 0)
  I = equiv→equality fe ((x , a) ℚₙ+ (x' , y')) (pos 0 , 0)

  II : (x , a) ℚₙ+ (x' , y') ≈ ((x' , y') ℚₙ+ (x , a))
  II = transport ((x , a) ℚₙ+ (x' , y') ≈_) (ℚₙ+-comm (x , a) (x' , y')) (≈-refl ((x , a) ℚₙ+ (x' , y')))

  IIIᵢ : (x' , y') ≈ (ℤ- x , a)
  IIIᵢ = ≈-sym (ℤ- x , a) (x' , y') (equality→equiv fe (ℤ- x , a) (x' , y') (pr₂ -qnc))

  III : ((x' , y') ℚₙ+ (x , a)) ≈ ((ℤ- x , a) ℚₙ+ (x , a))
  III = ≈-addition (x' , y') (ℤ- x , a) (x , a) IIIᵢ

  IVᵢ : (x , a) ℚₙ+ (x' , y') ≈ ((ℤ- x , a) ℚₙ+ (x , a))
  IVᵢ = ≈-trans ((x , a) ℚₙ+ (x' , y')) ((x' , y') ℚₙ+ (x , a)) ((ℤ- x , a) ℚₙ+ (x , a)) II III

  IV : ((ℤ- x , a) ℚₙ+ (x , a)) ≈ (pos 0 , 0)
  IV = ℚ+-inverse-lemma (x , a)

  V : ((x , a) ℚₙ+ (x' , y')) ≈ (pos 0 , 0)
  V = ≈-trans ((x , a) ℚₙ+ (x' , y')) ((ℤ- x , a) ℚₙ+ (x , a)) ((pos 0 , 0)) IVᵢ IV

  γ : (((x , a) , p) + (- ((x , a) , p))) ≡ 0ℚ
  γ = (((x , a) , p) + (- ((x , a) , p)))     ≡⟨ refl ⟩
      (((x , a) , p) + toℚ (ℤ- x , a))        ≡⟨ refl ⟩
      toℚ ((x , a) ℚₙ+ (x' , y'))             ≡⟨ I V ⟩
      toℚ (pos 0 , 0)                         ≡⟨ refl ⟩
      0ℚ ∎

ℚ-inverse-sum-to-zero' : Fun-Ext → (q : ℚ) → (- q) + q ≡ 0ℚ
ℚ-inverse-sum-to-zero' fe q = ℚ+-comm (- q) q ∙ ℚ-inverse-sum-to-zero fe q

ℚ+-inverse : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚ , q + q' ≡ 0ℚ
ℚ+-inverse fe q = (- q) , (ℚ-inverse-sum-to-zero fe q)

ℚ+-inverse' : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚ , q' + q ≡ 0ℚ
ℚ+-inverse' fe q = f (ℚ+-inverse fe q)
  where
   f : Σ q' ꞉ ℚ , q + q' ≡ 0ℚ → Σ q' ꞉ ℚ , q' + q ≡ 0ℚ
   f (q' , e) = q' , (ℚ+-comm q' q ∙ e)

ℚ-minus-minus : Fun-Ext → (p : ℚ) → p ≡ (- (- p))
ℚ-minus-minus fe p = IV
 where
  p-constructed : Σ (x , a) ꞉ ℚₙ , p ≡ toℚ (x , a)
  p-constructed = q-has-qn fe p

  x = pr₁ (pr₁ p-constructed)
  a = pr₂ (pr₁ p-constructed)

  I : (- toℚ (x , a)) ≡ toℚ (ℤ- x , a)
  I = toℚ-neg fe (x , a)

  II : - toℚ (ℤ- x , a) ≡ toℚ ((ℤ- (ℤ- x)) , a)
  II = toℚ-neg fe (ℤ- x , a)

  III : toℚ ((ℤ- (ℤ- x)) , a) ≡ toℚ (x , a)
  III = ap (λ k → toℚ (k , a)) (minus-minus-is-plus x)

  IV : p ≡ (- (- p))
  IV = p                     ≡⟨ pr₂ p-constructed ⟩
       toℚ (x , a)           ≡⟨ III ⁻¹ ⟩
       toℚ (ℤ- (ℤ- x) , a)   ≡⟨ II ⁻¹ ⟩
       (- toℚ (ℤ- x , a))    ≡⟨ ap -_ (I ⁻¹) ⟩
       (- (- toℚ (x , a)))   ≡⟨ ap (λ k → - (- k)) (pr₂ p-constructed ⁻¹) ⟩
       (- (- p)) ∎

ℚ-add-zero : Fun-Ext → (x y z : ℚ) → (x + y) ≡ ((x - z) + (z + y))
ℚ-add-zero fe x y z = I
 where
  I : (x + y) ≡ ((x - z) + (z + y))
  I = (x + y)                    ≡⟨ ap (_+ y) (ℚ-zero-right-neutral fe x ⁻¹) ⟩
      ((x + 0ℚ) + y)             ≡⟨ ap (λ k → (x + k) + y) (ℚ-inverse-sum-to-zero' fe z ⁻¹) ⟩
      ((x + ((- z) + z)) + y)    ≡⟨ ap (_+ y) (ℚ+-assoc fe x (- z) z ⁻¹) ⟩
      (((x + (- z)) + z) + y)    ≡⟨ ℚ+-assoc fe (x - z) z y ⟩
      ((x - z) + (z + y)) ∎

ℚ-subtraction-dist-over-mult : Fun-Ext → (p q : ℚ) → (- p) * q ≡ - (p * q)
ℚ-subtraction-dist-over-mult fe ((x , a) , α) ((y , b) , β) = I
 where
  xa : Σ (x' , a') ꞉ ℚₙ , ((x , a) , α) ≡ toℚ (x' , a')
  xa = q-has-qn fe ((x , a) , α)
  yb : Σ (y' , b') ꞉ ℚₙ , ((y , b) , β) ≡ toℚ (y' , b')
  yb = q-has-qn fe ((y , b) , β)
  x' = pr₁ (pr₁ xa)
  a' = pr₂ (pr₁ xa)
  y' = pr₁ (pr₁ yb)
  b' = pr₂ (pr₁ yb)

  II : ((ℚₙ- (x' , a')) ℚₙ* (y' , b')) ≈ (ℚₙ- ((x' , a') ℚₙ* (y' , b')))
  II = ℚₙ-subtraction-dist-over-mult (x' , a') (y' , b')

  I : (- ((x , a) , α)) * ((y , b) , β) ≡ - ((x , a) , α) * ((y , b) , β)
  I = (- ((x , a) , α)) * ((y , b) , β)    ≡⟨ ap (λ z → (- ((x , a) , α)) * z) (pr₂ yb) ⟩
      toℚ (ℚₙ- (x , a)) * toℚ (y' , b')     ≡⟨ toℚ-* fe (ℚₙ- (x , a)) (y' , b') ⁻¹ ⟩
      toℚ ((ℚₙ- (x' , a')) ℚₙ* (y' , b'))   ≡⟨ equiv→equality fe ((ℚₙ- (x' , a')) ℚₙ* (y' , b')) (ℚₙ- ((x' , a') ℚₙ* (y' , b'))) II ⟩
      toℚ (ℚₙ- ((x' , a') ℚₙ* (y' , b')))   ≡⟨ toℚ-neg fe ((x' , a') ℚₙ* (y' , b')) ⁻¹ ⟩
      - toℚ ((x' , a') ℚₙ* (y' , b'))      ≡⟨ ap -_ (toℚ-* fe (x' , a') (y' , b')) ⟩
      - toℚ (x' , a') * toℚ (y' , b')      ≡⟨ ap₂ (λ z z' → - (z * z')) (pr₂ xa ⁻¹) (pr₂ yb ⁻¹) ⟩
      - ((x , a) , α) * ((y , b) , β)      ∎

toℚ-subtraction : Fun-Ext → (p q : ℚₙ) → toℚ p - toℚ q ≡ toℚ (p ℚₙ+ (ℚₙ- q))
toℚ-subtraction fe p q = II
 where
  I : toℚ (p ℚₙ+ (ℚₙ- q)) ≡ toℚ p + toℚ (ℚₙ- q)
  I = toℚ-+ fe p (ℚₙ- q)
  II : toℚ p - toℚ q ≡ toℚ (p ℚₙ+ (ℚₙ- q))
  II = toℚ p - toℚ q       ≡⟨ ap (toℚ p +_) (toℚ-neg fe q) ⟩
       toℚ p + toℚ (ℚₙ- q) ≡⟨ I ⁻¹ ⟩
       toℚ (p ℚₙ+ (ℚₙ- q)) ∎

1-2/5≡3/5 : Fun-Ext → 1ℚ - 2/5 ≡ 3/5
1-2/5≡3/5 fe = 1ℚ - 2/5              ≡⟨ ap (λ α → α - 2/5) (2/5+3/5 fe ⁻¹) ⟩
               2/5 + 3/5 - 2/5       ≡⟨ ℚ+-assoc fe 2/5 3/5 (- 2/5) ⟩
               2/5 + (3/5 - 2/5)     ≡⟨ ap (2/5 +_) (ℚ+-comm 3/5 (- 2/5)) ⟩
               2/5 + ((- 2/5) + 3/5) ≡⟨ ℚ+-assoc fe 2/5 (- 2/5) 3/5 ⁻¹ ⟩
               2/5 - 2/5 + 3/5       ≡⟨ ap (_+ 3/5) (ℚ-inverse-sum-to-zero fe 2/5) ⟩
               0ℚ + 3/5              ≡⟨ ℚ-zero-left-neutral fe 3/5 ⟩ 
               3/5                   ∎

