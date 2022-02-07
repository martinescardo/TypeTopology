Andrew Sneap - 27th April 2021

I link to this module within the Natural Numbers section of my report.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import NaturalsAddition -- TypeTopology
open import NaturalNumbers-Properties -- TypeTopology
open import NaturalsOrder -- TypeTopology
open import OrderNotation -- TypeTopology
open import UF-Base --TypeTopology

open import MoreNaturalProperties
open import NaturalsOrderExtended

module NaturalsMultiplication where

_*_ : (x y : ℕ) → ℕ
x * 0      = 0
x * succ y = x + x * y

infixl 32 _*_

zero-right-is-zero : (x : ℕ) → x * 0 ≡ 0 
zero-right-is-zero x = refl

zero-left-is-zero : (x : ℕ) → 0 * x ≡ 0
zero-left-is-zero = induction refl step
 where
  step : (x : ℕ)
       → 0 * x     ≡ 0
       → 0 + 0 * x ≡ 0
  step x IH = 0 + 0 * x  ≡⟨ ap (0 +_) IH ⟩
              0 + 0      ≡⟨ refl         ⟩
              0          ∎

zero-left-is-zero' : (x : ℕ) → 0 * x ≡ 0
zero-left-is-zero' 0        = refl
zero-left-is-zero' (succ x) = 0 * succ x ≡⟨ refl                             ⟩
                              0 + 0 * x  ≡⟨ ap (0 +_) (zero-left-is-zero' x) ⟩
                              0 + 0      ≡⟨ refl                             ⟩
                              0          ∎

mult-right-id : (x : ℕ) → x * 1 ≡ x
mult-right-id x = refl

mult-left-id : (x : ℕ) → 1 * x ≡ x
mult-left-id = induction base step
 where
  base : 1 * 0 ≡ 0
  base = refl

  step : (x : ℕ)
       → 1 * x     ≡ x
       → 1 + 1 * x ≡ succ x
         
  step x IH = 1 + 1 * x  ≡⟨ ap (1 +_) IH        ⟩
              1 + x      ≡⟨ addition-commutativity 1 x ⟩
              x + 1      ≡⟨ refl                       ⟩
              succ x     ∎

distributivity-mult-over-nat : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z 
distributivity-mult-over-nat x y = induction refl step
 where
  step : (k : ℕ)
       → x * (y + k)      ≡ x * y + x * k
       → x * (y + succ k) ≡ x * y + x * succ k

  step k IH = x * (y + succ k)        ≡⟨ refl                                                ⟩
              x + x * (y + k)         ≡⟨ ap (x +_ ) IH                                       ⟩
              x + (x * y + x * k)     ≡⟨ ap (x +_ ) (addition-commutativity (x * y) (x * k)) ⟩ 
              x + (x * k + x * y)     ≡⟨ addition-associativity x (x * k) (x * y) ⁻¹         ⟩
              x + x * k + x * y       ≡⟨ addition-commutativity (x + x * k) (x * y)          ⟩
              x * y + (x + x * k)     ≡⟨ refl                                                ⟩  
              x * y + (x * (succ k))  ∎

addition-associativity-lemma : (x y u v : ℕ) → x + y + (u + v) ≡ x + y + u + v
addition-associativity-lemma x y u v = x + y + (u + v) ≡⟨ addition-associativity (x + y) u v ⁻¹ ⟩
                                       x + y + u + v   ∎

distributivity-mult-over-nat' : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
distributivity-mult-over-nat' x y = induction refl step
 where
  step : (k : ℕ)
       → (x + y) * k      ≡ x * k + y * k
       → (x + y) * succ k ≡ x * succ k + y * succ k

  step k IH = (x + y) * succ k                  ≡⟨ refl                                                        ⟩
              x + y + (x + y) * k               ≡⟨ ap (x + y +_) IH                                            ⟩
              x + y + (x * k + y * k)           ≡⟨ addition-associativity-lemma x y (x * k) (y * k)            ⟩
              x + y + x * k + y * k             ≡⟨ ap (_+ y * k) (addition-associativity x y (x * k))          ⟩
              x + (y + x * k) + y * k           ≡⟨ ap (λ - → x + - + y * k) (addition-commutativity y (x * k)) ⟩
              x + (x * k + y) + y * k           ≡⟨ ap (_+ y * k) (addition-associativity x (x * k) y) ⁻¹       ⟩
              x + x * k + y + y * k             ≡⟨ addition-associativity (x + x * k) y (y * k)                ⟩ 
              x + x * k + (y + y * k)           ≡⟨ refl                                                        ⟩
              x * succ k + y * succ k           ∎
                
mult-commutativity : (x y : ℕ) → x * y ≡ y * x
mult-commutativity x = induction base step
 where
  base : 0 ≡ 0 * x
  base = zero-left-is-zero x ⁻¹

  step : (k : ℕ)
       → x * k     ≡ k * x
       → x + x * k ≡ succ k * x

  step k IH = x + x * k       ≡⟨ ap (x +_ ) IH                          ⟩
              x + k * x       ≡⟨ ap (_+ k * x) (mult-left-id x ⁻¹)      ⟩
              1 * x + k * x   ≡⟨ distributivity-mult-over-nat' 1 k x ⁻¹ ⟩
              (1 + k) * x     ≡⟨ ap (_* x) (addition-commutativity 1 k) ⟩
              succ k * x ∎

mult-associativity : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
mult-associativity x y = induction base step
 where
  base : x * y * 0 ≡ x * (y * 0)
  base = x * y * 0   ≡⟨ refl ⟩
         (x * y) * 0 ≡⟨ refl ⟩
         0           ≡⟨ refl ⟩
         y * 0       ≡⟨ refl ⟩
         x * (y * 0) ∎
    
  step : (k : ℕ)
       → (x * y) * k      ≡ x * (y * k)
       → (x * y) * succ k ≡ x * (y * succ k)

  step k r = (x * y) * succ k          ≡⟨ refl                                        ⟩
             x * y + x * y * k         ≡⟨ ap ((x * y) +_) r                           ⟩
             x * y + x * (y * k)       ≡⟨ distributivity-mult-over-nat x y (y * k) ⁻¹ ⟩
             x * (y + y * k)           ≡⟨ refl                                        ⟩
             x * (y * succ k)          ∎

mult-rearrangement : (x y z : ℕ) → x * (y * z) ≡ y * (x * z)
mult-rearrangement x y z = x * (y * z)         ≡⟨ mult-associativity x y z ⁻¹ ⟩
                           x * y * z           ≡⟨ ap (_* z) (mult-commutativity x y) ⟩
                           y * x * z           ≡⟨ mult-associativity y x z ⟩
                           y * (x * z) ∎

pos-mult-is-succ : (x y : ℕ) → Σ z ꞉ ℕ , succ z ≡ succ x * succ y
pos-mult-is-succ x = induction base step
 where
  base : Σ z ꞉ ℕ , succ z ≡ succ x * 1
  base = x , refl

  step : (k : ℕ)
       → Σ z ꞉ ℕ , succ z ≡ succ x * succ k
       → Σ z' ꞉ ℕ , succ z' ≡ succ x * succ (succ k)
  step k (z , IH) = x + succ z , I
   where
    I : succ (x + succ z) ≡ succ x * succ (succ k)
    I = succ (x + succ z)               ≡⟨ succ-left x (succ z) ⁻¹ ⟩
        succ x + succ z                 ≡⟨ ap (succ x +_) IH ⟩
        succ x + (succ x + succ x * k)  ≡⟨ refl ⟩
        succ x * succ (succ k) ∎
        
ordering-multiplication-compatible : (m n k : ℕ) → m < n → m * succ k < n * succ k
ordering-multiplication-compatible m n = induction base step
 where
  base : m < n
       → succ m < succ n
  base i = i

  step : (k : ℕ)
       → (m < n → m * succ k < n * succ k)
       → m < n
       → m * succ (succ k) < n * succ (succ k)
  step k IH i = <-adding m n (m + m * k) (n + n * k) i (IH i)

ordering-multiplication-compatible' : (m n k : ℕ) → m ≤ n → m * k ≤ n * k
ordering-multiplication-compatible' m n = induction base step
 where
  base : m ≤ n → (m * 0) ≤ (n * 0)
  base l = zero-minimal 0

  step : (k : ℕ)
       → (m ≤ n → (m * k) ≤ (n * k))
       →  m ≤ n
       → (m * succ k) ≤ (n * succ k)
  step k IH l = ≤-adding m n (m * k) (n * k) l (IH l)

mult-right-cancellable : (x y z : ℕ) → (x * succ z) ≡ (y * succ z) → x ≡ y
mult-right-cancellable x y z e = tri-split (nat-order-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → x ≡ y
  tri-split (inl t)       = have less-than-not-equal (x * succ z) (y * succ z) (ordering-multiplication-compatible x y z t) which-contradicts e
  tri-split (inr (inl t)) = t
  tri-split (inr (inr t)) = have less-than-not-equal (y * succ z) (x * succ z) (ordering-multiplication-compatible y x z t) which-contradicts (e ⁻¹)
      
mult-left-cancellable : (x y z : ℕ) → succ z * x ≡ succ z * y → x ≡ y
mult-left-cancellable x y z r = mult-right-cancellable x y z lemma₀
 where
  lemma₀ : x * succ z ≡ y * succ z
  lemma₀ = x * succ z ≡⟨ mult-commutativity x (succ z)  ⟩
           succ z * x ≡⟨ r                              ⟩
           succ z * y ≡⟨ mult-commutativity (succ z) y  ⟩
           y * succ z ∎

mult-cancellable : (x y z : ℕ) → (x * succ z ≡ y * succ z)
                                ∔ (succ z * x ≡ succ z * y)
                                ∔ (succ z * x ≡ y * succ z)
                                ∔ (x * succ z ≡ succ z * y)
                               → x ≡ y
mult-cancellable x y z (inl e)             = mult-right-cancellable x y z e
mult-cancellable x y z (inr (inl e))       = mult-right-cancellable x y z (transport₂ (λ k k' → k ≡ k') (mult-commutativity (succ z) x) (mult-commutativity (succ z) y) e)
mult-cancellable x y z (inr (inr (inl e))) = mult-right-cancellable x y z (transport (_≡ y * succ z) (mult-commutativity (succ z) x) e)
mult-cancellable x y z (inr (inr (inr e))) = mult-right-cancellable x y z (transport (x * succ z ≡_) (mult-commutativity (succ z) y) e)

product-less-than-cancellable : (x y z : ℕ) → x * (succ y) ≤ z → x ≤ z
product-less-than-cancellable x = induction base step
 where
  base : (z : ℕ) → x * 1 ≤ z → x ≤ z
  base z l = l

  step : (k : ℕ)
       → ((z : ℕ) → (x * succ k) ≤ z → x ≤ z)
       → (z : ℕ)
       → x * succ (succ k) ≤ z
       → x ≤ z
  step k IH z l₁ = IH z (≤-trans (x * (succ k)) (x * (succ (succ k))) z I l₁)
   where
    I : (x * succ k) ≤ (x + x * succ k)
    I = ≤-+' x (x * (succ k))

less-than-pos-mult : (x y z : ℕ) → x < y → x < y * succ z
less-than-pos-mult x y z l = <-+ x y (y * z) l

ℕ-positive-multiplication-not-zero : (x y : ℕ) → ¬ (succ x * succ y ≡ 0)
ℕ-positive-multiplication-not-zero x = induction base step
 where
  base : ¬ (succ x * 1 ≡ 0)
  base e = 𝟘-elim (positive-not-zero x e) 

  step : (k : ℕ) → ¬ (succ x * succ k ≡ 0) → ¬ (succ x * succ (succ k) ≡ 0)
  step k IH e = IH I
   where
    I : succ x + succ x * k ≡ 0
    I = sum-to-zero-gives-zero (succ x) (succ x + succ x * k) e

succ-pred-multiplication : (x y : ℕ) → succ x * succ y ≡ succ (pred (succ x * succ y))
succ-pred-multiplication x y = succ-pred' (succ x * succ y) (ℕ-positive-multiplication-not-zero x y) ⁻¹

\end{code}
