Andrew Sneap, November 2021

In this file I define the limit for sequences of rational numbers,
and prove that 2/3^n converges by first proving the sandwich theorem,
and that 1/(n+1) converges to 0.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Abs
open import Rationals.MinMax hiding (min ; max)
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Positive hiding (_+_ ; _*_)
open import Rationals.FractionsOrder
open import Rationals.FractionsOperations renaming (_*_ to _𝔽*_) hiding (abs ; -_ ; _+_)
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Division
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Order
open import Naturals.Properties
open import Integers.Type hiding (abs)
open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Order
open import Integers.Multiplication renaming (_*_ to _ℤ*_)

module Rationals.Limits
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
 where

open import MetricSpaces.Rationals fe pe pt
open import MetricSpaces.Type fe pe pt

_⟶_ : (f : ℕ → ℚ) → (L : ℚ) → 𝓤₀ ̇
f ⟶ L = (ε₊@(ε , _) : ℚ₊) → Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → abs (f n - L) < ε)

sandwich-theorem : (L : ℚ)
                 → (f g h : ℕ → ℚ)
                 → Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → f n ≤ g n ≤ h n)
                 → f ⟶ L
                 → h ⟶ L
                 → g ⟶ L
sandwich-theorem L f g h (N , α) f⟶L h⟶L = γ
 where
  γ : g ⟶ L
  γ ε₊@(ε , _) = γ' (f⟶L ε₊) (h⟶L ε₊)
   where
    γ' : Σ N₁ ꞉ ℕ , ((n : ℕ) → N₁ ≤ n → abs (f n - L) < ε)
       → Σ N₂ ꞉ ℕ , ((n : ℕ) → N₂ ≤ n → abs (h n - L) < ε)
       → Σ M ꞉ ℕ , ((n : ℕ) → M ≤ n → abs (g n - L) < ε)
    γ' (N₁ , β) (N₂ , δ) = M , γ''
     where
      M : ℕ
      M = max (max N₁ N₂) N

      I : N ≤ M
      I = max-≤-upper-bound' N (max N₁ N₂)

      II : N₁ ≤ max N₁ N₂
      II = max-≤-upper-bound N₁ N₂

      III : N₂ ≤ max N₁ N₂
      III = max-≤-upper-bound' N₂ N₁

      IV : max N₁ N₂ ≤ M
      IV = max-≤-upper-bound (max N₁ N₂) N

      V : N₁ ≤ M
      V = ≤-trans N₁ (max N₁ N₂) M II IV

      VI : N₂ ≤ M
      VI = ≤-trans N₂ (max N₁ N₂) M III IV

      γ'' : (n : ℕ) → max (max N₁ N₂) N ≤ n → abs (g n - L) < ε
      γ'' n l = ℚ<-to-abs (g n - L) ε (γ₁ , γ₂)
       where
        VII : - ε < f n - L < ε
        VII = ℚ-abs-<-unpack (f n - L) ε (β n (≤-trans N₁ M n V l))

        VIII : - ε < h n - L < ε
        VIII = ℚ-abs-<-unpack (h n - L) ε (δ n (≤-trans N₂ M n VI l))

        l₁ : f n ≤ g n ≤ h n
        l₁ = α n (≤-trans N (max (max N₁ N₂) N) n I l)

        IX : f n - L ≤ g n - L
        IX = ℚ≤-addition-preserves-order (f n) (g n) (- L) (pr₁ l₁)

        X : g n - L ≤ h n - L
        X = ℚ≤-addition-preserves-order (g n) (h n) (- L) (pr₂ l₁)

        γ₁ : - ε < g n - L
        γ₁ = ℚ<-≤-trans (- ε) (f n - L) (g n - L) (pr₁ VII) IX

        γ₂ : g n - L < ε
        γ₂ = ℚ≤-<-trans (g n - L) (h n - L) ε X (pr₂ VIII)

0f : ℕ → ℚ
0f _ = 0ℚ

0f-converges : 0f ⟶ 0ℚ
0f-converges ε₊@(ε , 0<ε) = 0 , (λ n _ → 0<ε)

constant-sequence : (q : ℚ) → (n : ℕ) → ℚ
constant-sequence q n = q

constant-sequence-converges : (q : ℚ) → (constant-sequence q) ⟶ q
constant-sequence-converges q (ε , 0<ε) = 0 , γ
 where
  γ : (n : ℕ) → 0 ≤ n → abs (constant-sequence q n - q) < ε
  γ n _ = transport (_< ε) I 0<ε
   where
    I : 0ℚ ＝ abs (constant-sequence q n - q)
    I = ℚ-zero-dist q ⁻¹

⟨2/3⟩^_ : ℕ → ℚ
⟨2/3⟩^ 0         = toℚ (pos 1 , 0)
⟨2/3⟩^ (succ n)  = rec 2/3 (_* 2/3) n

⟨2/3⟩-to-mult : (n : ℕ) → ⟨2/3⟩^ (succ n) ＝ (⟨2/3⟩^ n) * 2/3
⟨2/3⟩-to-mult 0 = refl
⟨2/3⟩-to-mult (succ n) = refl

⟨2/3⟩^n-positive : (n : ℕ) → 0ℚ < (⟨2/3⟩^ n)
⟨2/3⟩^n-positive 0 = 0 , refl
⟨2/3⟩^n-positive (succ n) = transport (0ℚ <_) γ II
 where
  I : 0ℚ < (⟨2/3⟩^ n)
  I = ⟨2/3⟩^n-positive n

  II : 0ℚ < (⟨2/3⟩^ n) * 2/3
  II = ℚ<-pos-multiplication-preserves-order (⟨2/3⟩^ n) 2/3 I (1 , refl)

  γ : (⟨2/3⟩^ n) * 2/3 ＝ (⟨2/3⟩^ (succ n))
  γ = ⟨2/3⟩-to-mult n ⁻¹

⟨2/3⟩-all-positive : (n : ℕ) → 0ℚ ≤ (⟨2/3⟩^ n)
⟨2/3⟩-all-positive n = γ
 where
  I : 0ℚ < (⟨2/3⟩^ n)
  I = ⟨2/3⟩^n-positive n

  γ : 0ℚ ≤ (⟨2/3⟩^ n)
  γ = ℚ<-coarser-than-≤ 0ℚ (⟨2/3⟩^ n) I

⟨1/n⟩ : ℕ → ℚ
⟨1/n⟩ n = toℚ (pos 1 , n)

⟨1/sn⟩ : ℕ → ℚ
⟨1/sn⟩ 0 = 1ℚ
⟨1/sn⟩ (succ n) = ⟨1/n⟩ n

⟨1/n⟩-1 : ⟨1/n⟩ 0 ＝ 1ℚ
⟨1/n⟩-1 = refl

⟨1/n⟩-1/2 : ⟨1/n⟩ 1 ＝ 1/2
⟨1/n⟩-1/2 = refl

⟨1/2⟩^_ : ℕ → ℚ
⟨1/2⟩^ 0         = toℚ (pos 1 , 0)
⟨1/2⟩^ (succ n)  = rec (1/2) (_* 1/2) n

⟨1/sn⟩-converges-lemma : (a n x q r : ℕ)
                       → succ a ＝ q ℕ* succ x ℕ+ r
                       → r < succ x
                       → succ q ≤ succ n
                       → pos (succ a) < pos (succ n) ℤ* pos (succ x)
⟨1/sn⟩-converges-lemma a n x q r e l₁ l₂ = γ
 where
  x' = succ x
  q' = succ q
  a' = succ a
  n' = succ n

  I : pos r < pos x'
  I = ℕ-order-respects-ℤ-order r x' l₁

  II : pos (q ℕ* x') ℤ+ pos r < pos (q ℕ* x') ℤ+ pos x'
  II = ℤ<-adding-left (pos r) (pos x') (pos (q ℕ* x')) I

  III : pos (q ℕ* x') ℤ+ pos r ＝ pos a'
  III = pos (q ℕ* x') ℤ+ pos r ＝⟨ distributivity-pos-addition (q ℕ* x') r ⟩
        pos (q ℕ* x' ℕ+ r)     ＝⟨ ap pos (e ⁻¹)                           ⟩
        pos a'               ∎

  IV : pos (q ℕ* x') ℤ+ pos x' ＝ pos q' ℤ* pos x'
  IV = pos (q ℕ* x') ℤ+ pos x' ＝⟨ i   ⟩
       pos x' ℤ+ pos (q ℕ* x') ＝⟨ ii  ⟩
       pos x' ℤ+ pos (x' ℕ* q) ＝⟨ iii ⟩
       pos x' ℤ* pos q'        ＝⟨ iv  ⟩
       pos q' ℤ* pos x'        ∎
   where
    i   = ℤ+-comm (pos (q ℕ* x')) (pos x')
    ii  = ap (λ ■ → pos x' ℤ+ (pos ■)) (mult-commutativity q x')
    iii = ap (pos x' ℤ+_) (pos-multiplication-equiv-to-ℕ x' q ⁻¹)
    iv  = ℤ*-comm (pos x') (pos q')

  V : pos a' < pos q' ℤ* pos x'
  V = transport₂ _<_ III IV II

  VI : pos q' ≤ pos n'
  VI = ℕ≤-to-ℤ≤ q' n' l₂

  VII : pos q' ℤ* pos x' ≤ pos n' ℤ* pos x'
  VII = positive-multiplication-preserves-order' (pos q') (pos n') (pos x') ⋆ VI

  γ : pos a' < pos n' ℤ* pos x'
  γ = ℤ<-≤-trans (pos a') (pos q' ℤ* pos x') (pos n' ℤ* pos x') V VII

⟨1/sn⟩-converges : ⟨1/sn⟩ ⟶ 0ℚ
⟨1/sn⟩-converges (ε@((pos 0 , a) , p) , 0<ε) = 𝟘-elim γ
 where
  I : ε ＝ 0ℚ
  I = numerator-zero-is-zero ((pos 0 , a) , p) refl

  II : 0ℚ < 0ℚ
  II = transport (0ℚ <_) I 0<ε

  γ : 𝟘
  γ = ℚ<-irrefl 0ℚ II
⟨1/sn⟩-converges ε₊@(((negsucc x , a) , p) , 0<ε) = 𝟘-elim γ
 where
  γ : 𝟘
  γ = negative-not-greater-than-zero x a 0<ε
⟨1/sn⟩-converges ε₊@(((pos (succ x) , a) , p) , 0<ε) = γ (division (succ a) x)
 where
  γ : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ＝ q ℕ* succ x ℕ+ r) × (r < succ x)
    → Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → abs (⟨1/sn⟩ n - 0ℚ) < ε₊)
  γ (q , r , e , l₁) = succ q , γ'
   where
    γ' : (n : ℕ)
       → succ q < succ n
       → abs (⟨1/sn⟩ n - 0ℚ) <ℚ ((pos (succ x) , a) , p)
    γ' 0 l₂ = 𝟘-elim l₂
    γ' (succ n) l₂ = γ''
     where
      I : pos 0 ＝ pos 0 ℤ* pos (succ n)
      I = ℤ-zero-left-base (pos (succ n)) ⁻¹

      II : pos 0 ℤ* pos (succ n) < pos 1
      II = transport (_< pos 1) I (0 , refl)

      III : 0ℚ < toℚ (pos 1 , n)
      III = toℚ-< (pos 0 , 0) (pos 1 , n) II

      IV : toℚ (pos 1 , n) ＝ abs (⟨1/n⟩ n + 0ℚ)
      IV = toℚ (pos 1 , n)       ＝⟨ i  ⟩
           abs (toℚ (pos 1 , n)) ＝⟨ ii ⟩
           abs (⟨1/n⟩ n + 0ℚ)    ∎
       where
        i  = abs-of-pos-is-pos' (toℚ (pos 1 , n)) III ⁻¹
        ii = ap abs (ℚ-zero-right-neutral (⟨1/n⟩ n)) ⁻¹

      V : toℚ (pos (succ x) , a) ＝ ((pos (succ x) , a) , p)
      V = toℚ-to𝔽 ((pos (succ x) , a) , p) ⁻¹

      VI : pos (succ a) < pos (succ n) ℤ* pos (succ x)
      VI = ⟨1/sn⟩-converges-lemma a n x q r e l₁ l₂

      VII : (pos 1 , n) 𝔽< (pos (succ x) , a)
      VII = positive-order-flip a n x 0 VI

      VIII : toℚ (pos 1 , n) < toℚ (pos (succ x) , a)
      VIII = toℚ-< (pos 1 , n) (pos (succ x) , a) VII

      γ'' : abs (⟨1/n⟩ n - 0ℚ) <ℚ ((pos (succ x) , a) , p)
      γ'' = transport₂ _<_ IV V VIII

⟨1/sn⟩-bounds-⟨2/3⟩-lemma : (n : ℕ)
                          → (⟨1/sn⟩ (succ (succ n))) * 2/3
                          ≤ ⟨1/sn⟩ (succ (succ (succ n)))
⟨1/sn⟩-bounds-⟨2/3⟩-lemma n = γ
 where
  n+2 = succ (succ n)
  n+3 = succ (n+2)

  1' = pos 1
  2' = pos 2
  3' = pos 3
  6' = pos 6
  n' = pos n

  I : 2' ℤ* n' ℤ+ 6' ＝ 2' ℤ* pos (n ℕ+ 3)
  I = 2' ℤ* n' ℤ+ 6'      ＝⟨ distributivity-mult-over-ℤ' n' 3' 2' ⁻¹       ⟩
      2' ℤ* (n' ℤ+ 3')    ＝⟨ ap (2' ℤ*_) (distributivity-pos-addition n 3) ⟩
      2' ℤ* pos (n ℕ+ 3)  ∎

  II : 3' ℤ* n' ℤ+ 6' ＝ 1' ℤ* pos (succ (pred (n+2 ℕ* 3)))
  II = 3' ℤ* n' ℤ+ 6'                     ＝⟨ i   ⟩
       pos (3 ℕ* n) ℤ+ 6'                 ＝⟨ ii  ⟩
       pos (3 ℕ* n ℕ+ 6)                  ＝⟨ iii ⟩
       pos (3 ℕ* n+2)                     ＝⟨ iv  ⟩
       pos (n+2 ℕ* 3)                     ＝⟨ v   ⟩
       pos (succ (pred (n+2 ℕ* 3)))       ＝⟨ vi  ⟩
       1' ℤ* pos (succ (pred (n+2 ℕ* 3))) ∎
   where
    i   = ap (_ℤ+ 6') (pos-multiplication-equiv-to-ℕ 3 n)
    ii  = distributivity-pos-addition (3 ℕ* n) 6
    iii = ap pos (distributivity-mult-over-addition 3 n 2 ⁻¹)
    iv  = ap pos (mult-commutativity 3 n+2)
    v   = ap pos (succ-pred-multiplication (succ n) 2)
    vi  = ℤ-mult-left-id _ ⁻¹

  III : pos 0 ≤ n'
  III = ℤ-zero-least-pos n

  IV : 2' ℤ* n' ≤ 3' ℤ* n'
  IV = ℤ*-multiplication-order 2' 3' n' III (1 , refl)

  V : 2' ℤ* n' ℤ+ 6' ≤ 3' ℤ* n' ℤ+ 6'
  V = ℤ≤-adding' (2' ℤ* n') (3' ℤ* n') 6' IV

  VI : 2' ℤ* pos n+3 ≤ 1' ℤ* pos (succ (pred (n+2 ℕ* 3)))
  VI = transport₂ _≤_ I II V

  VII : toℚ ((1' , succ n) 𝔽* (2' , 2)) ≤ toℚ (1' , n+2)
  VII = toℚ-≤ ((1' , succ n) 𝔽* (2' , 2)) (1' , n+2) VI

  VIII : toℚ ((1' , succ n) 𝔽* (2' , 2)) ＝ toℚ (1' , succ n) * 2/3
  VIII = toℚ-* (1' , succ n) (2' , 2)

  γ : (⟨1/sn⟩ n+2) * 2/3 ≤ ⟨1/sn⟩ n+3
  γ = transport (_≤ ⟨1/sn⟩ n+3) VIII VII

⟨1/sn⟩-bounds-⟨2/3⟩ : (n : ℕ) → (⟨2/3⟩^ n) ≤ ⟨1/sn⟩ n
⟨1/sn⟩-bounds-⟨2/3⟩ = induction base step
 where
  base : 1ℚ ≤ 1ℚ
  base = 0 , refl

  step : (n : ℕ) → (⟨2/3⟩^ n) ≤ (⟨1/sn⟩ n) → (⟨2/3⟩^ succ n) ≤ ⟨1/sn⟩ (succ n)
  step 0 IH = 1 , refl
  step 1 IH = 1 , refl
  step (succ (succ n)) IH = γ
   where
    S₁⦅n+2⦆ = ⟨2/3⟩^ (succ (succ n))
    S₁⦅n+3⦆ = ⟨2/3⟩^ (succ (succ (succ n)))
    S₂⦅n+2⦆ = ⟨1/sn⟩ (succ (succ n))
    S₂⦅n+3⦆ = ⟨1/sn⟩ (succ (succ (succ n)))

    I : S₁⦅n+2⦆ * 2/3 ≤ S₂⦅n+2⦆ * 2/3
    I = ℚ≤-pos-multiplication-preserves-order' S₁⦅n+2⦆ S₂⦅n+2⦆  2/3 IH (2 , refl)

    II : S₂⦅n+2⦆ * 2/3 ≤ S₂⦅n+3⦆
    II = ⟨1/sn⟩-bounds-⟨2/3⟩-lemma n

    γ : S₁⦅n+3⦆ ≤ S₂⦅n+3⦆
    γ = ℚ≤-trans (S₁⦅n+2⦆ * 2/3) (S₂⦅n+2⦆ * 2/3) S₂⦅n+3⦆ I II

⟨2/3⟩^n-squeezed : Σ N ꞉ ℕ  , ((n : ℕ) → (N ≤ n) → (0f n ≤ ⟨2/3⟩^ n ≤ ⟨1/sn⟩ n))
⟨2/3⟩^n-squeezed = 1 , γ
 where
  γ : (n : ℕ) → 1 ≤ n → (0f n ≤ ⟨2/3⟩^ n ≤ ⟨1/sn⟩ n)
  γ n l = γ₁ , γ₂
   where
    γ₁ : 0ℚ ≤ (⟨2/3⟩^ n)
    γ₁ = ⟨2/3⟩-all-positive n

    γ₂ : (⟨2/3⟩^ n) ≤ (⟨1/sn⟩ n)
    γ₂ = ⟨1/sn⟩-bounds-⟨2/3⟩ n

⟨2/3⟩^n-converges : ⟨2/3⟩^_ ⟶ 0ℚ
⟨2/3⟩^n-converges =
 sandwich-theorem
  0ℚ 0f ⟨2/3⟩^_ ⟨1/sn⟩
   ⟨2/3⟩^n-squeezed
   0f-converges
   ⟨1/sn⟩-converges

⟨2/3⟩^n<ε : (ε : ℚ₊) → Σ n ꞉ ℕ , (⟨2/3⟩^ n) < ε
⟨2/3⟩^n<ε ε = γ (⟨2/3⟩^n-converges ε)
 where
  γ : Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → abs ((⟨2/3⟩^ n) - 0ℚ) < ε)
    → Σ n ꞉ ℕ , (⟨2/3⟩^ n) < ε
  γ (N , f) = N , γ'
   where
    I : abs ((⟨2/3⟩^ N) - 0ℚ) < ε
    I = f N (≤-refl N)

    II : 0ℚ < (⟨2/3⟩^ N)
    II = ⟨2/3⟩^n-positive N

    III : abs ((⟨2/3⟩^ N) - 0ℚ) ＝ ⟨2/3⟩^ N
    III = abs ((⟨2/3⟩^ N) + 0ℚ) ＝⟨ ap abs (ℚ-zero-right-neutral (⟨2/3⟩^ N)) ⟩
          abs (⟨2/3⟩^ N)        ＝⟨ abs-of-pos-is-pos' (⟨2/3⟩^ N) II         ⟩
          (⟨2/3⟩^ N)            ∎

    γ' : (⟨2/3⟩^ N) < ε
    γ' = transport (_< ε) III I

⟨2/3⟩^n<ε-consequence : (ε (p , _) : ℚ₊) → Σ n ꞉ ℕ , (⟨2/3⟩^ n) * p < ε
⟨2/3⟩^n<ε-consequence (ε , 0<ε) (p , 0<p) = γ (⟨2/3⟩^n<ε (ε * p' , 0<εp'))
 where
  p-not-zero : ¬ (p ＝ 0ℚ)
  p-not-zero = ℚ<-positive-not-zero p 0<p

  p' : ℚ
  p' = ℚ*-inv p p-not-zero

  0<p' : 0ℚ < p'
  0<p' = ℚ-inv-preserves-pos p 0<p p-not-zero

  0<εp' : 0ℚ < ε * p'
  0<εp' = ℚ<-pos-multiplication-preserves-order ε p' 0<ε 0<p'

  γ : Σ n ꞉ ℕ , (⟨2/3⟩^ n) < ε * p'
    → Σ n ꞉ ℕ , (⟨2/3⟩^ n) * p < ε
  γ (n , l) = n , γ'
   where
    I : (⟨2/3⟩^ n) * p < ε * p' * p
    I = ℚ<-pos-multiplication-preserves-order' (⟨2/3⟩^ n) (ε * p') p l 0<p

    II : ε * p' * p ＝ ε
    II = ε * p' * p   ＝⟨ ℚ*-assoc ε p' p                             ⟩
         ε * (p' * p) ＝⟨ ap (ε *_) (ℚ*-comm p' p)                    ⟩
         ε * (p * p') ＝⟨ ap (ε *_) (ℚ*-inverse-product p p-not-zero) ⟩
         ε * 1ℚ       ＝⟨ ℚ-mult-right-id ε                           ⟩
         ε            ∎

    γ' : (⟨2/3⟩^ n) * p < ε
    γ' = transport ((⟨2/3⟩^ n) * p <_) II I

\end{code}
