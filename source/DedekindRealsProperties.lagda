Andrew Sneap
ra
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation --TypeTopology
open import UF-Base -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-Subsingletons -- TypeTopology
open import NaturalNumbers-Properties --TypeTopology

open import NaturalsOrder
open import Rationals
open import RationalsAbs
open import RationalsAddition
open import RationalsLimits
open import RationalsMultiplication
open import RationalsNegation
open import RationalsOrder

module DedekindRealsProperties
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
      where
open import DedekindReals pe pt fe
open import MetricSpaceRationals fe pt pe
open PropositionalTruncation pt

exists-2/3-n : (x y p : ℚ) → x < y → 0ℚ < p → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y - x)) < p)
exists-2/3-n x y (p , α) l₁ l₂ = V use-limit
 where
  p-convert : p , α ≡ toℚ p
  p-convert = toℚ-toℚₙ fe (p , α)
  I : ¬ (y - x ≡ 0ℚ)
  I e = ℚ<-not-itself x (transport (x <_) δ l₁)
   where
    δ : y ≡ x
    δ = y                  ≡⟨ ℚ-zero-right-neutral fe y ⁻¹ ⟩
        y + 0ℚ             ≡⟨ ap (y +_) (ℚ-inverse-sum-to-zero fe x ⁻¹) ⟩
        y + (x - x)        ≡⟨ ap (y +_) (ℚ+-comm x (- x)) ⟩
        y + ((- x) + x)    ≡⟨ ℚ+-assoc fe y (- x) x ⁻¹ ⟩
        y - x + x          ≡⟨ ap (_+ x) e ⟩
        0ℚ + x             ≡⟨ ℚ-zero-left-neutral fe x ⟩
        x                  ∎

  II : 0ℚ < y - x
  II = ℚ<-difference-positive fe x y l₁

  z = multiplicative-inverse fe (y - x) I
  
  III : 0ℚ < multiplicative-inverse fe (y - x) I
  III = multiplicative-inverse-preserves-pos fe (y - x) II I
     
  IV : 0ℚ < (toℚ p * multiplicative-inverse fe (y - x) I)
  IV = ℚ<-pos-multiplication-preserves-order (toℚ p) (multiplicative-inverse fe (y - x) I) (transport (0ℚ <_) p-convert l₂) III

  use-limit : Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → ℚ-metric (⟨2/3⟩^ n) 0ℚ < (toℚ p * multiplicative-inverse fe (y - x) I))
  use-limit = ⟨2/3⟩^n-converges fe pt pe (toℚ p * multiplicative-inverse fe (y - x) I) IV

  V : (Σ N ꞉ ℕ , ((n : ℕ) → N ≤ n → ℚ-metric (⟨2/3⟩^ n) 0ℚ < (toℚ p * multiplicative-inverse fe (y - x) I)))
     → Σ n ꞉ ℕ , (((⟨2/3⟩^ n) * (y - x)) < (p , α))
  V (N , f) = (succ N) , transport₂ _<_ VIII IX VII
   where
    abstract
     VI : ℚ-metric (⟨2/3⟩^ succ N) 0ℚ <ℚ (toℚ p * multiplicative-inverse fe (y - x) I)
     VI = f (succ N) (≤-succ N)
     VII : ℚ-metric  (⟨2/3⟩^ succ N) 0ℚ  * (y - x) <ℚ (toℚ p * multiplicative-inverse fe (y - x) I) * (y - x)
     VII = ℚ<-pos-multiplication-preserves-order' fe (ℚ-metric (⟨2/3⟩^ succ N) 0ℚ) ((toℚ p * multiplicative-inverse fe (y - x) I)) (y - x) VI II
     VIII : ℚ-metric (⟨2/3⟩^ succ N) 0ℚ * (y - x) ≡ ((⟨2/3⟩^ (succ N)) * (y - x))
     VIII = ap (_* (y - x)) i
      where
       i : ℚ-metric (⟨2/3⟩^ succ N) 0ℚ ≡ (⟨2/3⟩^ (succ N))
       i = ℚ-metric (⟨2/3⟩^ succ N) 0ℚ ≡⟨ by-definition ⟩
           abs ((⟨2/3⟩^ succ N) - 0ℚ)     ≡⟨ ap (λ β → abs ((⟨2/3⟩^ succ N) + β) ) (ℚ-minus-zero-is-zero ⁻¹) ⟩
           abs ((⟨2/3⟩^ succ N) + 0ℚ)     ≡⟨ ap abs (ℚ-zero-right-neutral fe ((⟨2/3⟩^ succ N))) ⟩
           abs (⟨2/3⟩^ succ N)            ≡⟨ abs-of-pos-is-pos fe (⟨2/3⟩^ succ N) (ℚ<-coarser-than-≤ 0ℚ (⟨2/3⟩^ succ N) (⟨2/3⟩^n-positive fe pt pe (succ N))) ⟩
           (⟨2/3⟩^ succ N) ∎
     IX : (toℚ p * multiplicative-inverse fe (y - x) I) * (y - x) ≡ (p , α)
     IX = toℚ p * multiplicative-inverse fe (y - x) I * (y - x)     ≡⟨ ap (λ γ → γ * (multiplicative-inverse fe (y - x) I) * (y - x)) (p-convert ⁻¹) ⟩
          (p , α) * multiplicative-inverse fe (y - x) I * (y - x)   ≡⟨ ℚ*-assoc fe (p , α) (multiplicative-inverse fe (y - x) I) (y - x) ⟩
          (p , α) * (multiplicative-inverse fe (y - x) I * (y - x)) ≡⟨ ap ((p , α) *_) (ℚ*-comm ((multiplicative-inverse fe (y - x) I)) (y - x)) ⟩
          (p , α) * ((y - x) * multiplicative-inverse fe (y - x) I) ≡⟨ ap ((p , α) *_) (ℚ*-inverse-product-is-one fe (y - x) I) ⟩
          (p , α) * 1ℚ ≡⟨ ℚ-mult-right-id fe (p , α) ⟩
          p , α ∎


ral-lemma : (α β : ℚ) → (n : ℕ) → β ≡ 2/3 * α → ((rec 2/3 (λ k → k * 2/3) n * 2/3) * α) ≡ (rec 2/3 (λ k → k * 2/3) n * β)
ral-lemma α β n e = ((rec 2/3 (λ k → k * 2/3) n * 2/3) * α) ≡⟨ refl ⟩
               (((⟨2/3⟩^ (succ (succ n))) * α) )            ≡⟨ ap (_* α) (I (succ n)) ⟩
               (((⟨2/3⟩^ succ n) * 2/3) * α)                ≡⟨ ℚ*-assoc fe (⟨2/3⟩^ (succ n)) 2/3 α ⟩
               ((⟨2/3⟩^ succ n) * (2/3 * α))                ≡⟨ ap ((⟨2/3⟩^ (succ n)) *_) (e ⁻¹) ⟩
               (rec 2/3 (λ k → k * 2/3) n * β)              ∎
 where
  I : (n : ℕ) → ⟨2/3⟩^ (succ n) ≡ ((⟨2/3⟩^ n) * 2/3)
  I zero = f
   where
    abstract
     f : ⟨2/3⟩^ (succ 0) ≡ ((⟨2/3⟩^ 0) * 2/3)
     f = (ℚ-mult-left-id fe 2/3) ⁻¹
  I (succ n) = refl


ℝ-arithmetically-located : (((L , R) , _) : ℝ)
                          → (p : ℚ)
                          → 0ℚ < p
                          → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × 0ℚ < (y - x) × (y - x) < p
ℝ-arithmetically-located ((L , R) , inhabited-left , inhabited-right , rounded-left , rounded-right , disjoint , located) p l = ∥∥-rec ∃-is-prop I (binary-choice inhabited-left inhabited-right)
 where
  I : (Σ x ꞉ ℚ , x ∈ L) × (Σ y ꞉ ℚ , y ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x) × (y - x) < p)
  I ((x , x-L) , (y , y-R)) = II x y x-L y-R (pr₁ γ) (trisect fe x y (disjoint x y (x-L , y-R))) (pr₂ γ) 
   where
    γ : Sigma ℕ (λ n → ((⟨2/3⟩^ n) * (y - x)) < p)
    γ = exists-2/3-n x y p (disjoint x y (x-L , y-R)) l
    
    II : (x y : ℚ) → x ∈ L → y ∈ R → (n : ℕ) → (Σ (x' , y') ꞉ ℚ × ℚ , x < x' × x' < y' × y' < y × ((y - x') ≡ (2/3 * (y - x))) × (y' - x ≡ 2/3 * (y - x)))
       → ((⟨2/3⟩^ n) * (y - x)) < p
       → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < (y - x)) × ((y - x) < p)
    II x y x-L y-R zero ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄            = ∣ (x , y) , x-L , y-R , α , β ∣
     where
      abstract
       α : 0ℚ <ℚ (y - x)
       α = ℚ<-difference-positive fe x y (disjoint x y (x-L , y-R))
       β : y - x <ℚ p
       β = transport (_<ℚ p) (ℚ-mult-left-id fe (y - x)) l₄
      
    II x y x-L y-R (succ zero) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄     = ∥∥-rec ∃-is-prop III (located x' y' l₂)
     where
      III : (x' ∈ L) ∔ (y' ∈ R) → ∃ (x , y) ꞉ ℚ × ℚ , x ∈ L × y ∈ R × (0ℚ < y - x × y - x < p)
      III (inl x'-L) = ∣ (x' , y) , x'-L , y-R , α , β ∣
       where
        abstract
         α : 0ℚ <ℚ y - x'
         α = ℚ<-difference-positive fe x' y (disjoint x' y (x'-L , y-R))
         β : y - x' <ℚ p
         β = transport (_<ℚ p) (e₁ ⁻¹) l₄
      III (inr y'-R) = ∣ (x , y') , x-L , y'-R , α , β ∣
       where
        abstract
         α : 0ℚ <ℚ y' - x
         α = ℚ<-difference-positive fe x y' (disjoint x y' (x-L , y'-R))
         β : y' - x <ℚ p
         β = transport (_<ℚ p) (e₂ ⁻¹) l₄
    II x y x-L y-R (succ (succ n)) ((x' , y') , l₁ , l₂ , l₃ , e₁ , e₂) l₄ =
      ∥∥-induction (λ _ → ∃-is-prop)
        (cases (λ x'-L → II x' y  x'-L y-R  (succ n) (trisect fe x' y (ℚ<-trans x' y' y l₂ l₃)) III)
               (λ y'-R → II x  y' x-L  y'-R (succ n) (trisect fe x y' (ℚ<-trans x x' y' l₁ l₂)) IV))
        (located x' y' l₂)
     where
      III : ((⟨2/3⟩^ succ n) * (y - x')) < p
      III = transport (_< p) (ral-lemma (y - x) (y - x') n e₁) l₄
      IV : ((⟨2/3⟩^ succ n) * (y' - x)) < p
      IV = transport (_< p) (ral-lemma (y - x) (y' - x) n e₂) l₄

\end{code}
