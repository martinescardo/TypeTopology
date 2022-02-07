Andrew Sneap - 27th April 2021

In this file I prove some properties related to the order of Natural Numbers.

I build upon the work in the NaturalsOrder file.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import DecidableAndDetachable --TypeTopology
open import NaturalsAddition --TypeTopology
open import NaturalsOrder --TypeTopology
open import OrderNotation
open import UF-Base

module NaturalsOrderExtended where

≤-trans₂ : (x y u v : ℕ) → x ≤ y → y ≤ u → u ≤ v → x ≤ v
≤-trans₂ x y u v l₁ l₂ = ≤-trans x u v I
 where
  I : x ≤ u
  I = ≤-trans x y u l₁ l₂

<-trans₂ : (x y u v : ℕ) → x < y → y < u → u < v → x < v
<-trans₂ x y u v l₁ l₂ = <-trans x u v I 
 where
  I : x < u
  I = <-trans x y u l₁ l₂

nat-order-trichotomous : (x y : ℕ) → (x < y) ∔ (x ≡ y) ∔ (y < x)
nat-order-trichotomous 0        0        = inr (inl refl)
nat-order-trichotomous 0        (succ y) = inl (zero-minimal y)
nat-order-trichotomous (succ x) 0        = inr (inr (zero-minimal x))
nat-order-trichotomous (succ x) (succ y) = tri-split (nat-order-trichotomous x y)
 where
  tri-split : (x < y) ∔ (x ≡ y) ∔ (y < x) → (succ x < succ y) ∔ (succ x ≡ succ y) ∔ (succ y < succ x)
  tri-split (inl z)       = inl z
  tri-split (inr (inl z)) = inr (inl (ap succ z))
  tri-split (inr (inr z)) = inr (inr z)

≤-n-monotone-right : (x y z : ℕ) → x ≤ y → (x + z) ≤ (y + z)
≤-n-monotone-right x y 0        l = l
≤-n-monotone-right x y (succ n) l = ≤-n-monotone-right x y n l

≤-n-monotone-left : (x y z : ℕ) → x ≤ y → (z + x) ≤ (z + y)
≤-n-monotone-left x y z l = transport₂ _≤_ (addition-commutativity x z) (addition-commutativity y z) (≤-n-monotone-right x y z l)

≤-adding : (x y u v : ℕ) → x ≤ y → u ≤ v → (x + u) ≤ (y + v)
≤-adding x y u v l₁ l₂ = ≤-trans (x + u) (y + u) (y + v) (≤-n-monotone-right x y u l₁) (≤-n-monotone-left u v y l₂)

<-succ-monotone : (x y : ℕ) → x < y → succ x < succ y
<-succ-monotone x y = id

<-n-monotone-right : (x y z : ℕ) → x < y → (x + z) < (y + z)
<-n-monotone-right x y  0       l = l
<-n-monotone-right x y (succ z) l = <-n-monotone-right x y z l
    
<-n-monotone-left : (x y z : ℕ) → x < y → (z + x) < (z + y)
<-n-monotone-left x y z l = transport₂ _<_ (addition-commutativity x z) (addition-commutativity y z) (<-n-monotone-right x y z l)

<-adding : (x y u v : ℕ) → x < y → u < v → (x + u) < (y + v)
<-adding x y u v l₁ l₂ = <-trans (x + u) (y + u) (y + v) (<-n-monotone-right x y u l₁) (<-n-monotone-left u v y l₂)

<-+ : (x y z : ℕ) → x < y → x < y + z
<-+ x y z l₁ = ≤-trans (succ x) y (y + z) l₁ l₂
 where
  l₂ : y ≤ y + z
  l₂ = ≤-+ y z

equal-gives-less-than-or-equal : (x y : ℕ) → x ≡ y → x ≤ y
equal-gives-less-than-or-equal x y p = transport (_≤ y) (p ⁻¹) (≤-refl y)

less-than-not-equal : (x y : ℕ) → x < y → ¬ (x ≡ y)
less-than-not-equal x y r p = less-not-bigger-or-equal x y r (equal-gives-less-than-or-equal y x (p ⁻¹))

less-than-one-is-zero : (x : ℕ) → x < 1 → x ≡ 0
less-than-one-is-zero 0        l = refl
less-than-one-is-zero (succ x) l = 𝟘-elim l

not-less-or-equal-is-bigger : (x y : ℕ) → ¬(x ≤ y) → y < x
not-less-or-equal-is-bigger 0        y        l = l (zero-minimal y)
not-less-or-equal-is-bigger (succ x) 0        l = zero-minimal x
not-less-or-equal-is-bigger (succ x) (succ y) l = not-less-or-equal-is-bigger x y l

≤-dichotomous : (x y : ℕ) → x ≤ y ∔ y ≤ x
≤-dichotomous zero     y        = inl ⋆
≤-dichotomous (succ x) zero     = inr ⋆
≤-dichotomous (succ x) (succ y) = ≤-dichotomous x y

≥-dichotomy : (x y : ℕ) → x ≥ y ∔ x ≤ y
≥-dichotomy 0        y        = inr (zero-minimal y)
≥-dichotomy (succ x) 0        = inl (zero-minimal (succ x))
≥-dichotomy (succ x) (succ y) = ≥-dichotomy x y

subtraction' : (x y : ℕ) → x < y → Σ z ꞉ ℕ , (z + x ≡ y)
subtraction' 0        0        l = 𝟘-induction l
subtraction' 0        (succ y) l = (succ y) , refl
subtraction' (succ x) (succ y) l = pr₁ IH , ap succ (pr₂ IH)
 where
  IH : Σ z ꞉ ℕ , z + x ≡ y 
  IH = subtraction' x y l

subtraction'' : (x y : ℕ) → x < y → Σ z ꞉ ℕ , ((succ z) + x ≡ y)
subtraction'' 0        0        l = 𝟘-elim l
subtraction'' 0        (succ y) l = y , refl
subtraction'' (succ x) 0        l = 𝟘-elim l
subtraction'' (succ x) (succ y) l = z , ap succ e
 where
  I : Σ z ꞉ ℕ , succ z + x ≡ y
  I = subtraction'' x y l

  z : ℕ
  z = pr₁ I

  e : succ z + x ≡ y
  e = pr₂ I

least-element-unique : {A : ℕ → 𝓤 ̇} → (σ : detachable A)
                                      → ((α , αₚ) : Σ k ꞉ ℕ , A k × ((z : ℕ) → A z → k ≤ z))
                                      → ((β , βₚ) : Σ n ꞉ ℕ , A n × ((z : ℕ) → A z → n ≤ z))
                                      → α ≡ β
least-element-unique σ (α , α₀ , α₁) (β , β₀ , β₁) = ≤-anti α β I II
 where
  I : α ≤ β
  I = α₁ β β₀

  II : β ≤ α
  II = β₁ α α₀
    
least-element-unique' : {A : ℕ → 𝓤 ̇} → (σ : detachable A)
                                       → (x y : ℕ)
                                       → (δ : Σ A) → x ≡ pr₁ (minimal-from-given A σ δ) → y ≡ pr₁ (minimal-from-given A σ δ)
                                       → x ≡ y
least-element-unique' σ x y δ e₁ e₂ = e₁ ∙ e₂ ⁻¹

order-split : (x y : ℕ) → (x < y) ∔ (x ≥ y)
order-split 0        0        = inr (zero-minimal 0)
order-split 0        (succ y) = inl (zero-minimal (succ y))
order-split (succ x) 0        = inr (zero-minimal (succ x))
order-split (succ x) (succ y) = order-split x y

\end{code}

In the following functions, following a similar strategy employed in NaturalsOrder to prove bounded minimisation, I implement bounded maximisation of properties of Natural Numbers. That is, given a property of the natural numbers, and a proof that the property holds for some n : ℕ, I can produce a maximal m such that the property holds for m.

\begin{code}

bounded-maximisation : (A : ℕ → 𝓤 ̇) → detachable A
                     → (k : ℕ)
                     → (Σ m ꞉ ℕ , (m < k × A m × ((n : ℕ) → n < k → A n → n ≤ m))) ∔ ((n : ℕ) → A n → n ≥ k) 
bounded-maximisation A δ zero = inr (λ n a → zero-minimal n)
bounded-maximisation A δ (succ k) = f (bounded-maximisation A δ k)
 where
  conclusion = (Σ m ꞉ ℕ , (m < succ k) × A m × ((n : ℕ) → n < succ k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ succ k)
  
  f : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → n < k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ k)
    → conclusion
  f (inl (m , l , a , ψ)) = g (δ k)
   where
    g : A k ∔ ¬ A k → conclusion 
    g (inl k-holds) = inl (k , ((<-succ k) , (k-holds , ψ')))
     where
       ψ' : (n : ℕ) → n < succ k → A n → n ≤ k
       ψ' n z a' = z
    g (inr k-fails) = inl (m , ((<-trans m k (succ k) l (<-succ k)) , a , ψ'))
     where
      ψ' : (n : ℕ) → n < succ k → A n → n ≤ m
      ψ' n z a' = ψ n (ρ (<-split n k z)) a'
       where
        ρ : (n < k) ∔ (n ≡ k) → n < k
        ρ (inl r) = r
        ρ (inr r) = 𝟘-elim (k-fails (transport (λ - → A -) r a'))
  f (inr ω) = g (δ k)
   where
    g : A k ∔ ¬ A k → conclusion
    g (inl k-holds) = inl (k , (<-succ k , k-holds , (λ z l a' → l)))
    g (inr k-fails) = inr ψ
     where
      ψ : (n : ℕ) → A n → n ≥ succ k
      ψ n n-holds = τ (<-split k n (ω n n-holds))
       where
        τ : (k < n) ∔ (k ≡ n) → n ≥ succ k
        τ (inr w) = 𝟘-elim (k-fails (transport (λ - → A -) (w ⁻¹) n-holds))
        τ (inl w) = w

bounded-maximisation' : (A : ℕ → 𝓤 ̇) → detachable A
   → (k : ℕ)
   → (Σ m ꞉ ℕ , (m ≤ k × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m))) ∔ ((n : ℕ) → A n → n > k)
bounded-maximisation' A δ k = result (bounded-maximisation A δ k) (δ k)
 where
  result : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → n < k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ k) → A k ∔ ¬ A k
         → (Σ m ꞉ ℕ , (m ≤ k) × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n > k)
  result (inl z) (inl k-holds) = inl (k , (≤-refl k , (k-holds , (λ _ t _ → t))))
  result (inr z) (inl k-holds) = inl (k , ≤-refl k , k-holds , (λ _ t _ → t))
  result (inl (m , l , a , ψ)) (inr k-fails) = inl (m , (<-coarser-than-≤ m k l) , a , g)
   where
    g : (n : ℕ) → n ≤ k → A n → n ≤ m
    g n l' a' = ψ n (h (<-split n k l')) a'
     where
      h : (n < k) ∔ (n ≡ k) → n < k
      h (inl j) = j
      h (inr j) = 𝟘-elim (k-fails (transport (λ - → A -) j a'))
  result (inr z) (inr k-fails) = inr f
   where
    f : (n : ℕ) → A n → n > k
    f n a = g (<-split k n (z n a)) 
     where
      g : (k < n) ∔ (k ≡ n) → n > k
      g (inl j) = j
      g (inr j) = 𝟘-elim (k-fails (transport (λ - → A -) (j ⁻¹) a))
  
-- type of maximal element m : ℕ such that A m holds, given an upper bound

maximal-element : (A : ℕ → 𝓤 ̇) → (k : ℕ) → 𝓤 ̇
maximal-element A k = Σ m ꞉ ℕ , (m < k × A m × ((n : ℕ) → n < k → A n → n ≤ m))

maximal-element' : (A : ℕ → 𝓤 ̇) → (k : ℕ) → 𝓤 ̇
maximal-element' A k = Σ m ꞉ ℕ , (m ≤ k × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m))

--with bound b

maximal-from-given : (A : ℕ → 𝓤 ̇) → (b : ℕ) → detachable A → Σ k ꞉ ℕ , A k × k < b → maximal-element A b
maximal-from-given A b δ (k , a) = f (bounded-maximisation A δ b)
 where
  f : (Σ m ꞉ ℕ , (m < b) × A m × ((n : ℕ) → n < b → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n ≥ b) → maximal-element A b
  f (inl x) = x
  f (inr x) = 𝟘-elim (less-not-bigger-or-equal k b (pr₂ a) (x k (pr₁ a)))

maximal-from-given' : (A : ℕ → 𝓤 ̇) → (b : ℕ) → detachable A → Σ k ꞉ ℕ , A k × k ≤ b → maximal-element' A b
maximal-from-given' A b δ (k , a , c) = f (bounded-maximisation' A δ b)
 where
  f : (Σ m ꞉ ℕ , (m ≤ b) × A m × ((n : ℕ) → n ≤ b → A n → n ≤ m)) ∔ ((n : ℕ) → A n → n > b) → maximal-element' A b
  f (inr x) = 𝟘-elim (bigger-or-equal-not-less k b c (x k a))
  f (inl x) = x



\end{code}
