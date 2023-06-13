```
{-# OPTIONS --without-K --exact-split --safe #-}
            
open import Integers.Addition renaming (_+_ to _+ℤ_ ; _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Order
open import Notation.Order hiding (_≤_≤_)
open import UF.Base
open import UF.Subsingletons

module Thesis.Chapter5.PLDIPrelude where
```

ℤ-elimination

```agda
ℤ-elim : (P : ℤ → 𝓤 ̇ )
       → ((n : ℕ) → P (pos n)) → ((n : ℕ) → P (negsucc n))
       → Π P
ℤ-elim P Pp Pn (pos     n) = Pp n
ℤ-elim P Pp Pn (negsucc n) = Pn n
```

Monotone and rec properties

```agda
succ-to-monotone' : (P : ℤ → ℤ → 𝓤 ̇ )
                  → ((a : ℤ) → P a a)
                  → ((a b c : ℤ) → P a b → P b c → P a c)
                  → ((a : ℤ) → P a (succℤ a))
                  → (a b : ℤ) (n : ℕ) → a +pos n ＝ b → P a b
succ-to-monotone' P r t s a a zero refl = r a
succ-to-monotone' P r t s a b (succ n) refl
 = t a (succℤ a) b (s a)
     (succ-to-monotone' P r t s (succℤ a) (succℤ (a +pos n))
       n (ℤ-left-succ-pos a n))

succ-to-monotone : (P : ℤ → ℤ → 𝓤 ̇ )
                 → ((a : ℤ) → P a a)
                 → ((a b c : ℤ) → P a b → P b c → P a c)
                 → ((a : ℤ) → P a (succℤ a))
                 → (a b : ℤ) → a ≤ℤ b → P a b
succ-to-monotone P r t s a b (n , γ) = succ-to-monotone' P r t s a b n γ

≤-succ-to-monotone : (f : ℤ → ℤ) → ((a : ℤ) → f a ≤ℤ f (succℤ a))
                   → (a b : ℤ) → a ≤ℤ b → f a ≤ℤ f b
≤-succ-to-monotone f = succ-to-monotone (λ x y → f x ≤ℤ f y)
                         (λ x     → ℤ≤-refl  (f x))
                         (λ x y z → ℤ≤-trans (f x) (f y) (f z))

rec-to-monotone : (f g : ℤ → ℤ) → ((a b : ℤ) → a ≤ℤ b → f a ≤ℤ g b)
                → (a b : ℤ) (n : ℕ) → a ≤ℤ b → rec a f n ≤ℤ rec b g n
rec-to-monotone f g h a b zero a≤b
 = a≤b
rec-to-monotone f g h a b (succ n) a≤b
 = h (rec a f n) (rec b g n) (rec-to-monotone f g h a b n a≤b)

rec-f-＝ : {X : 𝓤 ̇ } → (f : X → X) (x : X) (n : ℕ)
        → rec (f x) f n ＝ rec x f (succ n) 
rec-f-＝ f x zero = refl
rec-f-＝ f x (succ n) = ap f (rec-f-＝ f x n)
```

Sign and num for integers

```agda
sign : ℤ → (ℕ → ℤ)
sign (pos     _) = pos
sign (negsucc _) = negsucc

num : ℤ → ℕ
num  (pos     n) = n
num  (negsucc n) = n
```

Natural number functions definitions and properties

```agda
_/2 : ℕ → ℕ
0 /2 = 0
1 /2 = 0
succ (succ n) /2 = succ (n /2)

_/2' : ℤ → ℤ
pos x     /2' = pos (x /2)
negsucc x /2' = ℤ- (pos (succ x /2))

_ℕ^_ : ℕ → ℕ → ℕ
a ℕ^ b = ((a ℕ*_) ^ b) 1

infixl 33 _ℕ^_ 

2^ : ℕ → ℕ
2^ = 2 ℕ^_

power-of-pos-positive : ∀ n → is-pos-succ (pos (2^ n))
power-of-pos-positive 0 = ⋆
power-of-pos-positive (succ n)
 = transport is-pos-succ (pos-multiplication-equiv-to-ℕ 2 (2^ n)) I
 where
  I : is-pos-succ (pos 2 ℤ* pos (2^ n))
  I = is-pos-succ-mult (pos 2) (pos (2^ n)) ⋆ (power-of-pos-positive n)

prod-of-powers : (n a b : ℕ) → n ℕ^ a ℕ* n ℕ^ b ＝ n ℕ^ (a +ℕ b)
prod-of-powers n a zero     = refl
prod-of-powers n a (succ b) = I
 where
  I : n ℕ^ a ℕ* n ℕ^ succ b ＝ n ℕ^ (a +ℕ succ b)
  I = n ℕ^ a ℕ* n ℕ^ succ b
        ＝⟨ refl ⟩
      n ℕ^ a ℕ* (n ℕ* n ℕ^ b)
        ＝⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a ℕ* n ℕ* n ℕ^ b
        ＝⟨ ap (_ℕ* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n ℕ* n ℕ^ a ℕ* n ℕ^ b
        ＝⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n ℕ* (n ℕ^ a ℕ* n ℕ^ b)
        ＝⟨ ap (n ℕ*_) (prod-of-powers n a b) ⟩
      n ℕ* n ℕ^ (a +ℕ b)
        ＝⟨ refl ⟩
      n ℕ^ succ (a +ℕ b)
        ＝⟨ refl ⟩
      n ℕ^ (a +ℕ succ b)       ∎

exponents-of-two-ordered : (m : ℕ) → 2 ℕ^ m < 2 ℕ^ (succ m)
exponents-of-two-ordered 0        = ⋆
exponents-of-two-ordered (succ m)
 = transport₂ _<_ I II
     (multiplication-preserves-strict-order (2 ℕ^ m) (2 ℕ^ succ m) 1 IH)
 where 
  IH : 2 ℕ^ m < 2 ℕ^ succ m
  IH = exponents-of-two-ordered m
  I : 2 ℕ^ m ℕ* 2 ＝ 2 ℕ^ succ m
  I = mult-commutativity (2 ℕ^ m) 2
  II : 2 ℕ^ succ m ℕ* 2 ＝ 2 ℕ^ succ (succ m)
  II = mult-commutativity (2 ℕ^ succ m) 2

div-by-two' : (k : ℕ) → k +ℕ k /2 ＝ k
div-by-two' 0 = refl
div-by-two' (succ k)
 = (succ k +ℕ succ k) /2     ＝⟨ ap _/2 (succ-left k (succ k)) ⟩
   succ (succ (k +ℕ k)) /2   ＝⟨ refl ⟩
   succ ((k +ℕ k) /2)        ＝⟨ ap succ (div-by-two' k) ⟩
   succ k                    ∎
```

Integer order definitions and properties

```
pred-shift : (a b : ℤ) → predℤ a ℤ- b ＝ a ℤ- succℤ b
pred-shift a b = ℤ-left-pred a (ℤ- b)
               ∙ ℤ-right-pred a (ℤ- b) ⁻¹
               ∙ ap (a +ℤ_)
                   (succℤ-lc (succpredℤ _
                             ∙ succpredℤ _ ⁻¹
                             ∙ ap succℤ (negation-dist b (pos 1))))

ℤ-less-not-equal : (a b : ℤ) → a <ℤ b → a ≠ b
ℤ-less-not-equal a a (n , a<a) refl = γ γ'
 where
   γ' : 0 ＝ succ n
   γ' = pos-lc (ℤ+-lc _ _ a (a<a ⁻¹ ∙ ℤ-left-succ-pos a n))
   γ : 0 ≠ succ n
   γ ()

≤-succℤ' : (x y : ℤ) → succℤ x ≤ succℤ y → x ≤ y
≤-succℤ' x y (n , e) = n , succℤ-lc (ℤ-left-succ x (pos n) ⁻¹ ∙ e) 

ℤ≤-succ-inj : (a b : ℤ) → a ≤ℤ b → succℤ a ≤ℤ succℤ b
ℤ≤-succ-inj a b (n , refl) = n , ℤ-left-succ-pos a n

ℤ≤-succⁿ-inj : (a b : ℤ) (n : ℕ) → a ≤ℤ b → (succℤ ^ n) a ≤ℤ (succℤ ^ n) b
ℤ≤-succⁿ-inj = rec-to-monotone succℤ succℤ ℤ≤-succ-inj

ℤ≤-pred-inj : (a b : ℤ) → a ≤ℤ b → predℤ a ≤ℤ predℤ b
ℤ≤-pred-inj a b (n , refl) = n , ℤ-left-pred-pos a n

ℤ≤-predⁿ-inj : (a b : ℤ) (n : ℕ) → a ≤ℤ b → (predℤ ^ n) a ≤ℤ (predℤ ^ n) b
ℤ≤-predⁿ-inj = rec-to-monotone predℤ predℤ ℤ≤-pred-inj

_≤ℤ_≤ℤ_ _≤_≤_ : ℤ → ℤ → ℤ → 𝓤₀ ̇ 
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)
_≤_≤_ = _≤ℤ_≤ℤ_

ℤ≤²-refl : (k : ℤ) → k ≤ℤ k ≤ℤ k
ℤ≤²-refl k = ℤ≤-refl k , ℤ≤-refl k

≤ℤ²-is-prop : {l u : ℤ} (x : ℤ) → is-prop (l ≤ℤ x ≤ℤ u)
≤ℤ²-is-prop {l} {u} x = ×-is-prop (ℤ≤-is-prop l x) (ℤ≤-is-prop x u)

ℤ[_,_] : ℤ → ℤ → 𝓤₀ ̇
ℤ[ l , u ] = Σ z ꞉ ℤ , (l ≤ℤ z ≤ℤ u)

ℤ[_,_]-succ : (l u : ℤ) → ℤ[ l , u ] → ℤ[ l , succℤ u ]
ℤ[ l , u ]-succ (z , l≤z , z≤u)
 = z , l≤z , ℤ≤-trans z u (succℤ u) z≤u (1 , refl) 

≤ℤ-antisym : ∀ x y → x ≤ℤ y ≤ℤ x → x ＝ y
≤ℤ-antisym x y (x≤y , y≤x) with ℤ≤-split x y x≤y | ℤ≤-split y x y≤x
... | inl (n , γ) | inl (m , δ)
 = 𝟘-elim (ℤ-equal-not-less-than x (ℤ<-trans x y x (n , γ) (m , δ)))
... | inl  _  | inr y＝x = y＝x ⁻¹
... | inr x＝y | _       = x＝y

≤ℤ-back : ∀ x y → x <ℤ y → x ≤ℤ predℤ y
≤ℤ-back x .(succℤ x +ℤ pos n) (n , refl)
 = ℤ≤-trans x (x +pos n) (predℤ (succℤ x +pos n))
     (n , refl)
     (transport ((x +pos n) ≤ℤ_)
       (predsuccℤ (x +pos n) ⁻¹
       ∙ ap predℤ (ℤ-left-succ x (pos n) ⁻¹))
       (ℤ≤-refl (x +pos n)))

ℤ-dich-succ : (x y : ℤ) 
            → ((      x <ℤ y) + (y ≤ℤ       x))
            → ((succℤ x <ℤ y) + (y ≤ℤ succℤ x))
ℤ-dich-succ x y (inl (0 , refl)) = inr (ℤ≤-refl _)
ℤ-dich-succ x y (inl (succ m , refl)) = inl (m , ℤ-left-succ-pos (succℤ x) m)
ℤ-dich-succ x y (inr (m , refl)) = inr (succ m , refl)

ℤ-trich-succ : (x y : ℤ) 
             → ((      x <ℤ y) + (      x ＝ y) + (y <ℤ       x))
             → ((succℤ x <ℤ y) + (succℤ x ＝ y) + (y <ℤ succℤ x))
ℤ-trich-succ x y (inl (0           , sn+j＝i))
 = (inr ∘ inl) sn+j＝i
ℤ-trich-succ x y (inl (succ j      , sn+j＝i))
 = inl (j , (ℤ-left-succ-pos (succℤ x) j ∙ sn+j＝i))
ℤ-trich-succ x y (inr (inl              n＝i))
 = (inr ∘ inr) (0 , ap succℤ (n＝i ⁻¹))
ℤ-trich-succ x y (inr (inr (j      , sn+j＝i)))
 = (inr ∘ inr) (succ j , ap succℤ sn+j＝i)

ℤ-vert-trich-locate : ℤ → ℤ → ℤ → 𝓤₀ ̇
ℤ-vert-trich-locate z a b = (z <ℤ a) + (a ≤ℤ z ≤ℤ b) + (b <ℤ z)

ℤ-vert-trich-succ : (z a b : ℤ) → a <ℤ b
                  → ℤ-vert-trich-locate        z  a b
                  → ℤ-vert-trich-locate (succℤ z) a b
ℤ-vert-trich-succ z a b (k , η) (inl (succ n , ε))
 = inl         (n , (ℤ-left-succ-pos (succℤ z) n ∙ ε))
ℤ-vert-trich-succ z a b (k , η) (inl (0      , refl))
 = (inr ∘ inl) ((0 , refl) , (succ k , (ℤ-left-succ-pos (succℤ z) k ⁻¹ ∙ η)))
ℤ-vert-trich-succ z a b (k , η) (inr (inl ((n₁ , ε₁) , succ n₂ , ε₂)))
 = (inr ∘ inl) ((succ n₁ , (ap succℤ ε₁)) , (n₂ , (ℤ-left-succ-pos z n₂ ∙ ε₂)))
ℤ-vert-trich-succ z a b (k , η) (inr (inl ((n₁ , ε₁) , zero , ε₂)))
 = (inr ∘ inr) (0 , ap succℤ (ε₂ ⁻¹))
ℤ-vert-trich-succ z a b (k , η) (inr (inr (n , refl)))
 = (inr ∘ inr) (succ n , refl)

ℤ-vert-trich-all : (z a b : ℤ) → ℤ-vert-trich-locate z a b
ℤ-vert-trich-all z a b = Cases (ℤ-trichotomous z a) inl
                 λ a≤z → Cases (ℤ-trichotomous b z) (inr ∘ inr)
                 λ z≤b → (inr ∘ inl) (ℤ≤-attach _ _ a≤z , ℤ≤-attach _ _ z≤b)

ℤ-vert-trich-is-prop : (z a b : ℤ) → a <ℤ b
                     → is-prop (ℤ-vert-trich-locate z a b)
ℤ-vert-trich-is-prop z a b a<b
 = +-is-prop (ℤ<-is-prop z a) (+-is-prop (≤ℤ²-is-prop z) (ℤ<-is-prop b z)
     (λ (_ , z≤b) → ℤ-bigger-or-equal-not-less z b z≤b))
    (λ z<a → cases
     (λ (a≤z , _) → ℤ-less-not-bigger-or-equal z a z<a a≤z)
     (ℤ-bigger-or-equal-not-less z b (<-is-≤ z b (ℤ<-trans z a b z<a a<b))))

ℤ≤-progress : (a b c : ℤ)
            → ((n , _) : a ≤ c) → a ≤ b → ((n₂ , _) : b ≤ c)
            → n₂ < succ n
ℤ≤-progress a b c a≤c (n₁ , refl) (n₂ , refl)
 = transport (n₂ ≤_)
     (ℤ≤-same-witness a c
       (ℤ≤-trans a b c (n₁ , refl) (n₂ , refl)) a≤c)
     (≤-+' n₁ n₂)

≥-lemma : (a b c : ℤ) → a ＝ b → (p : a ≥ c) → (q : b ≥ c)
        → pr₁ p ＝ pr₁ q
≥-lemma a a c refl (n , refl) (m , γ) = pos-lc (ℤ+-lc _ _ _ (γ ⁻¹))
```

Parity definitions and properties

```agda
odd even : ℤ → 𝓤₀ ̇
odd (pos                   0) = 𝟘
odd (pos                   1) = 𝟙
odd (pos (succ (succ x)))     = odd (pos x)
odd (negsucc               0) = 𝟙
odd (negsucc               1) = 𝟘
odd (negsucc (succ (succ x))) = odd (negsucc x)
even x = ¬ odd x

even-or-odd? : (x : ℤ) → even x + odd x
even-or-odd? (pos                   0) = inl (λ x → x)
even-or-odd? (pos                   1) = inr ⋆
even-or-odd? (pos (succ (succ x)))     = even-or-odd? (pos x)
even-or-odd? (negsucc               0) = inr ⋆
even-or-odd? (negsucc               1) = inl (λ x → x)
even-or-odd? (negsucc (succ (succ x))) = even-or-odd? (negsucc x)

odd-is-prop : (x : ℤ) → is-prop (odd x)
odd-is-prop (pos                   0) = 𝟘-is-prop
odd-is-prop (pos                   1) = 𝟙-is-prop
odd-is-prop (pos (succ (succ x)))     = odd-is-prop (pos x)
odd-is-prop (negsucc               0) = 𝟙-is-prop
odd-is-prop (negsucc               1) = 𝟘-is-prop
odd-is-prop (negsucc (succ (succ x))) = odd-is-prop (negsucc x)

succ-odd-is-even : (x : ℤ) → odd x → even (succℤ x)
succ-odd-is-even (pos                          1) o = id
succ-odd-is-even (pos            (succ (succ x))) o
 = succ-odd-is-even (pos x) o
succ-odd-is-even (negsucc                      0) o = id
succ-odd-is-even (negsucc (succ (succ (succ x)))) o
 = succ-odd-is-even (negsucc (succ x)) o

succ-even-is-odd : (x : ℤ) → even x → odd (succℤ x)
succ-even-is-odd (pos                          0) e = ⋆
succ-even-is-odd (pos                          1) e = e ⋆
succ-even-is-odd (pos            (succ (succ x))) e
 = succ-even-is-odd (pos x) e
succ-even-is-odd (negsucc                      0) e = e ⋆
succ-even-is-odd (negsucc                      1) e = ⋆
succ-even-is-odd (negsucc                      2) e = e ⋆
succ-even-is-odd (negsucc (succ (succ (succ x)))) e
 = succ-even-is-odd (negsucc (succ x)) e

odd-succ-succ : (x : ℤ) → odd x → odd (succℤ (succℤ x))
odd-succ-succ (pos x) = id
odd-succ-succ (negsucc zero) = id
odd-succ-succ (negsucc (succ (succ x))) = id

even-succ-succ : (x : ℤ) → even x → even (succℤ (succℤ x))
even-succ-succ (pos x) = id
even-succ-succ (negsucc zero) = id
even-succ-succ (negsucc (succ (succ x))) = id

negation-preserves-parity : (x : ℤ) → even x → even (ℤ- x)
negation-preserves-parity (pos 0) = id
negation-preserves-parity (pos (succ 0)) e = 𝟘-elim (e ⋆)
negation-preserves-parity (pos (succ (succ 0))) e = id
negation-preserves-parity (pos (succ (succ (succ x)))) e
 = negation-preserves-parity (pos (succ x)) e
negation-preserves-parity (negsucc 0) e = 𝟘-elim (e ⋆)
negation-preserves-parity (negsucc (succ 0)) e = id
negation-preserves-parity (negsucc (succ (succ x))) e
 = negation-preserves-parity (negsucc x)
     (even-succ-succ (negsucc (succ (succ x))) e)

even-lemma-pos : (x : ℕ) → even (pos x) → (pos x /2') ℤ* pos 2 ＝ pos x
even-lemma-pos 0 even-x = refl
even-lemma-pos (succ 0) even-x = 𝟘-elim (even-x ⋆)
even-lemma-pos (succ (succ x)) even-x
 = succℤ (pos x /2') +ℤ succℤ (pos x /2')
     ＝⟨ ℤ-left-succ (pos x /2') (succℤ (pos x /2')) ⟩
   succℤ (succℤ ((pos x /2') ℤ* pos 2))
     ＝⟨ ap (λ z → succℤ (succℤ z)) (even-lemma-pos x even-x) ⟩
   pos (succ (succ x)) ∎

even-lemma-neg : (x : ℕ) → even (negsucc x)
               → (negsucc x /2') ℤ* pos 2 ＝ negsucc x
even-lemma-neg x even-x
 = (ℤ- pos (succ x /2)) ℤ- pos (succ x /2)
     ＝⟨ negation-dist (pos (succ x /2)) (pos (succ x /2)) ⟩
   ℤ- (pos (succ x /2) +ℤ pos (succ x /2))
     ＝⟨ ap ℤ-_ (even-lemma-pos (succ x)
                  (negation-preserves-parity (negsucc x) even-x)) ⟩
   negsucc x ∎

even-lemma : (x : ℤ) → even x → (x /2') ℤ* pos 2 ＝ x
even-lemma (pos x) = even-lemma-pos x
even-lemma (negsucc x) = even-lemma-neg x

odd-succ-succ' : (k : ℤ) → odd (succℤ (succℤ k)) → odd k
odd-succ-succ' (pos x) = id
odd-succ-succ' (negsucc zero) = id
odd-succ-succ' (negsucc (succ (succ x))) = id

even-succ-succ' : (k : ℤ) → even (succℤ (succℤ k)) → even k
even-succ-succ' (pos 0) e = id
even-succ-succ' (pos (succ 0)) e = 𝟘-elim (e ⋆)
even-succ-succ' (pos (succ (succ x))) e = e
even-succ-succ' (negsucc 0) e = 𝟘-elim (e ⋆)
even-succ-succ' (negsucc (succ 0)) e = id
even-succ-succ' (negsucc (succ (succ x))) e = e

times-two-even' : (k : ℤ) → even (k +ℤ k)
times-two-even' (pos (succ k)) odd2k
 = times-two-even' (pos k)
     (odd-succ-succ' (pos k +ℤ pos k) (transport odd I odd2k))
 where
  I : pos (succ k) +ℤ pos (succ k) ＝ pos k +ℤ pos (succ (succ k))
  I = ℤ-left-succ (pos k) (pos (succ k))
times-two-even' (negsucc (succ k)) odd2k
 = times-two-even' (negsucc k)
     (transport odd I
       (odd-succ-succ (negsucc (succ k) +ℤ negsucc (succ k)) odd2k))
 where
  I : succℤ (succℤ (negsucc (succ k) +ℤ negsucc (succ k)))
    ＝ negsucc k +ℤ negsucc k
  I = succℤ (succℤ (negsucc (succ k) +ℤ negsucc (succ k)))
        ＝⟨ refl ⟩
      succℤ (succℤ (predℤ (negsucc k) +ℤ predℤ (negsucc k)))
        ＝⟨ refl ⟩
      succℤ (succℤ (predℤ (predℤ (negsucc k) +ℤ negsucc k)))
        ＝⟨ ap (λ a → succℤ a) (succpredℤ (predℤ (negsucc k) +ℤ negsucc k)) ⟩
      succℤ (predℤ (negsucc k) +ℤ negsucc k)
        ＝⟨ ap succℤ (ℤ-left-pred (negsucc k) (negsucc k)) ⟩
      succℤ (predℤ (negsucc k +ℤ negsucc k))
        ＝⟨ succpredℤ (negsucc k +ℤ negsucc k) ⟩
      negsucc k +ℤ negsucc k ∎

negsucc-lemma : (x : ℕ) → negsucc x +ℤ negsucc x ＝ negsucc (x +ℕ succ x)
negsucc-lemma x
 = negsucc x +ℤ negsucc x
     ＝⟨ refl ⟩
   (ℤ- pos (succ x)) ℤ- pos (succ x)
     ＝⟨ negation-dist (pos (succ x)) (pos (succ x)) ⟩
   ℤ- (pos (succ x) +ℤ pos (succ x))
     ＝⟨ refl ⟩
   ℤ- succℤ (pos (succ x) +ℤ pos x)
     ＝⟨ ap (λ z → ℤ- succℤ z) (distributivity-pos-addition (succ x) x) ⟩
   ℤ- succℤ (pos (succ x +ℕ x))
     ＝⟨ refl ⟩
   negsucc (succ x +ℕ x)
     ＝⟨ ap negsucc (addition-commutativity (succ x) x) ⟩
   negsucc (x +ℕ succ x) ∎

div-by-two : (k : ℤ) → (k +ℤ k) /2' ＝ k
div-by-two (pos k)
 = (pos k +ℤ pos k) /2'
     ＝⟨ ap _/2' (distributivity-pos-addition k k) ⟩     
   pos (k +ℕ k) /2'
     ＝⟨ ap pos (div-by-two' k) ⟩
   pos k ∎
div-by-two (negsucc x)
 = (negsucc x +ℤ negsucc x) /2'
     ＝⟨ ap _/2' (negsucc-lemma x) ⟩
   negsucc (x +ℕ succ x) /2'
     ＝⟨ refl ⟩
   ℤ- pos (succ (x +ℕ succ x) /2)
     ＝⟨ ap (λ z → ℤ- pos (z /2)) (succ-left x (succ x) ⁻¹) ⟩
   ℤ- pos ((succ x +ℕ succ x) /2)
     ＝⟨ ap (λ z → ℤ- pos z) (div-by-two' (succ x)) ⟩
   negsucc x ∎
```


Preserves-as properties

```agda
_preserves_as_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (X → 𝓦 ̇ ) → (Y → 𝓣 ̇ )
               → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇ 
f preserves A as B  = ∀ x → A x → B (f x)

_preserves_ : {X : 𝓤 ̇ } → (X → X) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓦 ̇
f preserves A = f preserves A as A

preserves-trans : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓤' ̇ }
                → (f : X → Y) → (g : Y → Z)
                → (A : X → 𝓦 ̇ ) → (B : Y → 𝓣 ̇ ) → (C : Z → 𝓥' ̇ )
                → f preserves A as B
                → g preserves B as C
                → (g ∘ f) preserves A as C
preserves-trans f g A B C p₁ p₂ x Ax = p₂ (f x) (p₁ x Ax)
```

Vector definition and properties

```agda
data Vec (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇  where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

pattern [_] x = x ∷ []

head : {A : 𝓤 ̇ } {n : ℕ} → Vec A (succ n) → A
head (x ∷ _) = x

vec-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ}
        → (A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ v) = f x ∷ vec-map f v

vec-map-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          → {n : ℕ}
          → (f : X → Y) → (g : Y → Z)
          → (xs : Vec X n)
          → vec-map (g ∘ f) xs ＝ vec-map g (vec-map f xs)
vec-map-∼ f g [] = refl
vec-map-∼ f g (x ∷ xs) = ap (g (f x) ∷_) (vec-map-∼ f g xs)

vec-map₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
         → Vec (X → Y) n → Vec X n → Vec Y n
vec-map₂ [] [] = []
vec-map₂ (x ∷ χs) (k ∷ ks) = x k ∷ vec-map₂ χs ks

vec-satisfy : {X : 𝓤 ̇ } {n : ℕ} → (X → 𝓦 ̇ ) → Vec X n → 𝓦 ̇ 
vec-satisfy p [] = 𝟙
vec-satisfy p (x ∷ xs) = p x × vec-satisfy p xs

pairwise₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ} (p : X → Y → 𝓦 ̇ )
          → Vec X n → Vec Y n → 𝓦 ̇
pairwise₂ p []       []       = 𝟙
pairwise₂ p (x ∷ xs) (y ∷ ys) = p x y × pairwise₂ p xs ys

vec-map₂-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
           → (f : Y → Z) (gs : Vec (X → Y) n)
           → (xs : Vec X n)
           → vec-map f (vec-map₂ gs xs) ＝ vec-map₂ (vec-map (f ∘_) gs) xs
vec-map₂-∼ f [] [] = refl
vec-map₂-∼ f (g ∷ gs) (x ∷ xs) = ap (f (g x) ∷_) (vec-map₂-∼ f gs xs)

pairwise₂-extend : {X : 𝓤 ̇ } {Y : 𝓥  ̇ } {Z : 𝓣  ̇ } {n : ℕ}
                 → (p₁ : X → 𝓦  ̇ )
                 → (p₂ : Y → Y → 𝓦'  ̇ )
                 → (p₃ : Z → Z → 𝓣'  ̇ )
                 → (f : X → Y → Z)
                 → (∀ x → p₁ x → ∀ i j → p₂ i j → p₃ (f x i) (f x j))
                 → (xs : Vec X n)
                 → (is : Vec Y n) (js : Vec Y n)
                 → vec-satisfy p₁ xs
                 → pairwise₂ p₂ is js
                 → pairwise₂ p₃ (vec-map₂ (vec-map f xs) is)
                                (vec-map₂ (vec-map f xs) js)
pairwise₂-extend p₁ p₂ p₃ f g [] [] [] _ x = ⋆
pairwise₂-extend p₁ p₂ p₃ f g
                 (x ∷ xs) (i ∷ is) (j ∷ js) (px , pxs) (pij , pisjs)
 = g x px i j pij , pairwise₂-extend p₁ p₂ p₃ f g xs is js pxs pisjs

vec-satisfy₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
             → (p : Y → 𝓦 ̇ )
             → (f : X → Y)
             → (∀ x → p (f x))
             → (xs : Vec X n)
             → vec-satisfy p (vec-map f xs)
vec-satisfy₁ p f Πp [] = ⋆
vec-satisfy₁ p f Πp (x ∷ xs) = Πp x , (vec-satisfy₁ p f Πp xs)

vec-satisfy-preserved-by : {X : 𝓤 ̇ }
                         → {n : ℕ} (xs : Vec (ℤ → X) n) → (ks : Vec ℤ n) 
                         → (p : X → 𝓦 ̇ )
                         → vec-satisfy (λ x → ∀ (n : ℤ) → p (x n)) xs
                         → vec-satisfy p (vec-map₂ xs ks)
vec-satisfy-preserved-by [] [] p ⋆ = ⋆
vec-satisfy-preserved-by (x ∷ xs) (k ∷ ks) p (px , pxs)
 = px k , vec-satisfy-preserved-by xs ks p pxs

_+++_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → X → Vec X (succ n)
[] +++ x = [ x ]
(h ∷ v) +++ x = h ∷ (v +++ x)

_!!_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → (k : ℕ) → k <ℕ n → X
((x ∷ v) !! zero) k<n = x
((x ∷ v) !! succ k) k<n = (v !! k) k<n

!!-helper : {X : 𝓤 ̇ } {n : ℕ} → (v : Vec X n) → (k₁ k₂ : ℕ)
          → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
          → k₁ ＝ k₂
          → (v !! k₁) k₁<n ＝ (v !! k₂) k₂<n
!!-helper (x ∷ v) zero .zero k₁<n k₂<n refl = refl
!!-helper (x ∷ v) (succ k) .(succ k) k₁<n k₂<n refl
 = !!-helper v k k k₁<n k₂<n refl

!!-prop : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X n)
        → (k₁ k₂ : ℕ) → k₁ ＝ k₂
        → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
        → (xs !! k₁) k₁<n ＝ (xs !! k₂) k₂<n
!!-prop n xs k k refl k₁<n k₂<n = ap (xs !! k) (<-is-prop-valued k n k₁<n k₂<n)

fst lst : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → X
fst xs = (xs !! 0) ⋆
lst {n = n} xs = (xs !! n) (<-succ n)

drop-fst drop-lst : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → Vec X n
drop-fst (x ∷ xs) = xs
drop-lst (x ∷ []) = []
drop-lst (x ∷ (y ∷ xs)) = x ∷ drop-lst (y ∷ xs)

inner : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ (succ n)) → Vec X n
inner = drop-fst ∘ drop-lst

pairwise pairwise-r : {X : 𝓤 ̇ } {n : ℕ}
                    → Vec X (succ n) → (p : X → X → 𝓥 ̇ ) → 𝓥 ̇
pairwise {𝓤} {𝓥} {X} {n} v p
 = (k : ℕ) → (k<n : k <ℕ n) → (k<sn : k <ℕ succ n)
 → p ((v !! k) k<sn) ((v !! succ k) k<n)

pairwise-r {𝓤} {𝓥} {X} {n} v p
 = (k : ℕ) → (k<n : k <ℕ n) → (k<sn : k <ℕ succ n)
 → p ((v !! succ k) k<n) ((v !! k) k<sn)

sigma-witness vector-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → X → X → ℕ → 𝓤 ̇ 

sigma-witness {𝓤} {X} p x y 0
 = p x y 
sigma-witness {𝓤} {X} p x y (succ n)
 = Σ z ꞉ X , (p x z) × (sigma-witness p z y n)

vector-witness {𝓤} {X} p x y n
 = Σ xs ꞉ Vec X (succ (succ n))
 , (fst xs ＝ x)
 × (lst xs ＝ y)
 × pairwise xs p

sigma→vector-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → (x y : X) (n : ℕ)
                     → sigma-witness p x y n → vector-witness p x y n
sigma→vector-witness p x y zero η
 = xs , refl , refl , γ
 where
  xs = x ∷ [ y ]
  γ : pairwise xs p
  γ zero ⋆ ⋆ = η
sigma→vector-witness p x y (succ n) (z , η , θ)
 = xs , refl , pr₁ (pr₂ (pr₂ IH)) , γ
 where
  IH = sigma→vector-witness p z y n θ
  xs = x ∷ pr₁ IH
  γ : pairwise xs p
  γ zero k<n k<sn = transport (p x) (pr₁ (pr₂ IH) ⁻¹) η
  γ (succ k) k<n k<sn = pr₂ (pr₂ (pr₂ IH)) k k<n k<sn

vector→sigma-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → (x y : X) (n : ℕ)
                     → vector-witness p x y n → sigma-witness p x y n
vector→sigma-witness p x y zero ((x ∷ (y ∷ [])) , refl , refl , w) = w 0 ⋆ ⋆
vector→sigma-witness p x y (succ n) ((x ∷ (z ∷ xs)) , refl , t , w)
 = z , w 0 ⋆ ⋆ , vector→sigma-witness p z y n ((z ∷ xs) , refl , t , w ∘ succ)

reverse : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
reverse [] = []
reverse (x ∷ xs) = reverse xs +++ x

reverse' : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
reverse' [] = []
reverse' (x ∷ []) = [ x ]
reverse' (x ∷ (y ∷ xs)) = lst (x ∷ (y ∷ xs)) ∷ reverse (drop-lst (x ∷ (y ∷ xs)))

fst-++ : {X : 𝓤 ̇ } {n : ℕ} → (x : X) (xs : Vec X (succ n))
       → fst (xs +++ x) ＝ fst xs
fst-++ {𝓤} {X} {n} x (y ∷ xs) = refl

lst-++ : {X : 𝓤 ̇ } {n : ℕ} → (x : X) (xs : Vec X n)
       → lst (xs +++ x) ＝ x
lst-++ {𝓤} {X} {0}      x []        = refl
lst-++ {𝓤} {X} {succ n} x (y ∷ xs) = lst-++ x xs

reverse-fst-becomes-lst : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X (succ n))
                        → lst (reverse xs) ＝ fst xs
reverse-fst-becomes-lst (x ∷ xs) = lst-++ x (reverse xs)

reverse-lst-becomes-fst : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X (succ n))
                        → fst (reverse xs) ＝ lst xs
reverse-lst-becomes-fst (x ∷ []) = refl
reverse-lst-becomes-fst (x ∷ (y ∷ xs)) = fst-++ x (reverse (y ∷ xs))
                                       ∙ reverse-lst-becomes-fst (y ∷ xs)

_−_ : (n k : ℕ) → k ≤ℕ n → ℕ
(n − zero) _ = n
(succ n − succ k) = (n − k)

−-< : (n k : ℕ) → (k≤n : k <ℕ n) → (n − succ k) k≤n <ℕ n
−-< (succ n) zero k≤n = ≤-refl n
−-< (succ (succ n)) (succ zero) k≤n = ≤-succ n
−-< (succ (succ n)) (succ (succ k)) k≤n
 = <-trans ((n − succ k) k≤n) n (succ (succ n))
     (−-< n k k≤n)
     (<-trans n (succ n) (succ (succ n))
       (<-succ n)
       (<-succ (succ n)))

drop-lst-< : {X : 𝓤 ̇ } (n k : ℕ) → (k<n : k <ℕ n) (k<sn : k <ℕ (succ n))
           → (xs : Vec X  (succ n))
           → (drop-lst xs !! k) k<n
           ＝ (         xs !! k) k<sn
drop-lst-< n zero k<n k<sn (x ∷ (y ∷ xs)) = refl
drop-lst-< (succ n) (succ k) k<n k<sn (x ∷ (y ∷ xs))
 = drop-lst-< n k k<n k<sn (y ∷ xs)

drop-fst-< : {X : 𝓤 ̇ } → (n k : ℕ) → (k<n : k <ℕ n)
           → (xs : Vec X (succ n))
           → (         xs !! succ k) k<n
           ＝ (drop-fst xs !!      k) k<n
drop-fst-< n k k<n (x ∷ xs) = refl

drop-fst-++ : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n)) (x : X)
            → drop-fst (xs +++ x) ＝ drop-fst xs +++ x
drop-fst-++ n (y ∷ xs) x = refl

drop-lst-++ : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n)) (x : X)
            → drop-lst (x ∷ xs) ＝ (x ∷ drop-lst xs)
drop-lst-++ n (y ∷ xs) x = refl

reverse-drop : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n))
             → reverse (drop-lst xs) ＝ drop-fst (reverse xs)
reverse-drop zero (x ∷ []) = refl
reverse-drop (succ n) (x ∷ xs)
 = ap reverse (drop-lst-++ n xs x)
 ∙ ap (_+++ x) (reverse-drop n xs)
 ∙ drop-fst-++ n (reverse xs) x ⁻¹

reverse-minus-becomes-k : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X n)
                        → (k : ℕ) → (k<n : k <ℕ n)
                        → (reverse xs !! k) k<n
                        ＝ (xs !! (n − succ k) k<n) (−-< n k k<n)
reverse-minus-becomes-k (x ∷ xs) 0 k<n = reverse-lst-becomes-fst (x ∷ xs)
reverse-minus-becomes-k {𝓤} {X} {succ (succ n)} (x ∷ xs) (succ k) k<n
 = drop-fst-< (succ n) k k<n (reverse xs +++ x)
 ∙ ap (λ - → (- !! k) k<n) (reverse-drop (succ n) (x ∷ xs) ⁻¹)
 ∙ reverse-minus-becomes-k {𝓤} {X} {succ n} (drop-lst (x ∷ xs)) k k<n
 ∙ drop-lst-< (succ n) ((n − k) k<n) (−-< (succ n) k k<n)
     (−-< (succ (succ n)) (succ k) k<n) (x ∷ xs) 

−-lemma : (n k : ℕ) → (k<sn : k <ℕ succ n) → (k<n : k <ℕ n)
        → (n − k) k<sn ＝ succ ((n − succ k) k<n)
−-lemma (succ n) zero k<sn k<n = refl
−-lemma (succ n) (succ k) k<sn k<n = −-lemma n k k<sn k<n

reverse-pairwise : {X : 𝓤 ̇ } {n : ℕ} → (p q : X → X → 𝓤 ̇ )
                 → ((x y : X) → p x y → q y x)
                 → (xs : Vec X (succ n))
                 → pairwise xs p
                 → pairwise (reverse xs) q
reverse-pairwise {𝓤} {X} {n} p q f xs w k k<n k<sn
 = transport (q _) (reverse-minus-becomes-k xs (succ k) k<n ⁻¹)
     (transport (λ - → (q -) _) (reverse-minus-becomes-k xs k k<sn ⁻¹)
       (f _ _ (transport (p _) (γ ⁻¹)
                 (w _ (−-< n k k<n) (−-< (succ n) (succ k) k<n)))))
 where
   γ : (xs !! (n − k) k<sn) (−-< (succ n) k k<sn)
     ＝ (xs !! succ ((n − succ k) k<n)) (−-< n k k<n)
   γ = !!-prop (succ n) xs ((n − k) k<sn) (succ ((n − succ k) k<n))
         (−-lemma n k k<sn k<n)
         (−-< (succ n) k k<sn) (−-< n k k<n)
 
vector-witness→inv : {X : 𝓤 ̇ } → (p q : X → X → 𝓤 ̇ )
                   → ((x y : X) → p x y → q y x)
                   → (x y : X) (n : ℕ)
                   → vector-witness p x y n
                   → vector-witness q y x n
vector-witness→inv p q f x y n (xs , s , t , u)
 = reverse xs
 , (reverse-lst-becomes-fst xs ∙ t)
 , (reverse-fst-becomes-lst xs ∙ s)
 , reverse-pairwise p q f xs u

sigma-witness→inv : {X : 𝓤 ̇ } → (p q : X → X → 𝓤 ̇ )
                  → ((x y : X) → p x y → q y x)
                  → (x y : X) (n : ℕ)
                  → sigma-witness p x y n
                  → sigma-witness q y x n
sigma-witness→inv p q f x y n
 = (vector→sigma-witness q y x n)
 ∘ (vector-witness→inv p q f x y n)
 ∘ (sigma→vector-witness p x y n)
```
