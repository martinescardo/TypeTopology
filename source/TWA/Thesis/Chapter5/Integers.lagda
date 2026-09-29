Todd Waugh Ambridge, January 2024

# Additional integer properties

\begin{code}
{-# OPTIONS --without-K --safe #-}

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

module TWA.Thesis.Chapter5.Integers where
\end{code}

## ℤ-elimination

\begin{code}
ℤ-elim : (P : ℤ → 𝓤 ̇ )
       → ((n : ℕ) → P (pos n)) → ((n : ℕ) → P (negsucc n))
       → Π P
ℤ-elim P Pp Pn (pos     n) = Pp n
ℤ-elim P Pp Pn (negsucc n) = Pn n
\end{code}

## Monotone and rec properties

\begin{code}
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
succ-to-monotone P r t s a b (n , γ)
 = succ-to-monotone' P r t s a b n γ

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
\end{code}

## Sign and num for integers

\begin{code}
sign : ℤ → (ℕ → ℤ)
sign (pos     _) = pos
sign (negsucc _) = negsucc

num : ℤ → ℕ
num  (pos     n) = n
num  (negsucc n) = n
\end{code}

## Natural number functions definitions and properties

\begin{code}
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
        ＝⟨refl⟩
      n ℕ^ a ℕ* (n ℕ* n ℕ^ b)
        ＝⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a ℕ* n ℕ* n ℕ^ b
        ＝⟨ ap (_ℕ* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n ℕ* n ℕ^ a ℕ* n ℕ^ b
        ＝⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n ℕ* (n ℕ^ a ℕ* n ℕ^ b)
        ＝⟨ ap (n ℕ*_) (prod-of-powers n a b) ⟩
      n ℕ* n ℕ^ (a +ℕ b)
        ＝⟨refl⟩
      n ℕ^ succ (a +ℕ b)
        ＝⟨refl⟩
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
   succ (succ (k +ℕ k)) /2   ＝⟨refl⟩
   succ ((k +ℕ k) /2)        ＝⟨ ap succ (div-by-two' k) ⟩
   succ k                    ∎
\end{code}

## Integer order definitions and properties

\begin{code}
ℤ≤-decidable : (n m : ℤ) → (n ≤ m) + ¬ (n ≤ m)
ℤ≤-decidable n m
 = Cases (ℤ-trichotomous m n)
     (inr ∘ ℤ-less-not-bigger-or-equal m n)
     (inl ∘ ℤ≤-attach n m)

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

ℤ≤-succⁿ-inj
 : (a b : ℤ) (n : ℕ) → a ≤ℤ b → (succℤ ^ n) a ≤ℤ (succℤ ^ n) b
ℤ≤-succⁿ-inj = rec-to-monotone succℤ succℤ ℤ≤-succ-inj

ℤ≤-pred-inj : (a b : ℤ) → a ≤ℤ b → predℤ a ≤ℤ predℤ b
ℤ≤-pred-inj a b (n , refl) = n , ℤ-left-pred-pos a n

ℤ≤-predⁿ-inj
 : (a b : ℤ) (n : ℕ) → a ≤ℤ b → (predℤ ^ n) a ≤ℤ (predℤ ^ n) b
ℤ≤-predⁿ-inj = rec-to-monotone predℤ predℤ ℤ≤-pred-inj

_≤ℤ_≤ℤ_ : ℤ → ℤ → ℤ → 𝓤₀ ̇
x ≤ℤ y ≤ℤ z = (x ≤ℤ y) × (y ≤ℤ z)

ℤ≤²-refl : (k : ℤ) → k ≤ℤ k ≤ℤ k
ℤ≤²-refl k = ℤ≤-refl k , ℤ≤-refl k

≤ℤ²-is-prop : {l u : ℤ} (x : ℤ) → is-prop (l ≤ℤ x ≤ℤ u)
≤ℤ²-is-prop {l} {u} x = ×-is-prop (ℤ≤-is-prop l x) (ℤ≤-is-prop x u)

ℤ[_,_] : ℤ → ℤ → 𝓤₀ ̇
ℤ[ l , u ] = Σ z ꞉ ℤ , (l ≤ℤ z ≤ℤ u)

ℤ[_,_]-succ : (l u : ℤ) → ℤ[ l , u ] → ℤ[ l , succℤ u ]
ℤ[ l , u ]-succ (z , l≤z , z≤u)
 = z , l≤z , ℤ≤-trans z u (succℤ u) z≤u (1 , refl)

≤ℤ-antisym : (x y : ℤ) → x ≤ℤ y ≤ℤ x → x ＝ y
≤ℤ-antisym x y (x≤y , y≤x)
 = Cases (ℤ≤-split x y x≤y) (Cases (ℤ≤-split y x y≤x)
     (λ y<x x<y
      → 𝟘-elim (ℤ-equal-not-less-than x (ℤ<-trans x y x x<y y<x)))
     (λ y=x _ → y=x ⁻¹))
     id

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
ℤ-dich-succ x y (inl (succ m , refl))
 = inl (m , ℤ-left-succ-pos (succℤ x) m)
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
 = (inr ∘ inl)
     ((0 , refl) , (succ k , (ℤ-left-succ-pos (succℤ z) k ⁻¹ ∙ η)))
ℤ-vert-trich-succ z a b (k , η) (inr (inl ((n₁ , ε₁) , succ n₂ , ε₂)))
 = (inr ∘ inl)
     ((succ n₁ , (ap succℤ ε₁)) , (n₂ , (ℤ-left-succ-pos z n₂ ∙ ε₂)))
ℤ-vert-trich-succ z a b (k , η) (inr (inl ((n₁ , ε₁) , zero , ε₂)))
 = (inr ∘ inr) (0 , ap succℤ (ε₂ ⁻¹))
ℤ-vert-trich-succ z a b (k , η) (inr (inr (n , refl)))
 = (inr ∘ inr) (succ n , refl)

ℤ-vert-trich-all : (z a b : ℤ) → ℤ-vert-trich-locate z a b
ℤ-vert-trich-all z a b = Cases (ℤ-trichotomous z a) inl
                 λ a≤z → Cases (ℤ-trichotomous b z) (inr ∘ inr)
                 λ z≤b → (inr ∘ inl)
                           (ℤ≤-attach _ _ a≤z , ℤ≤-attach _ _ z≤b)

ℤ-vert-trich-is-prop : (z a b : ℤ) → a <ℤ b
                     → is-prop (ℤ-vert-trich-locate z a b)
ℤ-vert-trich-is-prop z a b a<b
 = +-is-prop
     (ℤ<-is-prop z a) (+-is-prop (≤ℤ²-is-prop z) (ℤ<-is-prop b z)
     (λ (_ , z≤b) → ℤ-bigger-or-equal-not-less z b z≤b))
     (λ z<a → cases
      (λ (a≤z , _) → ℤ-less-not-bigger-or-equal z a z<a a≤z)
      (ℤ-bigger-or-equal-not-less z b
        (<-is-≤ z b (ℤ<-trans z a b z<a a<b))))

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
\end{code}

## Parity definitions and properties

\begin{code}
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
succ-odd-is-even (pos                          0) o = 𝟘-elim o
succ-odd-is-even (pos                          1) o = id
succ-odd-is-even (pos            (succ (succ x))) o
 = succ-odd-is-even (pos x) o
succ-odd-is-even (negsucc                      0) o = id
succ-odd-is-even (negsucc                      1) o = 𝟘-elim o
succ-odd-is-even (negsucc                      2) o = id
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
odd-succ-succ (negsucc (succ zero)) o = 𝟘-elim o
odd-succ-succ (negsucc (succ (succ x))) = id

even-succ-succ : (x : ℤ) → even x → even (succℤ (succℤ x))
even-succ-succ (pos x) = id
even-succ-succ (negsucc zero) = id
even-succ-succ (negsucc (succ zero)) e o = 𝟘-elim o
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
odd-succ-succ' (negsucc (succ zero)) o = 𝟘-elim o
odd-succ-succ' (negsucc (succ (succ x))) = id

even-succ-succ' : (k : ℤ) → even (succℤ (succℤ k)) → even k
even-succ-succ' (pos 0) e = id
even-succ-succ' (pos (succ 0)) e = 𝟘-elim (e ⋆)
even-succ-succ' (pos (succ (succ x))) e = e
even-succ-succ' (negsucc 0) e = 𝟘-elim (e ⋆)
even-succ-succ' (negsucc (succ 0)) e = id
even-succ-succ' (negsucc (succ (succ x))) e = e

times-two-even' : (k : ℤ) → even (k +ℤ k)
times-two-even' (pos zero) odd2k = 𝟘-elim odd2k
times-two-even' (negsucc zero) odd2k = 𝟘-elim odd2k
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
        ＝⟨refl⟩
      succℤ (succℤ (predℤ (negsucc k) +ℤ predℤ (negsucc k)))
        ＝⟨refl⟩
      succℤ (succℤ (predℤ (predℤ (negsucc k) +ℤ negsucc k)))
        ＝⟨ ap (λ a → succℤ a)
               (succpredℤ (predℤ (negsucc k) +ℤ negsucc k)) ⟩
      succℤ (predℤ (negsucc k) +ℤ negsucc k)
        ＝⟨ ap succℤ (ℤ-left-pred (negsucc k) (negsucc k)) ⟩
      succℤ (predℤ (negsucc k +ℤ negsucc k))
        ＝⟨ succpredℤ (negsucc k +ℤ negsucc k) ⟩
      negsucc k +ℤ negsucc k ∎

negsucc-lemma
 : (x : ℕ) → negsucc x +ℤ negsucc x ＝ negsucc (x +ℕ succ x)
negsucc-lemma x
 = negsucc x +ℤ negsucc x
     ＝⟨refl⟩
   (ℤ- pos (succ x)) ℤ- pos (succ x)
     ＝⟨ negation-dist (pos (succ x)) (pos (succ x)) ⟩
   ℤ- (pos (succ x) +ℤ pos (succ x))
     ＝⟨refl⟩
   ℤ- succℤ (pos (succ x) +ℤ pos x)
     ＝⟨ ap (λ z → ℤ- succℤ z) (distributivity-pos-addition (succ x) x) ⟩
   ℤ- succℤ (pos (succ x +ℕ x))
     ＝⟨refl⟩
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
     ＝⟨refl⟩
   ℤ- pos (succ (x +ℕ succ x) /2)
     ＝⟨ ap (λ z → ℤ- pos (z /2)) (succ-left x (succ x) ⁻¹) ⟩
   ℤ- pos ((succ x +ℕ succ x) /2)
     ＝⟨ ap (λ z → ℤ- pos z) (div-by-two' (succ x)) ⟩
   negsucc x ∎
\end{code}
