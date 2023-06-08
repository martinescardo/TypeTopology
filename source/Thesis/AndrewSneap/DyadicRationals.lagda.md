```agda
{-# OPTIONS --exact-split --without-K --auto-inline
            --experimental-lossy-unification #-}
            
open import Integers.Addition renaming (_+_ to _+ℤ_ ; _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_)
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import Notation.Order 
open import UF.Base
open import UF.FunExt
open import UF.Miscelanea
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import Thesis.Chapter5.PLDIPrelude

module Thesis.AndrewSneap.DyadicRationals where
```

This file defines dyadic rationals as a record, along with many widely
accepted operations, relations and results on dyadic rationals. They
are denoted ℤ[1/2].

```agda
ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , (n ＝ 0) + ((n ≠ 0) × odd z)

ℤ[1/2]-cond-is-prop : FunExt → (z : ℤ) (n : ℕ)
                    → is-prop ((n ＝ 0) + ((n ≠ 0) × odd z))
ℤ[1/2]-cond-is-prop fe z n
 = +-is-prop ℕ-is-set
     (×-is-prop (Π-is-prop (fe 𝓤₀ 𝓤₀) (λ _ → 𝟘-is-prop))
                 (odd-is-prop z))
     (λ e (ne , _) → ne e)

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , inl refl

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , inl refl

1/2ℤ[1/2] : ℤ[1/2]
1/2ℤ[1/2] = (pos 1 , 1) , inr (positive-not-zero 0 , ⋆)

normalise-pos normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-pos z 0        = (z , 0) , inl refl
normalise-pos z (succ n) with even-or-odd? z
... | inl e = normalise-pos (z /2') n
... | inr o = (z , succ n) , inr (positive-not-zero n , o)
normalise-neg z 0        = (z +ℤ z , 0) , inl refl
normalise-neg z (succ n) = normalise-neg (z +ℤ z) n

normalise-pos' : (x : ℤ) → (a : ℕ)
               → let ((k , δ) , p) = normalise-pos x a in
                 Σ m ꞉ ℕ , ((pos (2^ m) ℤ* k , δ +ℕ m) ＝ x , a)
normalise-pos' x 0 = 0 , to-×-＝ (ℤ-mult-left-id x) refl
normalise-pos' x (succ a) with even-or-odd? x
... | inr odd-k = 0 , (to-×-＝ (ℤ-mult-left-id x) refl)
... | inl even-k with normalise-pos' (x /2') a
... | (m , e) with from-×-＝' e
... | (e₁ , e₂)
 = succ m
 , let (k , δ) , p = normalise-pos (x /2') a in
   to-×-＝' (
     (pos (2^ (succ m)) ℤ* k
       ＝⟨ refl ⟩
     pos (2 ℕ* 2^ m) ℤ* k
       ＝⟨ ap (_ℤ* k) (pos-multiplication-equiv-to-ℕ 2 (2^ m) ⁻¹) ⟩
     pos 2 ℤ* pos (2^ m) ℤ* k
       ＝⟨ ℤ*-assoc (pos 2) (pos (2^ m)) k ⟩
     pos 2 ℤ* (pos (2^ m) ℤ* k)
       ＝⟨ ap (pos 2 ℤ*_) e₁ ⟩
     pos 2 ℤ* (x /2')
       ＝⟨ ℤ*-comm (pos 2) (x /2') ⟩
     (x /2') ℤ* pos 2
       ＝⟨ even-lemma x even-k ⟩ 
     x ∎)
    , ap succ e₂
   )

normalise : ℤ × ℤ → ℤ[1/2]
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

normalise-neg' : (x : ℤ) (a : ℕ)
               → let ((k , δ) , p) = normalise-neg x a in
                 (k , δ) ＝ pos (2^ (succ a)) ℤ* x , 0
normalise-neg' x 0        = to-×-＝ (ℤ*-comm x (pos 2)) refl
normalise-neg' x (succ a) with from-×-＝' (normalise-neg' (x +ℤ x) a)
... | e₁ , e₂ = to-×-＝ I e₂
 where
  I : pr₁ (pr₁ (normalise-neg (x +ℤ x) a)) ＝ pos (2^ (succ (succ a))) ℤ* x
  I = pr₁ (pr₁ (normalise-neg (x +ℤ x) a))
        ＝⟨ e₁ ⟩
      pos (2^ (succ a)) ℤ* (x ℤ* pos 2)
        ＝⟨ ap (pos (2^ (succ a)) ℤ*_) (ℤ*-comm x (pos 2)) ⟩
      pos (2^ (succ a)) ℤ* (pos 2 ℤ* x)
        ＝⟨ ℤ*-assoc (pos (2^ (succ a))) (pos 2) x ⁻¹ ⟩
      pos (2^ (succ a)) ℤ* pos 2 ℤ* x
        ＝⟨ ap (_ℤ* x) (pos-multiplication-equiv-to-ℕ (2^ (succ a)) 2) ⟩
      pos (2^ (succ a) ℕ* 2) ℤ* x
        ＝⟨ ap (λ z → pos z ℤ* x) (mult-commutativity (2^ (succ a)) 2) ⟩
      pos (2^ (succ (succ a))) ℤ* x ∎

lowest-terms-normalised : FunExt → (((k , δ) , p) : ℤ[1/2])
                        → normalise-pos k δ ＝ ((k , δ) , p)
lowest-terms-normalised fe ((k , .0) , inl refl) = refl
lowest-terms-normalised fe ((k , zero) , inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
lowest-terms-normalised fe ((k , succ δ) , inr (δnz , k-odd))
 with even-or-odd? k
... | inl k-even = 𝟘-elim (k-even k-odd)
... | inr k-odd = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n) refl

normalise-pos-lemma₁ : FunExt → (k : ℤ) (δ : ℕ)
                     → (p : (δ ＝ 0) + ((δ ≠ 0) × odd k))
                     → normalise-pos ((k +ℤ k) /2') δ ＝ (k , δ) , p
normalise-pos-lemma₁ fe k 0 (inl refl)
 = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n)
     (to-×-＝ (div-by-two k) refl)
normalise-pos-lemma₁ fe k 0 (inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
normalise-pos-lemma₁ fe k (succ δ) (inr p) with even-or-odd? ((k +ℤ k) /2')
normalise-pos-lemma₁ fe k (succ δ) (inr (δnz , k-odd)) | inl k-even
 = 𝟘-elim (k-even (transport odd (div-by-two k ⁻¹) k-odd))
... | inr _ = to-subtype-＝ (λ (z , n) → ℤ[1/2]-cond-is-prop fe z n)
                (to-×-＝ (div-by-two k) refl)
                
normalise-pos-lemma₂ : (k : ℤ) (δ : ℕ)
                     → normalise-pos k δ ＝ normalise-pos (k +ℤ k) (succ δ)
normalise-pos-lemma₂ k δ with even-or-odd? (k +ℤ k)
... | inl _ = ap (λ s → normalise-pos s δ) (div-by-two k ⁻¹)
... | inr o = 𝟘-elim (times-two-even' k o)

double : ℤ → ℤ
double a = a +ℤ a

normalise-lemma : FunExt → (k : ℤ) (δ : ℕ) (n : ℕ)
                → (p : (δ ＝ 0) + ((δ ≠ 0) × odd k))
                → normalise
                    (rec k double n +ℤ rec k double n , (pos (succ δ) +ℤ pos n))
                ＝ (k , δ) , p
normalise-lemma fe k δ 0 p with even-or-odd? (k +ℤ k)
... | inl even = normalise-pos-lemma₁ fe k δ p
... | inr odd = 𝟘-elim (times-two-even' k odd)
normalise-lemma fe k δ (succ n) p with even-or-odd? (k +ℤ k)
... | inl even
 = let y = rec k double n 
       z = (y +ℤ y) in 
   normalise (z +ℤ z , (succℤ (pos (succ δ) +ℤ pos n)))
     ＝⟨ ap (λ - → normalise (z +ℤ z , succℤ -))
           (distributivity-pos-addition (succ δ) n) ⟩
   normalise (z +ℤ z , succℤ (pos (succ δ +ℕ n)))
     ＝⟨ refl ⟩
   normalise-pos (z +ℤ z) (succ (succ δ +ℕ n))
     ＝⟨ normalise-pos-lemma₂ z (succ δ +ℕ n) ⁻¹ ⟩
   normalise-pos z (succ δ +ℕ n)
     ＝⟨ refl ⟩
   normalise (z , pos (succ δ +ℕ n))
     ＝⟨ ap (λ - → normalise (z , -))
           (distributivity-pos-addition (succ δ) n ⁻¹) ⟩
   normalise (z , pos (succ δ) +ℤ pos n)
     ＝⟨ normalise-lemma fe k δ n p ⟩
   (k , δ) , p ∎ 
... | inr odd = 𝟘-elim (times-two-even' k odd)

_<ℤ[1/2]_ _≤ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
((x , n) , _) <ℤ[1/2] ((y , m) , _) = x ℤ* pos (2^ m) < y ℤ* pos (2^ n)
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = x ℤ* pos (2^ m) ≤ y ℤ* pos (2^ n)

<ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
<ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _)
 = ℤ<-is-prop (x ℤ* pos (2^ b)) (y ℤ* pos (2^ a)) 

≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _)
 = ℤ≤-is-prop (x ℤ* pos (2^ b)) (y ℤ* pos (2^ a))

ℤ[1/2]⁺ : 𝓤₀ ̇
ℤ[1/2]⁺ = Σ x ꞉ ℤ[1/2] , 0ℤ[1/2] <ℤ[1/2] x

_<ℤ[1/2]⁺_ _≤ℤ[1/2]⁺_ : ℤ[1/2]⁺ → ℤ[1/2]⁺ → 𝓤₀ ̇
(x , l) <ℤ[1/2]⁺ (y , l') = x <ℤ[1/2] y
(x , l) ≤ℤ[1/2]⁺ (y , l') = x ≤ℤ[1/2] y

is-positive : ℤ[1/2] -> 𝓤₀ ̇
is-positive x = 0ℤ[1/2] <ℤ[1/2] x

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _≤ℤ[1/2]_

 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _<ℤ[1/2]_

instance
 Order-ℤ[1/2]⁺-ℤ[1/2]⁺ : Order ℤ[1/2]⁺ ℤ[1/2]⁺
 _≤_ {{Order-ℤ[1/2]⁺-ℤ[1/2]⁺}} = _≤ℤ[1/2]⁺_

 Strict-Order-ℤ[1/2]⁺-ℤ[1/2]⁺ : Strict-Order ℤ[1/2]⁺ ℤ[1/2]⁺
 _<_ {{Strict-Order-ℤ[1/2]⁺-ℤ[1/2]⁺}} = _<ℤ[1/2]⁺_

record Dyadics : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-_      : ℤ[1/2] → ℤ[1/2]

 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)

 field
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-abs : ℤ[1/2] → ℤ[1/2]
  trans  : (x y z : ℤ[1/2]) → x < y → y < z → x < z
  trans' : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
  dense  : (x y : ℤ[1/2]) → (x < y) → Σ k ꞉ ℤ[1/2] , (x < k) × (k < y)
  ≤-refl : (x : ℤ[1/2]) → x ≤ x
  <-is-≤ℤ[1/2] : (x y : ℤ[1/2]) → x < y → x ≤ y
  diff-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
  <-swap : (x y : ℤ[1/2]) → x < y → (ℤ[1/2]- y) < (ℤ[1/2]- x)
  ≤-swap : (x y : ℤ[1/2]) → x ≤ y → (ℤ[1/2]- y) ≤ (ℤ[1/2]- x)
  ≤-swap' : (x y : ℤ[1/2]) → (ℤ[1/2]- x) ≤ (ℤ[1/2]- y) → y ≤ x
  ≤-split : (x y : ℤ[1/2]) → x ≤ y → x < y + (x ＝ y)
  <-pos-mult'
   : (x y : ℤ[1/2]) → 0ℤ[1/2] < x
   → 0ℤ[1/2] < y → 0ℤ[1/2] < (x ℤ[1/2]* y)
  ℤ[1/2]<-+ : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → x < (x ℤ[1/2]+ y)
  ℤ[1/2]<-neg : (x y : ℤ[1/2]) → 0ℤ[1/2] < y → (x ℤ[1/2]- y) < x
  ℤ[1/2]<-rearrange : (x y z : ℤ[1/2]) → (x ℤ[1/2]+ y) < z → y < (z ℤ[1/2]- x)
  ℤ[1/2]-1/2-< : (x : ℤ[1/2]) → 0ℤ[1/2] < x → (1/2ℤ[1/2] ℤ[1/2]* x) < x
  normalise-≤
   : (n : ℕ) → ((k , p) : ℤ × ℤ)
   → normalise (k , p) ≤ normalise ((k +pos n) , p)
  ℤ[1/2]-ordering-property
   : (a b c d : ℤ[1/2]) → (a ℤ[1/2]- b) < (c ℤ[1/2]- d) → (a < c) + (d < b)
  normalise-succ' : (z n : ℤ) → normalise (z , n)
                              ＝ normalise (z +ℤ z , succℤ n)
  normalise-pred' : (z n : ℤ) → normalise (z , predℤ n)
                              ＝ normalise (pos 2 ℤ* z , n)
  ℤ[1/2]<-positive-mult
   : (a b : ℤ[1/2]) → is-positive a → is-positive b → is-positive (a ℤ[1/2]* b)
  ℤ[1/2]-find-lower : (ε : ℤ[1/2]) → is-positive ε
                    → Σ n ꞉ ℤ , normalise (pos 2 , n) < ε
  normalise-negation
   : (a b c : ℤ)
   → normalise (a , c) ℤ[1/2]- normalise (b , c) ＝ normalise (a ℤ- b , c)
  normalise-negation' : (a b : ℤ)
                      → ℤ[1/2]- normalise (a , b) ＝ normalise (ℤ- a , b)
  from-normalise-≤-same-denom
   : (a b c : ℤ) → normalise (a , c) ≤ normalise (b , c) → a ≤ b

 ℤ[1/2]<-≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
 ℤ[1/2]<-≤ x y z x<y y≤z with ≤-split y z y≤z
 ... | inl y<z = trans x y z x<y y<z
 ... | inr y=z = transport (x <_) y=z x<y

 ℤ[1/2]≤-< : (x y z : ℤ[1/2]) → x ≤ y → y < z → x < z
 ℤ[1/2]≤-< x y z x≤y y<z with ≤-split x y x≤y
 ... | inl x<y = trans x y z x<y y<z
 ... | inr x＝y = transport (_< z) (x＝y ⁻¹) y<z
 
 0<1/2ℤ[1/2] : 0ℤ[1/2] < 1/2ℤ[1/2]
 0<1/2ℤ[1/2] = 0 , refl

 0<1ℤ[1/2] : 0ℤ[1/2] < 1ℤ[1/2]
 0<1ℤ[1/2] = 0 , refl

 normalise-≤2 : (l r p : ℤ) → l ≤ r → normalise (l , p) ≤ normalise (r , p)
 normalise-≤2 l r p (j , refl) = normalise-≤ j (l , p)
```

