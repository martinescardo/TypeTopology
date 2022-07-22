```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import MLTT.Spartan
open import MLTT.Two-Properties hiding (zero-is-not-one)
open import Naturals.Order
open import DedekindReals.Integers.Order
open import DedekindReals.Integers.Integers
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import DedekindReals.Integers.Addition renaming (_+_ to _+ℤ_)
open import DedekindReals.Integers.Negation renaming (-_  to  −ℤ_)
open import UF.Subsingletons
open import Naturals.Order
open import NotionsOfDecidability.DecidableAndDetachable

module Todd.BelowAndAbove (fe : FunExt)where

open import Todd.TernaryBoehmRealsPrelude fe


```

```
b<a→a≢b : ∀ a b → (b <ℤ a) → a ≢ b
b<a→a≢b a a (n , a<a) refl = γ γ'
 where
   γ' : 0 ＝ succ n
   γ' = pos-lc (ℤ+-lc _ _ a (a<a ⁻¹ ∙ ℤ-left-succ-pos a n))
   γ : 0 ≢ succ n
   γ ()

ℤ-elim : (P : ℤ → 𝓤 ̇ )
       → ((n : ℕ) → P (pos n)) → ((n : ℕ) → P (negsucc n))
       → Π P
ℤ-elim P Pp Pn (pos     n) = Pp n
ℤ-elim P Pp Pn (negsucc n) = Pn n

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
```

downLeft, downMid and downRight

```
downLeft downMid downRight : ℤ → ℤ
downLeft  a = a +ℤ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)
```

downLeft and downRight properties

```
pred-downMid : (a : ℤ) → predℤ (downMid a) ＝ downLeft a
pred-downMid a = predsuccℤ _

pred-downRight : (a : ℤ) → predℤ (downRight a) ＝ downMid a
pred-downRight a = predsuccℤ _

pred-pred-downRight : (a : ℤ) → predℤ (predℤ (downRight a)) ＝ downLeft a
pred-pred-downRight a = ap predℤ (predsuccℤ _) ∙ predsuccℤ _

downLeft≢downRight : (a b : ℤ) → a ＝ b → downLeft a ≢ downRight a
downLeft≢downRight a a refl dL＝dR = b<a→a≢b _ _ (1 , refl) (dL＝dR ⁻¹)

downLeft-monotone' : (a b : ℤ) → ((n , _) : a ≤ℤ b)
                   → downLeft a +pos (n +ℕ n) ＝ downLeft b
downLeft-monotone' a b (n , refl)
 = ap ((a +ℤ a) +ℤ_) (distributivity-pos-addition n n ⁻¹)
 ∙ ℤ+-rearrangement (a +ℤ a) (pos n) (pos n) ⁻¹
 ∙ ap (λ - → (- +pos n) +pos n) (ℤ+-comm a a)
 ∙ ap (_+pos n)
     (ℤ+-assoc a a (pos n)
     ∙ ap (a +ℤ_) (ℤ+-comm a (pos n))
     ∙ ℤ+-assoc a (pos n) a ⁻¹)
 ∙ ℤ+-assoc (a +pos n) a (pos n)

ℤ≤<-trans : (a b c : ℤ) → a ≤ℤ b → b <ℤ c → a <ℤ c
ℤ≤<-trans a b c (m , refl) (n , refl)
 = m +ℕ n
 , (ap (succℤ a +ℤ_) (distributivity-pos-addition m n ⁻¹)
 ∙ ℤ+-assoc (succℤ a) (pos m) (pos n) ⁻¹ -- ℤ-left-succ a (pos m +pos n)
 ∙ ap (_+pos n) (ℤ-left-succ-pos a m))


downLeft<<downRight : (a b : ℤ) → a <ℤ b → downLeft a <ℤ downRight b
downLeft<<downRight a b (n , refl)
 = (succ (succ (succ (n +ℕ n))))
 , ap (succℤ ∘ succℤ)
     (ap succℤ
       (ap (_+pos (n +ℕ n)) (ℤ-left-succ a a ⁻¹)
       ∙ ap ((succℤ a +ℤ a) +ℤ_) (distributivity-pos-addition n n ⁻¹)
       ∙ ℤ+-rearrangement (succℤ a +ℤ a) (pos n) (pos n) ⁻¹
       ∙ ap (λ - → (- +pos n) +pos n) (ℤ+-comm (succℤ a) a)
       ∙ ap (_+pos n)
           (ℤ+-assoc a (succℤ a) (pos n)
         ∙ ap (a +ℤ_) (ℤ+-comm (succℤ a) (pos n))
         ∙ ℤ+-assoc a (pos n) (succℤ a) ⁻¹)
       ∙ ℤ+-assoc (a +pos n) (succℤ a) (pos n))
   ∙ ℤ-left-succ (a +pos n) (succℤ a +pos n) ⁻¹
   ∙ ap (_+ℤ (succℤ a +pos n)) (ℤ-left-succ-pos a n ⁻¹))

downLeft<downRight : (a : ℤ) (n : ℕ)
                   → rec a downLeft (succ n) <ℤ rec a downRight (succ n)
downLeft<downRight a zero = 1 , refl
downLeft<downRight a (succ n) = downLeft<<downRight _ _ (downLeft<downRight a n)

downLeft≤downRight : (a : ℤ) (n : ℕ) → rec a downLeft n ≤ℤ rec a downRight n
downLeft≤downRight a 0 = zero , refl
downLeft≤downRight a (succ n) = <-is-≤ _ _ (downLeft<downRight a n)

downLeft-≤-succ : (a : ℤ) → downLeft a ≤ℤ downLeft (succℤ a)
downLeft-≤-succ a
 = 2 , (ap succℤ (ℤ-left-succ a a ⁻¹) ∙ ℤ-right-succ (succℤ a) a ⁻¹)

downLeft-monotone : (a b : ℤ) → a ≤ℤ b → downLeft a ≤ℤ downLeft b
downLeft-monotone = ≤-succ-to-monotone downLeft downLeft-≤-succ

downLeftⁿ-monotone : (a b : ℤ) (n : ℕ) → a ≤ℤ b
                   → rec a downLeft (succ n) ≤ℤ rec b downLeft (succ n)
downLeftⁿ-monotone a b 0 a≤b
 = downLeft-monotone a b a≤b
downLeftⁿ-monotone a b (succ n) a≤b
 = downLeft-monotone _ _ (downLeftⁿ-monotone a b n a≤b)

downRight-≤-succ : (a : ℤ) → downRight a ≤ℤ downRight (succℤ a)
downRight-≤-succ a = 2 , ap (succℤ ∘ succℤ) (pr₂ (downLeft-≤-succ a))

downRight-monotone : (a b : ℤ) → a ≤ℤ b → downRight a ≤ℤ downRight b
downRight-monotone = ≤-succ-to-monotone downRight downRight-≤-succ

downRightⁿ-monotone : (a b : ℤ) (n : ℕ) → a ≤ℤ b
                    → rec a downRight (succ n) ≤ℤ rec b downRight (succ n)
downRightⁿ-monotone a b 0 a≤b
 = downRight-monotone a b a≤b
downRightⁿ-monotone a b (succ n) a≤b
 = downRight-monotone _ _ (downRightⁿ-monotone a b n a≤b)

downLeft≤<downRight : (a b : ℤ) → a ≤ℤ b → downLeft a <ℤ downRight b
downLeft≤<downRight a b a≤b
 = ℤ≤<-trans _ _ _ (downLeft-monotone _ _ a≤b) (downLeft<downRight b 0)

```

below and below'

```
_below_ : ℤ → ℤ → 𝓤₀ ̇ 
a below b = downLeft b ≤ℤ a ≤ℤ downRight b

downLeft-below  : (a : ℤ) → downLeft a below a
downLeft-below  a = (0 , refl) , (2 , refl)

downMid-below   : (a : ℤ) → downMid a below a
downMid-below   a = (1 , refl) , (1 , refl)

downRight-below : (a : ℤ) → downRight a below a
downRight-below a = (2 , refl) , (0 , refl)

_below'_ : ℤ → ℤ → 𝓤₀ ̇
a below' b = (a ＝ downLeft b) + (a ＝ downMid b) + (a ＝ downRight b)

below'-implies-below : (a b : ℤ) → a below' b → a below b
below'-implies-below .(downLeft  b) b (inl      refl ) = downLeft-below b
below'-implies-below .(downMid   b) b (inr (inl refl)) = downMid-below b
below'-implies-below .(downRight b) b (inr (inr refl)) = downRight-below b

below-implies-below' : (a b : ℤ) → a below b → a below' b
below-implies-below' a b ((0 , e) , _)
 = inl (e ⁻¹)
below-implies-below' a b ((1 , e) , _)
 = (inr ∘ inl) (e ⁻¹)
below-implies-below' a b ((2 , e) , _)
 = (inr ∘ inr) (e ⁻¹)
below-implies-below' a b ((succ (succ (succ _)) , _) , (0 , f))
 = (inr ∘ inr) f
below-implies-below' a b ((succ (succ (succ _)) , _) , (1 , f))
 = (inr ∘ inl) (succℤ-lc f)
below-implies-below' a b ((succ (succ (succ _)) , _) , (2 , f))
 = inl (succℤ-lc (succℤ-lc f))
below-implies-below' a b ((succ (succ (succ n)) , e) , (succ (succ (succ m)) , f))
 = 𝟘-elim (k≢2 k＝2)
 where
   k : ℕ
   k = (succ (succ (succ (succ (succ (succ (n +ℕ m)))))))
   η : downLeft b +pos k ＝ downRight b
   η = (ap ((succℤ ^ 6) ∘ downLeft b +ℤ_) (distributivity-pos-addition n m ⁻¹)
     ∙ ap (succℤ ^ 6) (ℤ+-assoc (downLeft b) (pos n) (pos m) ⁻¹)
     ∙ ap (succℤ ^ 5) (ℤ-left-succ-pos (downLeft b +pos n) m ⁻¹)
     ∙ ap (succℤ ^ 4) (ℤ-left-succ-pos (succℤ (downLeft b +pos n)) m ⁻¹)
     ∙ ap (succℤ ^ 3) (ℤ-left-succ-pos ((succℤ ^ 2) (downLeft b +pos n)) m ⁻¹)
     ∙ ap ((succℤ ^ 3) ∘ (_+pos m)) e
     ∙ f)
   ζ : downLeft b +pos 2 ＝ downRight b
   ζ = refl
   k＝2 : k ＝ 2
   k＝2 = pos-lc (ℤ+-lc (pos k) (pos 2) (downLeft b) (η ∙ ζ ⁻¹))
   k≢2 : k ≢ 2
   k≢2 = λ ()
```

upLeft and upRight

```
upRight : ℤ → ℤ
upRight x = sign x (num x /2)

upLeft : ℤ → ℤ
upLeft x = upRight (predℤ x)
```

upLeft and upRight properties

```
upRight-suc : (a : ℤ) → upRight (succℤ (succℤ a)) ＝ succℤ (upRight a)
upRight-suc (pos zero) = refl
upRight-suc (pos (succ zero)) = refl
upRight-suc (pos (succ (succ x))) = refl
upRight-suc (negsucc zero) = refl
upRight-suc (negsucc (succ zero)) = refl
upRight-suc (negsucc (succ (succ x))) = refl

upRight-pred : (a : ℤ) → upRight (predℤ (predℤ a)) ＝ predℤ (upRight a)
upRight-pred (pos 0) = refl
upRight-pred (pos 1) = refl
upRight-pred (pos (succ (succ x))) = refl
upRight-pred (negsucc 0) = refl
upRight-pred (negsucc 1) = refl
upRight-pred (negsucc (succ (succ x))) = refl

upLeft-suc : (a : ℤ) → upLeft (succℤ (succℤ a)) ＝ succℤ (upLeft a)
upLeft-suc (pos zero) = refl
upLeft-suc (pos (succ zero)) = refl
upLeft-suc (pos (succ (succ x))) = refl
upLeft-suc (negsucc zero) = refl
upLeft-suc (negsucc (succ zero)) = refl
upLeft-suc (negsucc (succ (succ x))) = refl

upLeft-pred : (a : ℤ) → upLeft (predℤ (predℤ a)) ＝ predℤ (upLeft a)
upLeft-pred = upRight-pred ∘ predℤ

upRight-succ-pos : (a : ℕ) → upRight (pos a) ≤ℤ upRight (succℤ (pos a))
upRight-succ-pos 0 = 0 , refl
upRight-succ-pos 1 = 1 , refl
upRight-succ-pos (succ (succ a))
 = m , (ℤ-left-succ-pos (pos (a /2)) m ∙ ap succℤ (pr₂ IH))
 where
   IH = upRight-succ-pos a
   m = pr₁ IH


upRight-succ-negsucc : (a : ℕ) → upRight (negsucc a) ≤ℤ upRight (succℤ (negsucc a))
upRight-succ-negsucc 0 = 1 , refl
upRight-succ-negsucc 1 = 0 , refl
upRight-succ-negsucc (succ (succ a))
 = m , (ℤ-left-pred-pos (negsucc (a /2)) m
       ∙ ap predℤ (pr₂ IH)
       ∙ upRight-pred _ ⁻¹
       ∙ ap (upRight ∘ predℤ) (predsuccℤ _))
 where
   IH = upRight-succ-negsucc a
   m = pr₁ IH


upRight-≤-succ : (a : ℤ) → upRight a ≤ℤ upRight (succℤ a)
upRight-≤-succ = ℤ-elim (λ a → upRight a ≤ℤ upRight (succℤ a))
                   upRight-succ-pos upRight-succ-negsucc

upRight-monotone : (a b : ℤ) → a ≤ℤ b → upRight a ≤ℤ upRight b
upRight-monotone = ≤-succ-to-monotone upRight upRight-≤-succ

upLeft-monotone : (a b : ℤ) → a ≤ℤ b → upLeft a ≤ℤ upLeft b
upLeft-monotone a b (n , refl) = upRight-monotone _ _ (n , ℤ-left-pred-pos a n)

upRight-<-succ-succ : (a : ℤ) → upRight a <ℤ upRight (succℤ (succℤ a))
upRight-<-succ-succ a = transport (upRight a <ℤ_) (upRight-suc a ⁻¹) (0 , refl)

upRight-<<' : (a b : ℤ) (n : ℕ) → (a +pos succ n) ＝ predℤ b → upRight a <ℤ upRight b
upRight-<<' a b zero e
 = transport (λ - → upRight a <ℤ upRight -)
     (ap succℤ e ∙ succpredℤ _)
     (upRight-<-succ-succ a)
upRight-<<' a b (succ n) e
 = transport (λ - → upRight a <ℤ upRight -)
     (ap succℤ e ∙ succpredℤ _)
     (ℤ≤-trans _ _ _ (upRight-<-succ-succ a)
       (upRight-monotone _ _
       (succ n , ap succℤ (ℤ-left-succ-pos (succℤ a) n ∙ ap succℤ (ℤ-left-succ-pos a n)))))
 
upRight-<< : (a b : ℤ) → a <ℤ predℤ b → upRight a <ℤ upRight b
upRight-<< a b (n , e)
 = upRight-<<' a b n (ℤ-left-succ-pos a n ⁻¹ ∙ e)

upLeft-<< : (a b : ℤ) → a <ℤ b → upLeft a <ℤ upRight b
upLeft-<< a b (n , refl)
 = upRight-<< (predℤ a) b
     (n , (ap (_+pos n) (succpredℤ _) ∙ predsuccℤ _ ⁻¹ ∙ ap predℤ (ℤ-left-succ-pos a n ⁻¹)))

```

above and above'

```
_above_ : ℤ → ℤ → 𝓤₀ ̇ 
b above a = upLeft a ≤ℤ b ≤ℤ upRight a

_above'_ : ℤ → ℤ → 𝓤₀ ̇
a above' b = (a ＝ upLeft b) + (a ＝ upRight b)

upLeft-＝-+-pos : (a : ℕ) → (upLeft (pos a) ＝ upRight (pos a))
                         + (succℤ (upLeft (pos a)) ＝ upRight (pos a))
upLeft-＝-+-pos 0 = inr refl
upLeft-＝-+-pos 1 = inl refl
upLeft-＝-+-pos (succ (succ a))
 = Cases (upLeft-＝-+-pos a)
     (λ l → inl (upLeft-suc (pos a) ∙ ap succℤ l))
     (λ r → inr (ap succℤ (upLeft-suc (pos a) ∙ r)))

upLeft-＝-+-negsucc : (a : ℕ) → (upLeft (negsucc a) ＝ upRight (negsucc a))
                             + (succℤ (upLeft (negsucc a)) ＝ upRight (negsucc a))
upLeft-＝-+-negsucc 0 = inl refl
upLeft-＝-+-negsucc 1 = inr refl
upLeft-＝-+-negsucc (succ (succ a))
 = Cases (upLeft-＝-+-negsucc a)
      (λ l → inl (upLeft-pred (negsucc a) ∙ ap predℤ l))
      (λ r → inr (predsuccℤ _ ⁻¹ ∙ ap predℤ r))

upLeft-＝-+ : (a : ℤ) → (upLeft a ＝ upRight a) + (succℤ (upLeft a) ＝ upRight a)
upLeft-＝-+ = ℤ-elim _ upLeft-＝-+-pos upLeft-＝-+-negsucc

upLeft≤upRight : (a : ℤ) → upLeft a ≤ℤ upRight a
upLeft≤upRight a = upRight-monotone _ _ (1 , succpredℤ _)

upLeft-upRight-mono : (a b : ℤ) → a ≤ℤ b → upLeft a ≤ℤ upRight b
upLeft-upRight-mono a b a≤b = ℤ≤-trans _ _ _ (upLeft-monotone _ _ a≤b) (upLeft≤upRight b)

upLeft≤upRightⁿ : (a : ℤ) (n : ℕ) → rec a upLeft n ≤ℤ rec a upRight n
upLeft≤upRightⁿ a 0 = ℤ≤-refl a
upLeft≤upRightⁿ a 1 = upLeft≤upRight a
upLeft≤upRightⁿ a (succ (succ n)) = upLeft-upRight-mono _ _ (upLeft≤upRightⁿ a (succ n))

upLeft-above : (a : ℤ) → upLeft a above a
upLeft-above a = ℤ≤-refl _ , upLeft≤upRight a

upRight-above : (a : ℤ) → upRight a above a
upRight-above a = upLeft≤upRight a , ℤ≤-refl _

above'-implies-above : (a b : ℤ) → a above' b → a above b
above'-implies-above .(upLeft  b) b (inl refl) = upLeft-above b
above'-implies-above .(upRight b) b (inr refl) = upRight-above b

nothing-between : (a b c : ℤ) → a <ℤ b → b <ℤ c → ¬ ((a ＝ c) + (succℤ a ＝ c))
nothing-between a b .a a<b b<c (inl refl)
 = ℤ-less-not-bigger-or-equal a b a<b (<-is-≤ b a b<c)
nothing-between a b .(succℤ a) a<b b<c (inr refl)
 = ℤ-less-not-bigger-or-equal b (succℤ a) b<c a<b

above-implies-above' : (a b : ℤ) → a above b → a above' b
above-implies-above' a b (l≤a , a≤r)
 = Cases (ℤ≤-split (upLeft b) a l≤a)
     (λ l<a → Cases (ℤ≤-split a (upRight b) a≤r)
       (λ a<r → 𝟘-elim (nothing-between (upLeft b) a (upRight b) l<a a<r (upLeft-＝-+ b)))
       inr)
     (inl ∘ _⁻¹)

```

Relationship between below and above

```
upRight-downLeft-pos : (b : ℕ) → pos b ＝ upRight (downLeft (pos b))
upRight-downLeft-pos 0 = refl
upRight-downLeft-pos (succ b)
 = ap succℤ (upRight-downLeft-pos b)
 ∙ upRight-suc (downLeft (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downLeft-negsucc : (b : ℕ) → negsucc b ＝ upRight (downLeft (negsucc b))
upRight-downLeft-negsucc 0 = refl
upRight-downLeft-negsucc (succ b)
 = ap predℤ (upRight-downLeft-negsucc b)
 ∙ upRight-pred (downLeft (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)

upRight-downMid-pos : (b : ℕ) → pos b ＝ upRight (downMid (pos b))
upRight-downMid-pos 0 = refl
upRight-downMid-pos (succ b)
 = ap succℤ (upRight-downMid-pos b)
 ∙ upRight-suc (downMid (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downMid-negsucc : (b : ℕ) → negsucc b ＝ upRight (downMid (negsucc b))
upRight-downMid-negsucc 0 = refl
upRight-downMid-negsucc (succ b)
 = ap predℤ (upRight-downMid-negsucc b)
 ∙ upRight-pred (downMid (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (predsuccℤ _)
 ∙ ap upRight (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)
 ∙ ap upRight (succpredℤ _ ⁻¹)

upRight-downLeft : (a : ℤ) → a ＝ upRight (downLeft a)
upRight-downLeft = ℤ-elim _ upRight-downLeft-pos upRight-downLeft-negsucc

upRight-downMid : (a : ℤ) → a ＝ upRight (downMid a)
upRight-downMid = ℤ-elim _ upRight-downMid-pos upRight-downMid-negsucc

upRight-downRight : (a : ℤ) → succℤ a ＝ upRight (downRight a)
upRight-downRight a = ap succℤ (upRight-downLeft a) ∙ upRight-suc (downLeft a) ⁻¹

upLeft-downLeft : (a : ℤ) → succℤ (upLeft (downLeft a)) ＝ a
upLeft-downLeft a = upRight-suc (predℤ (downLeft a)) ⁻¹
                  ∙ ap (upRight ∘ succℤ) (succpredℤ _)
                  ∙ upRight-downMid a ⁻¹

upLeft-downMid : (a : ℤ) → upLeft (downMid a) ＝ a
upLeft-downMid a = ap upRight (pred-downMid a) ∙ upRight-downLeft a ⁻¹

upLeft-downRight : (a : ℤ) → upLeft (downRight a) ＝ a
upLeft-downRight a = ap upRight (pred-downRight a) ∙ upRight-downMid a ⁻¹

below-implies-above-dL : (b : ℤ) → b above (downLeft b)
below-implies-above-dL b
 = (1 , upLeft-downLeft  b)
 , (0 , upRight-downLeft b)

below-implies-above-dM : (b : ℤ) → b above (downMid b)
below-implies-above-dM b
 = (0 , upLeft-downMid  b)
 , (0 , upRight-downMid b)

below-implies-above-dR : (b : ℤ) → b above (downRight b)
below-implies-above-dR b
 = (0 , upLeft-downRight  b)
 , (1 , upRight-downRight b)

below'-implies-above : (a b : ℤ) → a below' b → b above a
below'-implies-above .(downLeft  b) b (inl refl)
 = below-implies-above-dL b
below'-implies-above .(downMid   b) b (inr (inl refl))
 = below-implies-above-dM b
below'-implies-above .(downRight b) b (inr (inr refl))
 = below-implies-above-dR b

dL-transform : (a : ℤ) → downLeft (succℤ a) ＝ (succℤ ^ 2) (downLeft a)
dL-transform a = ℤ-left-succ a (succℤ a) ∙ ap succℤ (ℤ-right-succ a a)

dL-transform-pred : (a : ℤ) → downLeft (predℤ a) ＝ (predℤ ^ 2) (downLeft a)
dL-transform-pred a = ℤ-left-pred a (predℤ a) ∙ ap predℤ (ℤ-right-pred a a)

dR-transform : (a : ℤ) → downRight (succℤ a) ＝ (succℤ ^ 2) (downRight a)
dR-transform a = ap (succℤ ^ 2) (dL-transform a)

dR-transform-pred : (a b : ℤ) → downRight (predℤ a) ＝ (predℤ ^ 2) (downRight a)
dR-transform-pred a b = ap (succℤ ^ 2) (dL-transform-pred a)
                      ∙ ap succℤ (succpredℤ _)
                      ∙ succpredℤ _
                      ∙ predsuccℤ _ ⁻¹
                      ∙ ap predℤ (predsuccℤ _ ⁻¹)

ℤ≤-succ-inj : (a b : ℤ) → a ≤ℤ b → succℤ a ≤ℤ succℤ b
ℤ≤-succ-inj a b (n , refl) = n , ℤ-left-succ-pos a n

ℤ≤-succⁿ-inj : (a b : ℤ) (n : ℕ) → a ≤ℤ b → (succℤ ^ n) a ≤ℤ (succℤ ^ n) b
ℤ≤-succⁿ-inj = rec-to-monotone succℤ succℤ ℤ≤-succ-inj

ℤ≤-pred-inj : (a b : ℤ) → a ≤ℤ b → predℤ a ≤ℤ predℤ b
ℤ≤-pred-inj a b (n , refl) = n , ℤ-left-pred-pos a n

ℤ≤-predⁿ-inj : (a b : ℤ) (n : ℕ) → a ≤ℤ b → (predℤ ^ n) a ≤ℤ (predℤ ^ n) b
ℤ≤-predⁿ-inj = rec-to-monotone predℤ predℤ ℤ≤-pred-inj

downLeft-upRight : (b : ℤ) → downLeft (upRight b) ≤ℤ b
downLeft-upRight = ℤ-elim _ downLeft-upRight-pos downLeft-upRight-negsucc
 where
  downLeft-upRight-pos : (b : ℕ) → downLeft (upRight (pos b)) ≤ℤ pos b
  downLeft-upRight-pos 0 = 0 , refl
  downLeft-upRight-pos 1 = 1 , refl
  downLeft-upRight-pos (succ (succ b))
   = transport (_≤ℤ succℤ (succℤ (pos b)))
      ((ap downLeft (upRight-suc (pos b)) ∙ dL-transform (upRight (pos b))) ⁻¹)
      (ℤ≤-succⁿ-inj _ _ 2 (downLeft-upRight-pos b))
  downLeft-upRight-negsucc : (b : ℕ) → downLeft (upRight (negsucc b)) ≤ℤ negsucc b
  downLeft-upRight-negsucc 0 = 1 , refl
  downLeft-upRight-negsucc 1 = 0 , refl
  downLeft-upRight-negsucc (succ (succ b))
   = transport (_≤ℤ predℤ (predℤ (negsucc b)))
       ((ap downLeft (upRight-pred (negsucc b)) ∙ dL-transform-pred (upRight (negsucc b))) ⁻¹)
       (ℤ≤-predⁿ-inj _ _ 2 (downLeft-upRight-negsucc b))

downLeft-upLeft  : (b : ℤ) → downLeft (upLeft b) ≤ℤ b
downLeft-upLeft b
 = ℤ≤-trans _ _ _ (downLeft-monotone _ _ (upLeft≤upRight b)) (downLeft-upRight b)

downRight-upLeft-pos : (b : ℕ) → pos b ≤ℤ downRight (upLeft (pos b))
downRight-upLeft-pos 0 = 0 , refl
downRight-upLeft-pos 1 = 1 , refl
downRight-upLeft-pos (succ (succ b))
 = transport ((succℤ ^ 2) (pos b) ≤ℤ_)
    ((ap downRight (upLeft-suc (pos b)) ∙ dR-transform (upLeft (pos b))) ⁻¹)
    (ℤ≤-succⁿ-inj _ _ 2 (downRight-upLeft-pos b))

downRight-upLeft-negsucc : (b : ℕ) → negsucc b ≤ℤ downRight (upLeft (negsucc b))
downRight-upLeft-negsucc 0 = 1 , refl
downRight-upLeft-negsucc 1 = 0 , refl
downRight-upLeft-negsucc (succ (succ b))
 = transport ((predℤ ^ 2) (negsucc b) ≤ℤ_)
     ((ap downRight (upLeft-pred (negsucc b))
      ∙ dR-transform-pred (upLeft (negsucc b)) (pos b)) ⁻¹)
     (ℤ≤-predⁿ-inj _ _ 2 (downRight-upLeft-negsucc b)) 
 
downRight-upLeft : (b : ℤ) → b ≤ℤ downRight (upLeft b)
downRight-upLeft = ℤ-elim _ downRight-upLeft-pos downRight-upLeft-negsucc

downRight-upRight : (b : ℤ) → b ≤ℤ downRight (upRight b)
downRight-upRight b
 = ℤ≤-trans _ _ _ (downRight-upLeft b) (downRight-monotone _ _ (upLeft≤upRight b))
     
above-upRight : (b : ℤ) → b below (upRight b)
above-upRight b = downLeft-upRight b , downRight-upRight b

above-upLeft : (b : ℤ) → b below (upLeft b)
above-upLeft b = downLeft-upLeft  b , downRight-upLeft b

above'-implies-below : (a b : ℤ) → a above' b → b below a
above'-implies-below .(upLeft  b) b (inl refl) = above-upLeft b
above'-implies-below .(upRight b) b (inr refl) = above-upRight b

above-implies-below : (a b : ℤ) → a above b → b below a
above-implies-below a b = above'-implies-below a b ∘ above-implies-above' a b

below-implies-above : (a b : ℤ) → a below b → b above a
below-implies-above a b = below'-implies-above a b ∘ below-implies-below' a b

above-downLeft : (a : ℤ) → a above (downLeft a)
above-downLeft a = below-implies-above (downLeft a) a (downLeft-below a)

above-downMid : (a : ℤ) → a above (downMid a)
above-downMid a = below-implies-above (downMid a) a (downMid-below a)

above-downRight : (a : ℤ) → a above (downRight a)
above-downRight a = below-implies-above (downRight a) a (downRight-below a)
```

Recursive above

```

data Vec (X : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
  [] : Vec X 0
  _++_ : ∀ {n} → X → Vec X n → Vec X (succ n)

[_] : {X : 𝓤 ̇ } → X → Vec X 1
[ x ] = x ++ []

_+++_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → X → Vec X (succ n)
[] +++ x = [ x ]
(h ++ v) +++ x = h ++ (v +++ x)

_!!_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → (k : ℕ) → k <ℕ n → X
((x ++ v) !! zero) k<n = x
((x ++ v) !! succ k) k<n = (v !! k) k<n

!!-prop : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X n)
        → (k₁ k₂ : ℕ) → k₁ ＝ k₂
        → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
        → (xs !! k₁) k₁<n ＝ (xs !! k₂) k₂<n
!!-prop n xs k k refl k₁<n k₂<n = ap (xs !! k) (<-is-prop-valued k n k₁<n k₂<n)

fst lst : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → X
fst xs = (xs !! 0) ⋆
lst {n = n} xs = (xs !! n) (<-succ n)

drop-fst drop-lst : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → Vec X n
drop-fst (x ++ xs) = xs
drop-lst (x ++ []) = []
drop-lst (x ++ (y ++ xs)) = x ++ drop-lst (y ++ xs)

inner : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ (succ n)) → Vec X n
inner = drop-fst ∘ drop-lst

pairwise pairwise-r : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → (p : X → X → 𝓥 ̇ ) → 𝓥 ̇
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

_aboveⁿ_ _belowⁿ_ _aboveⁿ-vec_ _belowⁿ-vec_ : (a c : ℤ) → ℕ → 𝓤₀ ̇ 
_aboveⁿ_     = sigma-witness  _above_
_belowⁿ_     = sigma-witness  _below_
_aboveⁿ-vec_ = vector-witness _above_
_belowⁿ-vec_ = vector-witness _below_

sigma→vector-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → (x y : X) (n : ℕ)
                     → sigma-witness p x y n → vector-witness p x y n
sigma→vector-witness p x y zero η = xs , refl , refl , γ
 where
  xs = x ++ [ y ]
  γ : pairwise xs p
  γ zero ⋆ ⋆ = η
sigma→vector-witness p x y (succ n) (z , η , θ) = xs , refl , pr₁ (pr₂ (pr₂ IH)) , γ
 where
  IH = sigma→vector-witness p z y n θ
  xs = x ++ pr₁ IH
  γ : pairwise xs p
  γ zero k<n k<sn = transport (p x) (pr₁ (pr₂ IH) ⁻¹) η
  γ (succ k) k<n k<sn = pr₂ (pr₂ (pr₂ IH)) k k<n k<sn

vector→sigma-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → (x y : X) (n : ℕ)
                     → vector-witness p x y n → sigma-witness p x y n
vector→sigma-witness p x y zero ((x ++ (y ++ [])) , refl , refl , w) = w 0 ⋆ ⋆
vector→sigma-witness p x y (succ n) ((x ++ (z ++ xs)) , refl , t , w)
 = z , w 0 ⋆ ⋆ , vector→sigma-witness p z y n ((z ++ xs) , refl , t , w ∘ succ)

reverse : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
reverse [] = []
reverse (x ++ xs) = reverse xs +++ x

reverse' : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
reverse' [] = []
reverse' (x ++ []) = [ x ]
reverse' (x ++ (y ++ xs)) = lst (x ++ (y ++ xs)) ++ reverse (drop-lst (x ++ (y ++ xs)))

fst-++ : {X : 𝓤 ̇ } {n : ℕ} → (x : X) (xs : Vec X (succ n))
       → fst (xs +++ x) ＝ fst xs
fst-++ {𝓤} {X} {n} x (y ++ xs) = refl

lst-++ : {X : 𝓤 ̇ } {n : ℕ} → (x : X) (xs : Vec X n)
       → lst (xs +++ x) ＝ x
lst-++ {𝓤} {X} {0}      x []        = refl
lst-++ {𝓤} {X} {succ n} x (y ++ xs) = lst-++ x xs

reverse-fst-becomes-lst : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X (succ n))
                        → lst (reverse xs) ＝ fst xs
reverse-fst-becomes-lst (x ++ xs) = lst-++ x (reverse xs)

reverse-lst-becomes-fst : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X (succ n))
                        → fst (reverse xs) ＝ lst xs
reverse-lst-becomes-fst (x ++ []) = refl
reverse-lst-becomes-fst (x ++ (y ++ xs)) = fst-++ x (reverse (y ++ xs))
                                         ∙ reverse-lst-becomes-fst (y ++ xs)

_−_ : (n k : ℕ) → k ≤ℕ n → ℕ
(n − zero) _ = n
(succ n − succ k) = (n − k)

−-< : (n k : ℕ) → (k≤n : k <ℕ n) → (n − succ k) k≤n <ℕ n
−-< (succ n) zero k≤n = ≤-refl n
−-< (succ (succ n)) (succ zero) k≤n = ≤-succ n
−-< (succ (succ n)) (succ (succ k)) k≤n = <-trans ((n − succ k) k≤n) n (succ (succ n)) (−-< n k k≤n) (<-trans n (succ n) (succ (succ n)) (<-succ n) (<-succ (succ n)))

drop-lst-< : {X : 𝓤 ̇ } (n k : ℕ) → (k<n : k <ℕ n) (k<sn : k <ℕ (succ n))
           → (xs : Vec X  (succ n))
           → (drop-lst xs !! k) k<n
           ＝ (         xs !! k) k<sn
drop-lst-< n zero k<n k<sn (x ++ (y ++ xs)) = refl
drop-lst-< (succ n) (succ k) k<n k<sn (x ++ (y ++ xs)) = drop-lst-< n k k<n k<sn (y ++ xs)

drop-fst-< : {X : 𝓤 ̇ } → (n k : ℕ) → (k<n : k <ℕ n)
           → (xs : Vec X (succ n))
           → (         xs !! succ k) k<n
           ＝ (drop-fst xs !!      k) k<n
drop-fst-< n k k<n (x ++ xs) = refl

drop-fst-++ : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n)) (x : X)
            → drop-fst (xs +++ x) ＝ drop-fst xs +++ x
drop-fst-++ n (y ++ xs) x = refl

drop-lst-++ : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n)) (x : X)
            → drop-lst (x ++ xs) ＝ (x ++ drop-lst xs)
drop-lst-++ n (y ++ xs) x = refl

reverse-drop : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n))
             → reverse (drop-lst xs) ＝ drop-fst (reverse xs)
reverse-drop zero (x ++ []) = refl
reverse-drop (succ n) (x ++ xs)
 = ap reverse (drop-lst-++ n xs x)
 ∙ ap (_+++ x) (reverse-drop n xs)
 ∙ drop-fst-++ n (reverse xs) x ⁻¹

reverse-minus-becomes-k : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X n)
                         → (k : ℕ) → (k<n : k <ℕ n)
                         → (reverse xs !! k) k<n ＝ (xs !! (n − succ k) k<n) (−-< n k k<n)
reverse-minus-becomes-k (x ++ xs) 0 k<n = reverse-lst-becomes-fst (x ++ xs)
reverse-minus-becomes-k {𝓤} {X} {succ (succ n)} (x ++ xs) (succ k) k<n
 = drop-fst-< (succ n) k k<n (reverse xs +++ x)
 ∙ ap (λ - → (- !! k) k<n) (reverse-drop (succ n) (x ++ xs) ⁻¹)
 ∙ reverse-minus-becomes-k {𝓤} {X} {succ n} (drop-lst (x ++ xs)) k k<n
 ∙ drop-lst-< (succ n) ((n − k) k<n) (−-< (succ n) k k<n)
     (−-< (succ (succ n)) (succ k) k<n) (x ++ xs) 

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
       (f _ _ (transport (p _) (γ ⁻¹) (w _ (−-< n k k<n) (−-< (succ n) (succ k) k<n)))))
 where
   γ : (xs !! (n − k) k<sn) (−-< (succ n) k k<sn)
     ＝ (xs !! succ ((n − succ k) k<n)) (−-< n k k<n)
   γ = !!-prop (succ n) xs ((n − k) k<sn) (succ ((n − succ k) k<n)) (−-lemma n k k<sn k<n)
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

below-up : (a c : ℤ) (n : ℕ) → (a belowⁿ c) (succ n)
         → (upLeft a belowⁿ c) n + (upRight a belowⁿ c) n
below-up a c n (b , η , θ)
 = Cases (above-implies-above' b a (below-implies-above a b η))
     (λ l → inl (transport (λ - → (- belowⁿ c) n) l θ))
     (λ r → inr (transport (λ - → (- belowⁿ c) n) r θ))

below-vec' : (a c : ℤ) → (n : ℕ) → (a belowⁿ c) n → Vec ℤ (succ n)
below-vec' a c zero b = [ a ]
below-vec' a c (succ n) (a' , _ , f) = a ++ below-vec' a' c n f

below-vec : (a c : ℤ) → (n : ℕ) → (a belowⁿ c) n → Vec ℤ (succ (succ n))
below-vec a c n b = (below-vec' a c n b) +++ c

below-vec-!!0 : (a c : ℤ) (n : ℕ) (b : (a belowⁿ c) n)
              → (below-vec a c n b !! zero) ⋆ ＝ a
below-vec-!!0 a c zero b = refl
below-vec-!!0 a c (succ n) b = refl

!!-helper : {X : 𝓤 ̇ } {n : ℕ} → (v : Vec X n) → (k₁ k₂ : ℕ)
          → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
          → k₁ ＝ k₂
          → (v !! k₁) k₁<n ＝ (v !! k₂) k₂<n
!!-helper (x ++ v) zero .zero k₁<n k₂<n refl = refl
!!-helper (x ++ v) (succ k) .(succ k) k₁<n k₂<n refl
 = !!-helper v k k k₁<n k₂<n refl

below-vec-!!sn : (a c : ℤ) (n : ℕ) (b : (a belowⁿ c) n)
               → (n<sn : n <ℕ succ n)
               → (below-vec a c n b !! succ n) n<sn ＝ c
below-vec-!!sn a c zero b n<sn = refl
below-vec-!!sn a c (succ n) (b , e , f) n<sn
 = below-vec-!!sn b c n f n<sn

pairwise-below-vec : (a c : ℤ) → (n : ℕ) → (b : (a belowⁿ c) n)
                   → pairwise (below-vec a c n b) _below_
pairwise-below-vec a c zero b zero k<n k<sn
 = b
pairwise-below-vec a c (succ n) (b' , e , f) zero k<n k<sn
 = transport (a below_) (below-vec-!!0 b' c n f ⁻¹) e
pairwise-below-vec a c (succ n) (b' , e , f) (succ k) k<n k<sn
 = pairwise-below-vec b' c n f k k<n k<sn

below-everything-in-vec : (a c : ℤ) → (n : ℕ) → (b : (a belowⁿ c) n)
                        → (k : ℕ) → (k<sn : k <ℕ succ n)
                        → (a belowⁿ ((below-vec a c n b !! (succ k)) k<sn)) k
below-everything-in-vec a c zero b zero k<sn
 = b
below-everything-in-vec a c (succ n) (b , η , θ) zero k<sn
 = transport (a below_) (below-vec-!!0 b c n θ ⁻¹) η 
below-everything-in-vec a c (succ n) (b , η , θ) (succ k) k<sn
 = b , η , below-everything-in-vec b c n θ k k<sn

aboveⁿ-implies-belowⁿ : (a c : ℤ) (n : ℕ) → (c aboveⁿ a) n → (a belowⁿ c) n
aboveⁿ-implies-belowⁿ a c n
 = sigma-witness→inv _above_ _below_ above-implies-below c a n


```

```
upRight≤upLeft-succ : (a : ℤ) → upRight a ＝ upLeft (succℤ a)
upRight≤upLeft-succ a = ap upRight (predsuccℤ _ ⁻¹)

upRight≤upLeft : (a b : ℤ) → a <ℤ b → upRight a ≤ℤ upLeft b
upRight≤upLeft a b (n      , refl)
 = transport (_≤ℤ upLeft (succℤ a +pos n)) (upRight≤upLeft-succ a ⁻¹)
     (upLeft-monotone _ _ (n , refl))

downRight＝downLeft : (a : ℤ) → downRight a ＝ downLeft (succℤ a)
downRight＝downLeft a = ap succℤ (ℤ-left-succ a a ⁻¹ ∙ ℤ+-comm (succℤ a) a)
                     ∙ ℤ-left-succ a (succℤ a) ⁻¹

apparently : (k₁ k₂ c : ℤ)
           → downRight (upLeft k₁) ≤ℤ c ≤ℤ downLeft (upRight k₂)
           → k₁ ≤ℤ c ≤ℤ k₂
apparently k₁ k₂ c (l≤c , c≤u)
 = ℤ≤-trans _ _ _ (downRight-upLeft k₁) l≤c
 , ℤ≤-trans _ _ _ c≤u (downLeft-upRight k₂) 
