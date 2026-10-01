Todd Waugh Ambridge, January 2024

# Structural properties of ternary Boehm encodings

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Notation.Order
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Properties

open import TWA.Thesis.Chapter5.Integers

module TWA.Thesis.Chapter5.BoehmStructure where
\end{code}

## downLeft, downMid and downRight

\begin{code}
downLeft downMid downRight : ℤ → ℤ
downLeft  a = a ℤ+ a
downMid   a = succℤ (downLeft a)
downRight a = succℤ (downMid  a)
\end{code}

## downLeft and downRight properties

\begin{code}
pred-downMid : (a : ℤ) → predℤ (downMid a) ＝ downLeft a
pred-downMid a = predsuccℤ _

pred-downRight : (a : ℤ) → predℤ (downRight a) ＝ downMid a
pred-downRight a = predsuccℤ _

pred-pred-downRight
 : (a : ℤ) → predℤ (predℤ (downRight a)) ＝ downLeft a
pred-pred-downRight a = ap predℤ (predsuccℤ _) ∙ predsuccℤ _

downLeft-monotone' : (a b : ℤ) → ((n , _) : a ≤ℤ b)
                   → downLeft a +pos (n ℕ+ n) ＝ downLeft b
downLeft-monotone' a b (n , refl)
 = ap ((a ℤ+ a) ℤ+_) (distributivity-pos-addition n n ⁻¹)
 ∙ ℤ+-rearrangement (a ℤ+ a) (pos n) (pos n) ⁻¹
 ∙ ap (λ - → (- +pos n) +pos n) (ℤ+-comm a a)
 ∙ ap (_+pos n)
     (ℤ+-assoc a a (pos n)
     ∙ ap (a ℤ+_) (ℤ+-comm a (pos n))
     ∙ ℤ+-assoc a (pos n) a ⁻¹)
 ∙ ℤ+-assoc (a +pos n) a (pos n)

ℤ≤<-trans : (a b c : ℤ) → a ≤ℤ b → b <ℤ c → a <ℤ c
ℤ≤<-trans a b c (m , refl) (n , refl)
 = m ℕ+ n
 , (ap (succℤ a ℤ+_) (distributivity-pos-addition m n ⁻¹)
 ∙ ℤ+-assoc (succℤ a) (pos m) (pos n) ⁻¹ 
 ∙ ap (_+pos n) (ℤ-left-succ-pos a m))

downLeft<<downRight : (a b : ℤ) → a <ℤ b → downLeft a <ℤ downRight b
downLeft<<downRight a b (n , refl)
 = (succ (succ (succ (n ℕ+ n))))
 , ap (succℤ ∘ succℤ)
     (ap succℤ
       (ap (_+pos (n ℕ+ n)) (ℤ-left-succ a a ⁻¹)
       ∙ ap ((succℤ a ℤ+ a) ℤ+_) (distributivity-pos-addition n n ⁻¹)
       ∙ ℤ+-rearrangement (succℤ a ℤ+ a) (pos n) (pos n) ⁻¹
       ∙ ap (λ - → (- +pos n) +pos n) (ℤ+-comm (succℤ a) a)
       ∙ ap (_+pos n)
           (ℤ+-assoc a (succℤ a) (pos n)
         ∙ ap (a ℤ+_) (ℤ+-comm (succℤ a) (pos n))
         ∙ ℤ+-assoc a (pos n) (succℤ a) ⁻¹)
       ∙ ℤ+-assoc (a +pos n) (succℤ a) (pos n))
   ∙ ℤ-left-succ (a +pos n) (succℤ a +pos n) ⁻¹
   ∙ ap (_ℤ+ (succℤ a +pos n)) (ℤ-left-succ-pos a n ⁻¹))

downLeft<downRight
 : (a : ℤ) (n : ℕ)
 → rec a downLeft (succ n) <ℤ rec a downRight (succ n)
downLeft<downRight a zero = 1 , refl
downLeft<downRight a (succ n)
 = downLeft<<downRight _ _ (downLeft<downRight a n)

downLeft≤downRight
 : (a : ℤ) (n : ℕ) → rec a downLeft n ≤ℤ rec a downRight n
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

downRightⁿ-monotone
 : (a b : ℤ) (n : ℕ)
 → a ≤ℤ b
 → rec a downRight (succ n) ≤ℤ rec b downRight (succ n)
downRightⁿ-monotone a b 0 a≤b
 = downRight-monotone a b a≤b
downRightⁿ-monotone a b (succ n) a≤b
 = downRight-monotone _ _ (downRightⁿ-monotone a b n a≤b)

downLeft≤<downRight : (a b : ℤ) → a ≤ℤ b → downLeft a <ℤ downRight b
downLeft≤<downRight a b a≤b
 = ℤ≤<-trans _ _ _ (downLeft-monotone _ _ a≤b) (downLeft<downRight b 0)

downLeft≠downMid : (a b : ℤ) → a ＝ b → downLeft a ≠ downMid b
downLeft≠downMid a a refl
 = ℤ-less-not-equal (downLeft a) (downMid a)
     (0 , refl)

downLeft≠downRight : (a b : ℤ) → a ＝ b → downLeft a ≠ downRight b
downLeft≠downRight a a refl
 = ℤ-less-not-equal (downLeft a) (downRight a)
     (1 , refl)

downMid≠downRight : (a b : ℤ) → a ＝ b → downMid a ≠ downRight b
downMid≠downRight a a refl
 = ℤ-less-not-equal (downMid a) (downRight a)
     (0 , refl)

downRight＝downLeft : (a : ℤ) → downRight a ＝ downLeft (succℤ a)
downRight＝downLeft a
 = ap succℤ (ℤ-left-succ a a ⁻¹ ∙ ℤ+-comm (succℤ a) a)
 ∙ ℤ-left-succ a (succℤ a) ⁻¹
\end{code}

## below and below'

\begin{code}
_below_ : ℤ → ℤ → 𝓤₀ ̇ 
a below b = downLeft b ≤ a ≤ downRight b

downLeft-below  : (a : ℤ) → downLeft a below a
downLeft-below  a = (0 , refl) , (2 , refl)

downMid-below   : (a : ℤ) → downMid a below a
downMid-below   a = (1 , refl) , (1 , refl)

downRight-below : (a : ℤ) → downRight a below a
downRight-below a = (2 , refl) , (0 , refl)

_below'_ : ℤ → ℤ → 𝓤₀ ̇
a below' b = (a ＝ downLeft b) + (a ＝ downMid b) + (a ＝ downRight b)

below'-implies-below : (a b : ℤ) → a below' b → a below b
below'-implies-below .(downLeft  b) b (inl      refl )
 = downLeft-below b
below'-implies-below .(downMid   b) b (inr (inl refl))
 = downMid-below b
below'-implies-below .(downRight b) b (inr (inr refl))
 = downRight-below b

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
below-implies-below' a b
 ((succ (succ (succ n)) , e) , (succ (succ (succ m)) , f))
 = 𝟘-elim (k≠2 k＝2)
 where
   k : ℕ
   k = (succ (succ (succ (succ (succ (succ (n ℕ+ m)))))))
   η : downLeft b +pos k ＝ downRight b
   η = ap ((succℤ ^ 6) ∘ downLeft b ℤ+_)
          (distributivity-pos-addition n m ⁻¹)
     ∙ ap (succℤ ^ 6)
         (ℤ+-assoc (downLeft b) (pos n) (pos m) ⁻¹)
     ∙ ap (succℤ ^ 5)
         (ℤ-left-succ-pos (downLeft b +pos n) m ⁻¹)
     ∙ ap (succℤ ^ 4)
         (ℤ-left-succ-pos (succℤ (downLeft b +pos n)) m ⁻¹)
     ∙ ap (succℤ ^ 3)
         (ℤ-left-succ-pos ((succℤ ^ 2) (downLeft b +pos n)) m ⁻¹)
     ∙ ap ((succℤ ^ 3) ∘ (_+pos m)) e
     ∙ f
   ζ : downLeft b +pos 2 ＝ downRight b
   ζ = refl
   k＝2 : k ＝ 2
   k＝2 = pos-lc (ℤ+-lc (pos k) (pos 2) (downLeft b) (η ∙ ζ ⁻¹))
   k≠2 : k ≠ 2
   k≠2 p = positive-not-zero ((n ℕ+ m) ℕ+ 3) (succ-lc (succ-lc p))
\end{code}

## upLeft and upRight

\begin{code}
upRight : ℤ → ℤ
upRight x = sign x (num x /2)

upLeft : ℤ → ℤ
upLeft x = upRight (predℤ x)
\end{code}

## upLeft and upRight properties

\begin{code}
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

upRight-succ-negsucc
 : (a : ℕ) → upRight (negsucc a) ≤ℤ upRight (succℤ (negsucc a))
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
upLeft-monotone a b (n , refl)
 = upRight-monotone _ _ (n , ℤ-left-pred-pos a n)

upRight≤upLeft-succ : (a : ℤ) → upRight a ＝ upLeft (succℤ a)
upRight≤upLeft-succ a = ap upRight (predsuccℤ _ ⁻¹)

upRight≤upLeft : (a b : ℤ) → a <ℤ b → upRight a ≤ℤ upLeft b
upRight≤upLeft a b (n      , refl)
 = transport (_≤ℤ upLeft (succℤ a +pos n)) (upRight≤upLeft-succ a ⁻¹)
     (upLeft-monotone _ _ (n , refl))

upRight-<-succ-succ : (a : ℤ) → upRight a <ℤ upRight (succℤ (succℤ a))
upRight-<-succ-succ a
 = transport (upRight a <ℤ_) (upRight-suc a ⁻¹) (0 , refl)

upRight-<<' : (a b : ℤ) (n : ℕ) → (a +pos succ n) ＝ predℤ b
            → upRight a <ℤ upRight b
upRight-<<' a b zero e
 = transport (λ - → upRight a <ℤ upRight -)
     (ap succℤ e ∙ succpredℤ _)
     (upRight-<-succ-succ a)
upRight-<<' a b (succ n) e
 = transport (λ - → upRight a <ℤ upRight -)
     (ap succℤ e ∙ succpredℤ _)
     (ℤ≤-trans _ _ _ (upRight-<-succ-succ a)
       (upRight-monotone _ _
       (succ n , ap succℤ (ℤ-left-succ-pos (succℤ a) n
               ∙ ap succℤ (ℤ-left-succ-pos a n)))))
 
upRight-<< : (a b : ℤ) → a <ℤ predℤ b → upRight a <ℤ upRight b
upRight-<< a b (n , e)
 = upRight-<<' a b n (ℤ-left-succ-pos a n ⁻¹ ∙ e)

upLeft-<< : (a b : ℤ) → a <ℤ b → upLeft a <ℤ upRight b
upLeft-<< a b (n , refl)
 = upRight-<< (predℤ a) b
     (n , (ap (_+pos n) (succpredℤ _) ∙ predsuccℤ _ ⁻¹
         ∙ ap predℤ (ℤ-left-succ-pos a n ⁻¹)))
\end{code}

## above and above'

\begin{code}
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

upLeft-＝-+-negsucc
 : (a : ℕ)
 → (upLeft (negsucc a) ＝ upRight (negsucc a))
 + (succℤ (upLeft (negsucc a)) ＝ upRight (negsucc a))
upLeft-＝-+-negsucc 0 = inl refl
upLeft-＝-+-negsucc 1 = inr refl
upLeft-＝-+-negsucc (succ (succ a))
 = Cases (upLeft-＝-+-negsucc a)
      (λ l → inl (upLeft-pred (negsucc a) ∙ ap predℤ l))
      (λ r → inr (predsuccℤ _ ⁻¹ ∙ ap predℤ r))

upLeft-＝-+
 : (a : ℤ) → (upLeft a ＝ upRight a) + (succℤ (upLeft a) ＝ upRight a)
upLeft-＝-+ = ℤ-elim _ upLeft-＝-+-pos upLeft-＝-+-negsucc

upLeft≤upRight : (a : ℤ) → upLeft a ≤ℤ upRight a
upLeft≤upRight a = upRight-monotone _ _ (1 , succpredℤ _)

upLeft-upRight-mono : (a b : ℤ) → a ≤ℤ b → upLeft a ≤ℤ upRight b
upLeft-upRight-mono a b a≤b
 = ℤ≤-trans _ _ _ (upLeft-monotone _ _ a≤b) (upLeft≤upRight b)

upLeft≤upRightⁿ : (a : ℤ) (n : ℕ) → rec a upLeft n ≤ℤ rec a upRight n
upLeft≤upRightⁿ a 0 = ℤ≤-refl a
upLeft≤upRightⁿ a 1 = upLeft≤upRight a
upLeft≤upRightⁿ a (succ (succ n))
 = upLeft-upRight-mono _ _ (upLeft≤upRightⁿ a (succ n))

upLeft-above : (a : ℤ) → upLeft a above a
upLeft-above a = ℤ≤-refl _ , upLeft≤upRight a

upRight-above : (a : ℤ) → upRight a above a
upRight-above a = upLeft≤upRight a , ℤ≤-refl _

above'-implies-above : (a b : ℤ) → a above' b → a above b
above'-implies-above .(upLeft  b) b (inl refl) = upLeft-above b
above'-implies-above .(upRight b) b (inr refl) = upRight-above b

above-implies-above' : (a b : ℤ) → a above b → a above' b
above-implies-above' a b (l≤a , a≤r)
 = Cases (ℤ≤-split (upLeft b) a l≤a)
     (λ l<a → Cases (ℤ≤-split a (upRight b) a≤r)
       (λ a<r → 𝟘-elim
                  (Cases (upLeft-＝-+ b)
                    (λ e → ℤ-less-not-bigger-or-equal (upLeft b) a
                             l<a
                             (transport (a ≤ℤ_) (e ⁻¹) a≤r))
                    (λ e → ℤ-less-not-bigger-or-equal a (upRight b)
                             a<r
                             (transport (_≤ℤ a) e l<a))))
       inr)
     (inl ∘ _⁻¹)
\end{code}

## Relationship between below and above

\begin{code}
upRight-downLeft-pos : (b : ℕ) → pos b ＝ upRight (downLeft (pos b))
upRight-downLeft-pos 0 = refl
upRight-downLeft-pos (succ b)
 = ap succℤ (upRight-downLeft-pos b)
 ∙ upRight-suc (downLeft (pos b)) ⁻¹
 ∙ ap (upRight ∘ succℤ) (ℤ-left-succ-pos (pos b) b ⁻¹)

upRight-downLeft-negsucc
 : (b : ℕ) → negsucc b ＝ upRight (downLeft (negsucc b))
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

upRight-downMid-negsucc
 : (b : ℕ) → negsucc b ＝ upRight (downMid (negsucc b))
upRight-downMid-negsucc 0 = refl
upRight-downMid-negsucc (succ b)
 = ap predℤ (upRight-downMid-negsucc b)
 ∙ upRight-pred (downMid (negsucc b)) ⁻¹
 ∙ ap (upRight ∘ predℤ) (predsuccℤ _)
 ∙ ap upRight (ℤ-left-pred-negsucc (negsucc b) b ⁻¹)
 ∙ ap upRight (succpredℤ _ ⁻¹)

upRight-downLeft : (a : ℤ) → a ＝ upRight (downLeft a)
upRight-downLeft
 = ℤ-elim _ upRight-downLeft-pos upRight-downLeft-negsucc

upRight-downMid : (a : ℤ) → a ＝ upRight (downMid a)
upRight-downMid = ℤ-elim _ upRight-downMid-pos upRight-downMid-negsucc

upRight-downRight : (a : ℤ) → succℤ a ＝ upRight (downRight a)
upRight-downRight a = ap succℤ (upRight-downLeft a)
                    ∙ upRight-suc (downLeft a) ⁻¹

upLeft-downLeft : (a : ℤ) → succℤ (upLeft (downLeft a)) ＝ a
upLeft-downLeft a = upRight-suc (predℤ (downLeft a)) ⁻¹
                  ∙ ap (upRight ∘ succℤ) (succpredℤ _)
                  ∙ upRight-downMid a ⁻¹

upLeft-downMid : (a : ℤ) → upLeft (downMid a) ＝ a
upLeft-downMid a = ap upRight (pred-downMid a) ∙ upRight-downLeft a ⁻¹

upLeft-downRight : (a : ℤ) → upLeft (downRight a) ＝ a
upLeft-downRight a
 = ap upRight (pred-downRight a) ∙ upRight-downMid a ⁻¹

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

dL-transform-pred
 : (a : ℤ) → downLeft (predℤ a) ＝ (predℤ ^ 2) (downLeft a)
dL-transform-pred a
 = ℤ-left-pred a (predℤ a) ∙ ap predℤ (ℤ-right-pred a a)

dR-transform
 : (a : ℤ) → downRight (succℤ a) ＝ (succℤ ^ 2) (downRight a)
dR-transform a = ap (succℤ ^ 2) (dL-transform a)

dR-transform-pred
 : (a b : ℤ) → downRight (predℤ a) ＝ (predℤ ^ 2) (downRight a)
dR-transform-pred a b = ap (succℤ ^ 2) (dL-transform-pred a)
                      ∙ ap succℤ (succpredℤ _)
                      ∙ succpredℤ _
                      ∙ predsuccℤ _ ⁻¹
                      ∙ ap predℤ (predsuccℤ _ ⁻¹)

downLeft-upRight : (b : ℤ) → downLeft (upRight b) ≤ℤ b
downLeft-upRight
 = ℤ-elim _ downLeft-upRight-pos downLeft-upRight-negsucc
 where
  downLeft-upRight-pos : (b : ℕ) → downLeft (upRight (pos b)) ≤ℤ pos b
  downLeft-upRight-pos 0 = 0 , refl
  downLeft-upRight-pos 1 = 1 , refl
  downLeft-upRight-pos (succ (succ b))
   = transport (_≤ℤ succℤ (succℤ (pos b)))
      ((ap downLeft (upRight-suc (pos b))
        ∙ dL-transform (upRight (pos b))) ⁻¹)
      (ℤ≤-succⁿ-inj _ _ 2 (downLeft-upRight-pos b))
  downLeft-upRight-negsucc
   : (b : ℕ) → downLeft (upRight (negsucc b)) ≤ℤ negsucc b
  downLeft-upRight-negsucc 0 = 1 , refl
  downLeft-upRight-negsucc 1 = 0 , refl
  downLeft-upRight-negsucc (succ (succ b))
   = transport (_≤ℤ predℤ (predℤ (negsucc b)))
       ((ap downLeft (upRight-pred (negsucc b))
         ∙ dL-transform-pred (upRight (negsucc b))) ⁻¹)
       (ℤ≤-predⁿ-inj _ _ 2 (downLeft-upRight-negsucc b))

downLeft-upLeft  : (b : ℤ) → downLeft (upLeft b) ≤ℤ b
downLeft-upLeft b
 = ℤ≤-trans _ _ _
     (downLeft-monotone _ _ (upLeft≤upRight b))
     (downLeft-upRight b)

downRight-upLeft-pos : (b : ℕ) → pos b ≤ℤ downRight (upLeft (pos b))
downRight-upLeft-pos 0 = 0 , refl
downRight-upLeft-pos 1 = 1 , refl
downRight-upLeft-pos (succ (succ b))
 = transport ((succℤ ^ 2) (pos b) ≤ℤ_)
    ((ap downRight (upLeft-suc (pos b))
      ∙ dR-transform (upLeft (pos b))) ⁻¹)
    (ℤ≤-succⁿ-inj _ _ 2 (downRight-upLeft-pos b))

downRight-upLeft-negsucc
 : (b : ℕ) → negsucc b ≤ℤ downRight (upLeft (negsucc b))
downRight-upLeft-negsucc 0 = 1 , refl
downRight-upLeft-negsucc 1 = 0 , refl
downRight-upLeft-negsucc (succ (succ b))
 = transport ((predℤ ^ 2) (negsucc b) ≤ℤ_)
     ((ap downRight (upLeft-pred (negsucc b))
      ∙ dR-transform-pred (upLeft (negsucc b)) (pos b)) ⁻¹)
     (ℤ≤-predⁿ-inj _ _ 2 (downRight-upLeft-negsucc b)) 
 
downRight-upLeft : (b : ℤ) → b ≤ℤ downRight (upLeft b)
downRight-upLeft
 = ℤ-elim _ downRight-upLeft-pos downRight-upLeft-negsucc

downRight-upRight : (b : ℤ) → b ≤ℤ downRight (upRight b)
downRight-upRight b
 = ℤ≤-trans _ _ _
     (downRight-upLeft b)
     (downRight-monotone _ _ (upLeft≤upRight b))
     
above-upRight : (b : ℤ) → b below (upRight b)
above-upRight b = downLeft-upRight b , downRight-upRight b

above-upLeft : (b : ℤ) → b below (upLeft b)
above-upLeft b = downLeft-upLeft  b , downRight-upLeft b

above'-implies-below : (a b : ℤ) → a above' b → b below a
above'-implies-below .(upLeft  b) b (inl refl) = above-upLeft b
above'-implies-below .(upRight b) b (inr refl) = above-upRight b

above-implies-below : (a b : ℤ) → a above b → b below a
above-implies-below a b
 = above'-implies-below a b ∘ above-implies-above' a b

below-implies-above : (a b : ℤ) → a below b → b above a
below-implies-above a b
 = below'-implies-above a b ∘ below-implies-below' a b

above-downLeft : (a : ℤ) → a above (downLeft a)
above-downLeft a
 = below-implies-above (downLeft a) a (downLeft-below a)

above-downMid : (a : ℤ) → a above (downMid a)
above-downMid a
 = below-implies-above (downMid a) a (downMid-below a)

above-downRight : (a : ℤ) → a above (downRight a)
above-downRight a
 = below-implies-above (downRight a) a (downRight-below a)
\end{code}
