[⇐ Index](../html/TWA.Thesis.index.html)

# Ternary Boehm encodings of real numbers

```agda
{-# OPTIONS --exact-split --without-K --safe #-}

open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Notation.Order
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open import TWA.Thesis.Chapter5.BelowAndAbove
 hiding (downLeft; downMid; downRight; upRight; upLeft; _below_)
open import TWA.Thesis.AndrewSneap.DyadicRationals
 renaming (normalise to ι)
open import TWA.Thesis.Chapter5.Integers
open import TWA.Thesis.Chapter5.SignedDigit

module TWA.Thesis.Chapter5.BoehmVerification
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (dy : Dyadics)
  where

open PropositionalTruncation pt
open Dyadics dy
  renaming ( _ℤ[1/2]+_ to _+𝔻_ ; ℤ[1/2]-_ to -_ ; _ℤ[1/2]-_ to _-_
           ; _ℤ[1/2]*_ to _*_ )

open import TWA.Thesis.AndrewSneap.DyadicReals pe pt fe dy
open import TWA.Thesis.Chapter3.ClosenessSpaces fe hiding (⟨_⟩ ; ι)
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
```

## Structural operations and properties

```
downLeft downMid downRight : ℤ → ℤ
downLeft  k = (k ℤ+ k)
downMid   k = (k ℤ+ k) +pos 1
downRight k = (k ℤ+ k) +pos 2

upRight upLeft : ℤ → ℤ
upRight k = sign k (num k /2)
upLeft  k = upRight (predℤ k)

_below_ : ℤ → ℤ → 𝓤₀ ̇
a below b = downLeft b ≤ a ≤ downRight b

ternary : (ℤ → ℤ) → 𝓤₀  ̇
ternary x = (δ : ℤ) → x (succℤ δ) below x δ

𝕋 : 𝓤₀ ̇ 
𝕋 = Σ x ꞉ (ℤ → ℤ) , ternary x

ℤ[1/2]ᴵ : 𝓤₀ ̇
ℤ[1/2]ᴵ = Σ (l , r) ꞉ (ℤ[1/2] × ℤ[1/2]) , l ≤ r

ld rd : ℤ[1/2]ᴵ → ℤ[1/2]
ld ((l , r) , _) = l
rd ((l , r) , _) = r

ld≤rd : (p : ℤ[1/2]ᴵ) → ld p ≤ rd p
ld≤rd ((l , r) , l≤r) = l≤r

_covers_ : ℤ[1/2]ᴵ → ℤ[1/2]ᴵ → 𝓤₀ ̇
a covers b = (ld a ≤ ld b) × (rd b ≤ rd a)

covers-refl : (ab : ℤ[1/2]ᴵ) → ab covers ab
covers-refl ab = ≤-refl (ld ab) , ≤-refl (rd ab)

covers-trans : (a b c : ℤ[1/2]ᴵ) → a covers b → b covers c → a covers c
covers-trans a b c (l≤₁ , r≤₁) (l≤₂ , r≤₂)
 = trans' (ld a) (ld b) (ld c) l≤₁ l≤₂
 , trans' (rd c ) (rd b) (rd a) r≤₂ r≤₁

nested positioned : (ℤ → ℤ[1/2]ᴵ) → 𝓤₀ ̇
nested      ζ = (n : ℤ) → (ζ n) covers (ζ (succℤ n))
positioned     ζ = (ϵ : ℤ[1/2]) → is-positive ϵ
              → Σ n ꞉ ℤ , (rd (ζ n) - ld (ζ n)) ≤ ϵ

fully-nested' : (ℤ → ℤ[1/2]ᴵ) → ℕ → 𝓤₀ ̇
fully-nested' ζ k = (n : ℤ) → (ζ n) covers (ζ (n +pos k))

fully-nested : (ℤ → ℤ[1/2]ᴵ) → 𝓤₀ ̇
fully-nested ζ = (n m : ℤ) → n ≤ m → (ζ n) covers (ζ m)

nested-implies-fully-nested'
 : (ζ : ℤ → ℤ[1/2]ᴵ) → nested ζ → Π (fully-nested' ζ)
nested-implies-fully-nested' ζ ρ 0 n = (0 , refl) , (0 , refl)
nested-implies-fully-nested' ζ ρ (succ k) n
 = covers-trans (ζ n) (ζ (succℤ n)) (ζ (succℤ (n +pos k))) (ρ n)
     (nested-implies-fully-nested' (ζ ∘ succℤ) (ρ ∘ succℤ) k n)

nested-implies-fully-nested
 : (ζ : ℤ → ℤ[1/2]ᴵ) → nested ζ → fully-nested ζ
nested-implies-fully-nested ζ ρ n m (k , refl)
 = nested-implies-fully-nested' ζ ρ k n
```

## Verification of the structure of ternary Boehm encodings

```
-- By Andrew Sneap
⦅_⦆ : (χ : ℤ → ℤ[1/2]ᴵ) → nested χ → positioned χ → ℝ-d
⦅_⦆ χ τ π = (L , R)
          , inhabited-l , inhabited-r
          , rounded-l   , rounded-r
          , is-disjoint , is-located
 where
  L R : ℤ[1/2] → Ω 𝓤₀
  L p = (∃ n ꞉ ℤ , p < ld (χ n)) , ∃-is-prop
  R q = (∃ n ꞉ ℤ , rd (χ n) < q) , ∃-is-prop

  
  inhabited-l : inhabited-left L
  inhabited-l = ∣ ld (χ (pos 0)) - 1ℤ[1/2]
              , ∣ (pos 0)
                  , (ℤ[1/2]<-neg (ld (χ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2]) ∣ ∣
  
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (rd (χ (pos 0)) +𝔻 1ℤ[1/2])
              , ∣ pos 0
                  , ℤ[1/2]<-+ (rd (χ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  
  rounded-l : rounded-left L
  rounded-l p = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))
        → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld (χ n')))
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))
        → Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n' ꞉ ℤ , (p' <ℤ[1/2] ld (χ n')))
      I (n , p<ζn) = let (p' , p<p' , p'<ζn) = dense p (ld (χ n)) p<ζn
                     in p' , (p<p' , ∣ n , p'<ζn ∣)
    rtl : ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] ld (χ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ p' ꞉ ℤ[1/2] , p < p' × (∃ n ꞉ ℤ , (p' <ℤ[1/2] ld (χ n)))
        → ∃ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))
      I (p' , p<p' , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (p' <ℤ[1/2] ld (χ n))
           → Σ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))
        II (n  , p'<ζn) = n , (trans p p' (ld (χ n)) p<p' p'<ζn)
      
  rounded-r : rounded-right R
  rounded-r q = ltr , rtl
   where
    ltr : ∃ n ꞉ ℤ , rd (χ n) < q → ∃ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
    ltr = ∥∥-functor I
     where
      I : Σ n ꞉ ℤ , rd (χ n) < q → Σ q' ꞉ ℤ[1/2] , q' < q × q' ∈ R
      I (n , ζn<q) = let (q' , ζn<q' , q'<q) = dense (rd (χ n)) q ζn<q
                     in q' , (q'<q , ∣ n , ζn<q' ∣)
    rtl : ∃ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
    rtl = ∥∥-rec ∃-is-prop I
     where
      I : Σ q' ꞉ ℤ[1/2] , q' < q × (R q' holds) → R q holds
      I (q' , q'<q , te) = ∥∥-functor II te
       where
        II : Σ n ꞉ ℤ , (rd (χ n) < q') → Σ n ꞉ ℤ , (rd (χ n) <ℤ[1/2] q)
        II (n , ζ<q') = n , (trans (rd (χ n)) q' q ζ<q' q'<q)
  
  is-disjoint : disjoint L R
  is-disjoint p q (tp<x , tx<q)
   = ∥∥-rec (<ℤ[1/2]-is-prop p q)
       (λ ((n , p<l) , (n' , r<q))
        → I n n' p<l r<q (ℤ-dichotomous n n'))
       (binary-choice tp<x tx<q)
   where
    I : (n n' : ℤ)
      → p <ℤ[1/2] ld (χ n)
      → rd (χ n') <ℤ[1/2] q
      → (n ≤ n') + (n' ≤ n)
      → p <ℤ[1/2] q
    I n n' p<l r<q (inl n≤n')
      = let p<l' = ℤ[1/2]<-≤ p (ld (χ n)) (ld (χ n')) p<l
                     (pr₁ (nested-implies-fully-nested
                             χ τ n n' n≤n'))
            l<q' = ℤ[1/2]≤-< (ld (χ n')) (rd (χ n')) q
                     (ld≤rd (χ n')) r<q 
      in trans p (ld (χ n')) q p<l' l<q'
    I n n' p<l r<q (inr n'≤n)
      = let p<r' = ℤ[1/2]<-≤ p (ld (χ n)) (rd (χ n)) p<l
                     (ld≤rd (χ n))
            r<q' = ℤ[1/2]≤-< (rd (χ n)) (rd (χ n')) q
                     (pr₂ (nested-implies-fully-nested
                        χ τ n' n n'≤n)) r<q
      in trans p (rd (χ n)) q p<r' r<q'
 
  is-located : located L R
  is-located p q p<q
   = I (π (1/2ℤ[1/2] * (q - p))
         (ℤ[1/2]<-positive-mult 1/2ℤ[1/2] (q - p)
            0<1/2ℤ[1/2] (diff-positive p q p<q)))
   where
    0<ε : 0ℤ[1/2] < (1/2ℤ[1/2] * (q - p))
    0<ε = <-pos-mult' 1/2ℤ[1/2] (q - p) 0<1/2ℤ[1/2]
            (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((rd (χ n) - ld (χ n))
                     ≤ℤ[1/2] (1/2ℤ[1/2] * (q - p))))
      → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (rd (χ n))
                       (ld (χ n)) q p l₂)
     where
      l₂ :(rd (χ n) - ld (χ n)) < (q - p)
      l₂ = ℤ[1/2]≤-< (rd (χ n) - ld (χ n)) (1/2ℤ[1/2] * (q - p))
             (q - p) l₁ (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : (rd (χ n) < q) + (p < ld (χ n)) → (L p holds) ∨ (R q holds) 
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣
  
ℤ³ : 𝓤₀ ̇
ℤ³ = Σ ((l , r) , p) ꞉ ((ℤ × ℤ) × ℤ) , l ≤ r

ℤ³-to-ℤ[1/2]ᴵ : ℤ³ → ℤ[1/2]ᴵ
ℤ³-to-ℤ[1/2]ᴵ (((l , r) , p) , i)
 = ((ι (l , p)) , ι (r , p)) , normalise-≤2 l r p i

⦅_⦆' : (χ : ℤ → ℤ³)
      → nested (ℤ³-to-ℤ[1/2]ᴵ ∘ χ) → positioned (ℤ³-to-ℤ[1/2]ᴵ ∘ χ)
      → ℝ-d
⦅ χ ⦆' = ⦅ ℤ³-to-ℤ[1/2]ᴵ ∘ χ ⦆

ℤ² : 𝓤₀ ̇ 
ℤ² = ℤ × ℤ

ℤ²-to-ℤ³ : ℤ² → ℤ³
ℤ²-to-ℤ³ (k , p)
 = (((k , k +pos 2) , p)
 , ℤ≤-trans k (succℤ k) (succℤ (succℤ k))
     (≤-incrℤ k) (≤-incrℤ (succℤ k)))

ℤ²-to-ℤ[1/2]ᴵ : ℤ² → ℤ[1/2]ᴵ
ℤ²-to-ℤ[1/2]ᴵ = ℤ³-to-ℤ[1/2]ᴵ ∘ ℤ²-to-ℤ³

⦅_⦆'' : (χ : ℤ → ℤ²)
      → nested  (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
      → positioned (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
      → ℝ-d
⦅_⦆'' = ⦅_⦆' ∘ (ℤ²-to-ℤ³ ∘_)

normalised : (ℤ → ℤ²) → 𝓤₀ ̇ 
normalised χ = (n : ℤ) → pr₂ (χ n) ＝ n

ℤ²-width : ((k , p) : ℤ²)
         → (ι (k +pos 2 , p) - ι (k , p)) ＝ ι (pos 2 , p)
ℤ²-width (k , p)
 = normalise-negation (k +pos 2) k p
 ∙ ap (λ - → ι (- , p))
     (ℤ-left-succ (succℤ k) (ℤ- k)
     ∙ ap succℤ (ℤ-left-succ k (ℤ- k))
     ∙ ap (succℤ ∘ succℤ) (ℤ-sum-of-inverse-is-zero k))

normalised-positioned : (χ : ℤ → ℤ²)
                   → normalised χ
                   → positioned (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
normalised-positioned χ η ϵ ϵ⁺
 = q , transport (_≤ ϵ) (ℤ²-width (χ q) ⁻¹)
         (transport (λ - → ι (pos 2 , -) ≤ ϵ) (η q ⁻¹) γ)
 where
  q : ℤ
  q = pr₁ (ℤ[1/2]-find-lower ϵ ϵ⁺)
  f : pr₁ (ℤ[1/2]-find-lower ϵ ϵ⁺) ＝
        pr₂ (χ (pr₁ (ℤ[1/2]-find-lower ϵ ϵ⁺)))
  f = η q ⁻¹
  γ : ι (pos 2 , q) ≤ ϵ
  γ = <-is-≤ℤ[1/2] (ι (pos 2 , q)) ϵ (pr₂ (ℤ[1/2]-find-lower ϵ ϵ⁺))

ℤ≤-succ' : (a : ℤ) (n : ℕ) → succℤ a ≤ succℤ (a +pos n)
ℤ≤-succ' a zero = zero , refl
ℤ≤-succ' a (succ n) = ℤ≤-trans _ _ _ (ℤ≤-succ' a n) (1 , refl)

ℤ≤-succ : (a b : ℤ) → a ≤ b → succℤ a ≤ succℤ b
ℤ≤-succ a b (n , refl) = ℤ≤-succ' a n

ℤ≤-pred'
 : (a : ℤ) (n : ℕ) → a ≤ (a +pos n)
ℤ≤-pred' a n = n , refl

ℤ≤-pred : (a b : ℤ) → succℤ a ≤ succℤ b → a ≤ b
ℤ≤-pred a b (n , e)
  = transport (a ≤_)
      (succℤ-lc (ℤ-left-succ-pos a n ⁻¹ ∙ e))
      (ℤ≤-pred' a n)

downLeft-downRight-2
 : (a : ℤ) → downLeft (a +pos 2) ＝ downRight a +pos 2
downLeft-downRight-2 a
 = ℤ-left-succ (succℤ a) (succℤ (succℤ a))
 ∙ ap succℤ (ℤ-left-succ a (succℤ (succℤ a)))
 ∙ ap (succℤ ^ 2)
     (ℤ-right-succ a (succℤ a)
     ∙ ap succℤ (ℤ-right-succ a a))

ℤ³-width : ((((l , r) , p) , _) : ℤ³)
         → (ι (r , p) - ι (l , p)) ＝ ι (r ℤ- l , p)
ℤ³-width (((l , r) , p) , _) = normalise-negation r l p

ternary-nested : (χ : ℤ → ℤ²)
               → normalised χ
               → ternary (pr₁ ∘ χ)
               ↔ nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
pr₁ (pr₁ (ternary-nested χ η) f n) = γ
 where
  γ' : ι (pr₁ (χ n) , n) ≤ ι (pr₁ (χ (succℤ n)) , succℤ n)
  γ' = transport (_≤ ι (pr₁ (χ (succℤ n)) , succℤ n))
         (normalise-succ' (pr₁ (χ n)) n ⁻¹)
         (normalise-≤2
           (pr₁ (χ n) ℤ+ pr₁ (χ n))
           (pr₁ (χ (succℤ n)))
           (succℤ n)
           (pr₁ (f n)))
  γ : ι (χ n) ≤ ι (χ (succℤ n))
  γ = transport (λ - → ι (pr₁ (χ n) , -)
                 ≤ ι (χ (succℤ n)))
        (η n ⁻¹)
        (transport (λ - → ι (pr₁ (χ n) , n)
                        ≤ ι (pr₁ (χ (succℤ n)) , -))
          (η (succℤ n) ⁻¹)
          γ')
pr₂ (pr₁ (ternary-nested χ η) f n) 
 = transport (λ - → ι ((pr₁ (χ (succℤ n)) +pos 2) , -)
                  ≤ ι ((pr₁ (χ n) +pos 2) , pr₂ (χ n)))
     (η (succℤ n) ⁻¹)
     (transport (λ - → ι ((pr₁ (χ (succℤ n)) +pos 2) , succℤ n)
                     ≤ ι ((pr₁ (χ n) +pos 2) , -))
        (η n ⁻¹)
        (transport (ι ((pr₁ (χ (succℤ n)) +pos 2) , succℤ n) ≤_)
          (normalise-succ' (pr₁ (χ n) +pos 2) n ⁻¹)
          (normalise-≤2
            (pr₁ (χ (succℤ n)) +pos 2)
            ((pr₁ (χ n) +pos 2) ℤ+ (pr₁ (χ n) +pos 2))
            (succℤ n)
            (transport ((pr₁ (χ (succℤ n)) +pos 2) ≤_)
              (downLeft-downRight-2 (pr₁ (χ n)) ⁻¹)
              (ℤ≤-succ _ _ (ℤ≤-succ _ _ (pr₂ (f n))))))))
pr₁ (pr₂ (ternary-nested χ η) f n)
 = from-normalise-≤-same-denom _ _ (succℤ n) γ
 where
  γ' : ι (pr₁ (χ n) , n) ≤ ι (pr₁ (χ (succℤ n)) , succℤ n)
  γ' = transport (λ - → ι (pr₁ (χ n) , -)
                      ≤ ι (pr₁ (χ (succℤ n)) , succℤ n))
         (η n)
         (transport (λ - → ι (χ n) ≤ ι (pr₁ (χ (succℤ n)) , -))
           (η (succℤ n))
           (pr₁ (f n)))
  γ : ι (downLeft (pr₁ (χ n)) , succℤ n)
    ≤ ι (pr₁ (χ (succℤ n)) , succℤ n)
  γ = transport (_≤ ι (pr₁ (χ (succℤ n)) , succℤ n))
        (normalise-succ' (pr₁ (χ n)) n)
        γ'
pr₂ (pr₂ (ternary-nested χ η) f n)
 = ℤ≤-pred _ _ (ℤ≤-pred _ _
     (from-normalise-≤-same-denom _ _ (succℤ n) γ))
 where
  γ'' : ι (pr₁ (χ (succℤ n)) +pos 2 , succℤ n)
      ≤ ι (pr₁ (χ n) +pos 2 , n)
  γ'' = transport (λ - → ι (pr₁ (χ (succℤ n)) +pos 2 , -)
                       ≤ ι (pr₁ (χ n) +pos 2 , n))
          (η (succℤ n))
          (transport (λ - → ι (pr₁ (χ (succℤ n)) +pos 2
                             , pr₂ (χ (succℤ n)))
                          ≤ ι (pr₁ (χ n) +pos 2 , -))
            (η n)
            (pr₂ (f n)))
  γ' : ι (pr₁ (χ (succℤ n)) +pos 2 , succℤ n)
     ≤ ι (downLeft (pr₁ (χ n) +pos 2) , succℤ n)
  γ' = transport (ι (pr₁ (χ (succℤ n)) +pos 2 , succℤ n) ≤_)
        (normalise-succ' (pr₁ (χ n) +pos 2) n)
        γ''
  γ : ι (pr₁ (χ (succℤ n)) +pos 2 , succℤ n)
    ≤ ι (downRight (pr₁ (χ n)) +pos 2 , succℤ n)
  γ = transport (λ - → ι (pr₁ (χ (succℤ n)) +pos 2 , succℤ n)
                     ≤ ι (- , succℤ n))
        (downLeft-downRight-2 (pr₁ (χ n)))
        γ'

to-interval-seq : 𝕋 → (ℤ → ℤ²)
to-interval-seq χ n = (pr₁ χ n) , n

𝕋→nested-normalised
 : 𝕋 → Σ χ ꞉ (ℤ → ℤ²) , (nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ) × normalised χ)
𝕋→nested-normalised χ
 = to-interval-seq χ
 , pr₁ (ternary-nested _ i) (pr₂ χ)
 , i
 where
   i : normalised (to-interval-seq χ)
   i n = refl

ternary-normalised→𝕋
 : Σ χ ꞉ (ℤ → ℤ²) , (nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ) × normalised χ) → 𝕋
ternary-normalised→𝕋 (χ , τ , π)
 = (pr₁ ∘ χ) , pr₂ (ternary-nested χ π) τ

open import UF.Equiv

covers-is-prop : (a b : ℤ[1/2]ᴵ) → is-prop (a covers b)
covers-is-prop ((l₁ , r₁) , _) ((l₂ , r₂) , _)
 = ×-is-prop (≤ℤ[1/2]-is-prop l₁ l₂) (≤ℤ[1/2]-is-prop r₂ r₁)

nested-is-prop : (χ : ℤ → ℤ[1/2]ᴵ) → is-prop (nested χ)
nested-is-prop χ
 = Π-is-prop (fe _ _) (λ n → covers-is-prop (χ n) (χ (succℤ n)))

normalised-is-prop : (χ : ℤ → ℤ²) → is-prop (normalised χ)
normalised-is-prop χ = Π-is-prop (fe _ _) (λ _ → ℤ-is-set)

nested-×-normalised-is-prop
 : (χ : ℤ → ℤ²)
 → is-prop (nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ) × normalised χ)
nested-×-normalised-is-prop χ
 = ×-is-prop (nested-is-prop (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
             (normalised-is-prop χ)

below-is-prop : (a b : ℤ) → is-prop (a below b)
below-is-prop a b
 = ×-is-prop (ℤ≤-is-prop (downLeft b) a)
             (ℤ≤-is-prop a (downRight b))

ternary-is-prop : (χ : ℤ → ℤ) → is-prop (ternary χ)
ternary-is-prop χ
 = Π-is-prop (fe _ _) (λ n → below-is-prop (χ (succℤ n)) (χ n)) 

ternary-normalised≃𝕋 : (Σ χ ꞉ (ℤ → ℤ²)
                     , (nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                     × normalised χ))
                     ≃ 𝕋
ternary-normalised≃𝕋
 = qinveq ternary-normalised→𝕋 (𝕋→nested-normalised , ρ , μ)
 where
  ρ : 𝕋→nested-normalised ∘ ternary-normalised→𝕋 ∼ id
  ρ (χ , τ , π)
   = to-subtype-＝ nested-×-normalised-is-prop (dfunext (fe _ _) γ)
   where
    γ : to-interval-seq (ternary-normalised→𝕋 (χ , τ , π)) ∼ χ
    γ i = ap (pr₁ (χ i) ,_) (π i ⁻¹)
  μ : (ternary-normalised→𝕋 ∘ 𝕋→nested-normalised) ∼ id
  μ (χ , b) = to-subtype-＝ ternary-is-prop (dfunext (fe _ _) γ)
   where
    γ : (λ x → pr₁ (pr₁ (𝕋→nested-normalised (χ , b)) x)) ∼ χ
    γ i = refl

𝕋→nested-positioned
 : 𝕋
 → Σ χ ꞉ (ℤ → ℤ²) , (nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                  × positioned (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
𝕋→nested-positioned χ
 = χ' , τ , normalised-positioned χ' π
 where
  γ = 𝕋→nested-normalised χ
  χ' = pr₁ γ 
  τ  = pr₁ (pr₂ γ)
  π  = pr₂ (pr₂ γ)

⟦_⟧ : 𝕋 → ℝ-d
⟦ χ ⟧ = ⦅ χ' ⦆'' τ π
 where
  γ = 𝕋→nested-positioned χ
  χ' = pr₁ γ 
  τ  = pr₁ (pr₂ γ)
  π  = pr₂ (pr₂ γ)
```

## Representing compact intervals

``` 
CompactInterval : ℤ × ℤ → 𝓤₀ ̇
CompactInterval (k , δ) = Σ (x , _) ꞉ 𝕋 , x(δ) ＝ k

CompactInterval2 : ℤ × ℤ → 𝓤₀ ̇
CompactInterval2 (k , δ)
 = Σ χ ꞉ (ℕ → ℤ) , (χ 0 below k)
                 × ((n : ℕ) → χ (succ n) below χ n)

CompactInterval-1-to-2 : ((k , δ) : ℤ × ℤ)
                       → CompactInterval  (k , δ)
                       → CompactInterval2 (k , δ)
CompactInterval-1-to-2 (k , δ) ((χ' , b') , e')
 = χ , transport (χ' (succℤ δ) below_) e' (b' δ) , bₛ
 where
  χ : ℕ → ℤ
  χ n =  χ' (succℤ (δ +pos n))
  b₀ : χ 0 below χ' δ
  b₀ = b' δ
  bₛ : (n : ℕ) → χ (succ n) below χ n
  bₛ n = b' (succℤ (δ +pos n))

replace-right''
 : ((k , δ) : ℤ × ℤ) → (ℕ → ℤ) → (n : ℤ) → trich-locate n δ → ℤ
replace-right'' (k , δ) χ n (inl (i , n+si＝δ))
 = (upRight ^ succ i) k
replace-right'' (k , δ) χ n (inr (inl refl))
 = k
replace-right'' (k , δ) χ n (inr (inr (i , δ+si＝n)))
 = χ i

replace-right''-correct
 : ((k , δ) : ℤ × ℤ)
 → (χ : ℕ → ℤ)
 → χ 0 below k
 → ((n : ℕ) → χ (succ n) below χ n) 
 → (n : ℤ)
 → (η : trich-locate n δ)
 →       replace-right'' (k , δ) χ (succℤ n) (ℤ-trich-succ n δ η)
   below replace-right'' (k , δ) χ n η
replace-right''-correct (k , δ) χ b₀ bₛ n (inl (0      , refl))
 = above-implies-below _ _ (upRight-above _)
replace-right''-correct (k , δ) χ b₀ bₛ n (inl (succ i , refl))
 = above-implies-below _ _ (upRight-above _)
replace-right''-correct (k , δ) χ b₀ bₛ n (inr (inl refl))
 = b₀
replace-right''-correct (k , δ) χ b₀ bₛ n (inr (inr (i , refl)))
 = bₛ i

CompactInterval-2-to-1 : ((k , δ) : ℤ × ℤ)
                       → CompactInterval2 (k , δ)
                       → CompactInterval  (k , δ)
CompactInterval-2-to-1 (k , δ) (χ' , b'₀ , b'ₛ)
 = (χ , b) , e
 where
  χ : ℤ → ℤ
  χ n = replace-right'' (k , δ) χ' n (ℤ-trichotomous n δ)
  b' : (n : ℤ) → replace-right'' (k , δ) χ' (succℤ n)
                   (ℤ-trich-succ n δ (ℤ-trichotomous n δ))
                 below
                 replace-right'' (k , δ) χ' n (ℤ-trichotomous n δ)
  b' n = replace-right''-correct (k , δ) χ' b'₀ b'ₛ n
           (ℤ-trichotomous n δ)
  b : (n : ℤ) → χ (succℤ n) below χ n
  b n = transport (λ - → replace-right'' (k , δ) χ' (succℤ n) -
                         below χ n)
          (ℤ-trichotomous-is-prop _ _
            (ℤ-trich-succ n δ (ℤ-trichotomous n δ))
            (ℤ-trichotomous (succℤ n) δ))
          (b' n)
  e : χ δ ＝ k
  e = ap (replace-right'' (k , δ) χ' δ)
        (ℤ-trichotomous-is-prop _ _ (ℤ-trichotomous δ δ)
        (inr (inl refl)))

_≈_ : 𝕋 → 𝕋 → 𝓤₀ ̇
(χ₁ , _) ≈ (χ₂ , _) = Σ δ ꞉ ℤ , ((n : ℤ) → δ ≤ n → χ₁ n ＝ χ₂ n)

CompactInterval-≈
 : ((k , δ) : ℤ × ℤ)
 → ((χ , b) : CompactInterval (k , δ))
 → χ ≈ pr₁ (CompactInterval-2-to-1 (k , δ)
             (CompactInterval-1-to-2 (k , δ) (χ , b)))
CompactInterval-≈ (k , δ) ((χ' , b') , e') = δ , γ
 where
  χ = pr₁ (CompactInterval-2-to-1 (k , δ)
             (CompactInterval-1-to-2 (k , δ) ((χ' , b') , e')))
  γ : (n : ℤ) → δ ≤ n → χ' n ＝ pr₁ χ n
  γ n (0 , refl)
   = e'
   ∙ ap (replace-right'' (k , δ)
       (pr₁ (CompactInterval-1-to-2 (k , δ) ((χ' , b') , e'))) δ)
       (ℤ-trichotomous-is-prop _ _
         (ℤ-trichotomous δ δ)
         (inr (inl refl))) ⁻¹
  γ n (succ i , refl)
   = ap (replace-right'' (k , δ)
       (pr₁ (CompactInterval-1-to-2 (k , δ) ((χ' , b') , e')))
       (δ +pos succ i))
       (ℤ-trichotomous-is-prop _ _
         (ℤ-trichotomous (δ +pos succ i) δ)
         (inr (inr (i , ℤ-left-succ-pos δ i)))) ⁻¹

down-to-𝟛 : (a b : ℤ) → a below' b → 𝟛
down-to-𝟛 a b (inl      dL ) = −1
down-to-𝟛 a b (inr (inl dM)) =  O
down-to-𝟛 a b (inr (inr dR)) = +1

𝟛-to-down : (a : 𝟛) → (ℤ → ℤ)
𝟛-to-down −1 = downLeft
𝟛-to-down  O = downMid
𝟛-to-down +1 = downRight

𝟛-down-eq : (a b : ℤ) (d : a below' b)
          → 𝟛-to-down (down-to-𝟛 a b d) b ＝ a 
𝟛-down-eq a b (inl      dL ) = dL ⁻¹
𝟛-down-eq a b (inr (inl dM)) = dM ⁻¹
𝟛-down-eq a b (inr (inr dR)) = dR ⁻¹

down-𝟛-eq : (a : 𝟛) (b : ℤ)
          → (e : 𝟛-to-down a b below' b)
          → down-to-𝟛 (𝟛-to-down a b) b e ＝ a 
down-𝟛-eq −1 b (inl e) = refl
down-𝟛-eq  O b (inl e)
 = 𝟘-elim (downLeft≠downMid b b refl (e ⁻¹))
down-𝟛-eq +1 b (inl e)
 = 𝟘-elim (downLeft≠downRight b b refl (e ⁻¹))
down-𝟛-eq −1 b (inr (inl e))
 = 𝟘-elim (downLeft≠downMid b b refl e)
down-𝟛-eq  O b (inr (inl e)) = refl
down-𝟛-eq +1 b (inr (inl e))
 = 𝟘-elim (downMid≠downRight b b refl (e ⁻¹))
down-𝟛-eq −1 b (inr (inr e))
 = 𝟘-elim (downLeft≠downRight b b refl e)
down-𝟛-eq  O b (inr (inr e))
 = 𝟘-elim (downMid≠downRight b b refl e)
down-𝟛-eq +1 b (inr (inr e)) = refl

CI2-to-𝟛ᴺ  : ((k , i) : ℤ × ℤ) → CompactInterval2 (k , i) → 𝟛ᴺ
CI2-to-𝟛ᴺ (k , i) (χ , b₀ , bₛ) 0
 = down-to-𝟛 (χ 0) k (below-implies-below' (χ 0) k b₀)
CI2-to-𝟛ᴺ (k , i) (χ , b₀ , bₛ) (succ n)
 = down-to-𝟛 (χ (succ n)) (χ n)
    (below-implies-below' (χ (succ n)) (χ n) (bₛ n))

𝟛-to-down-is-below : (a : 𝟛) (k : ℤ) → 𝟛-to-down a k below k
𝟛-to-down-is-below −1 k = downLeft-below  k
𝟛-to-down-is-below  O k = downMid-below   k
𝟛-to-down-is-below +1 k = downRight-below k

𝟛ᴺ-to-CI2 : ((k , i) : ℤ × ℤ) → 𝟛ᴺ → CompactInterval2 (k , i)
𝟛ᴺ-to-CI2 (k , i) α = χ , b₀ , bₛ
 where
  χ  : ℕ → ℤ
  χ 0        = 𝟛-to-down (α 0) k
  χ (succ n) = 𝟛-to-down (α (succ n)) (χ n)
  b₀ : χ 0 below k
  b₀ = 𝟛-to-down-is-below (α 0) k
  bₛ : (n : ℕ) → χ (succ n) below χ n
  bₛ n = 𝟛-to-down-is-below (α (succ n)) (χ n)

integer-approx : 𝟛ᴺ → (ℕ → ℤ)
integer-approx α = pr₁ (𝟛ᴺ-to-CI2 (negsucc 0 , pos 0) α)

𝟛-possibilities : (a : 𝟛) → (a ＝ −1) + (a ＝ O) + (a ＝ +1)
𝟛-possibilities −1 = inl refl
𝟛-possibilities  O = inr (inl refl)
𝟛-possibilities +1 = inr (inr refl)

CI2-criteria : ((k , i) : ℤ × ℤ) → (ℕ → ℤ) → 𝓤₀ ̇
CI2-criteria (k , i) χ = (χ 0 below k)
                       × ((n : ℕ) → χ (succ n) below χ n)

CI2-prop
 : ((k , i) : ℤ × ℤ)
 → (χ : ℕ → ℤ)
 → is-prop (CI2-criteria (k , i) χ)
CI2-prop (k , i) χ
 = ×-is-prop (below-is-prop (χ 0) k)
     (Π-is-prop (fe _ _) (λ n → below-is-prop (χ (succ n)) (χ n)))

CompactInterval2-ternary
 : ((k , i) : ℤ × ℤ) → CompactInterval2 (k , i) ≃ 𝟛ᴺ
CompactInterval2-ternary (k , i)
 = qinveq (CI2-to-𝟛ᴺ (k , i)) (𝟛ᴺ-to-CI2 (k , i) , η , μ)
 where
  η : (𝟛ᴺ-to-CI2 (k , i)) ∘ (CI2-to-𝟛ᴺ (k , i)) ∼ id
  η (χ , b₀ , bₛ)
   = to-subtype-＝ (CI2-prop (k , i)) (dfunext (fe _ _) γ)
   where
    χ' = pr₁ (𝟛ᴺ-to-CI2 (k , i) (CI2-to-𝟛ᴺ (k , i) (χ , b₀ , bₛ))) 
    γ : χ' ∼ χ
    γ zero = 𝟛-down-eq (χ 0) k (below-implies-below' (χ 0) k b₀)
    γ (succ n)
     = ap (𝟛-to-down (down-to-𝟛 (χ (succ n)) (χ n)
            (below-implies-below' (χ (succ n)) (χ n) (bₛ n))))
          (γ n)
     ∙ 𝟛-down-eq (χ (succ n)) (χ n)
         (below-implies-below' (χ (succ n)) (χ n) (bₛ n))
  μ : (CI2-to-𝟛ᴺ (k , i)) ∘ (𝟛ᴺ-to-CI2 (k , i)) ∼ id
  μ α = dfunext (fe _ _) γ
   where
    α' = 𝟛ᴺ-to-CI2 (k , i) α
    γ : CI2-to-𝟛ᴺ (k , i) α' ∼ α
    γ 0 = down-𝟛-eq (α 0) k _
    γ (succ n) = down-𝟛-eq (α (succ n)) _ _

CI2-ClosenessSpace
 : ((k , i) : ℤ × ℤ)
 → is-closeness-space (CompactInterval2 (k , i))
CI2-ClosenessSpace (k , i)
 = Σ-clospace (CI2-criteria (k , i)) (CI2-prop (k , i))
     (discrete-seq-clospace (λ _ → ℤ-is-discrete))

_split-below_ : ℤ → ℤ → 𝓤₀ ̇
n split-below m = (n ＝ downLeft m) + (n ＝ downRight m)

split-below-is-prop : (n m : ℤ) → is-prop (n split-below m)
split-below-is-prop n m
 = +-is-prop ℤ-is-set ℤ-is-set
     (λ l r → downLeft≠downRight m m refl (l ⁻¹ ∙ r))

CI3-criteria : ((k , i) : ℤ × ℤ) → (ℕ → ℤ) → 𝓤₀ ̇
CI3-criteria (k , i) χ = (χ 0 split-below k)
                       × ((n : ℕ) → χ (succ n) split-below χ n)

CI3-prop : ((k , i) : ℤ × ℤ)
         → (χ : ℕ → ℤ)
         → is-prop (CI3-criteria (k , i) χ)
CI3-prop (k , i) χ
 = ×-is-prop (split-below-is-prop (χ 0) k)
     (Π-is-prop (fe _ _)
       (λ n → split-below-is-prop (χ (succ n)) (χ n)))

CompactInterval3 : ℤ × ℤ → 𝓤₀ ̇
CompactInterval3 (k , i) = Σ (CI3-criteria (k , i))

split-below-implies-below : (n m : ℤ) → n split-below m → n below m
split-below-implies-below n m (inl refl) = (0 , refl) , (2 , refl)
split-below-implies-below n m (inr refl) = (2 , refl) , (0 , refl)

CI3-to-CI2 : ((k , i) : ℤ × ℤ)
           → CompactInterval3 (k , i)
           → CompactInterval2 (k , i)
CI3-to-CI2 (k , i) (χ , b₀ , bₛ)
 = χ , split-below-implies-below (χ 0) k b₀
 , λ n → split-below-implies-below (χ (succ n)) (χ n) (bₛ n)

CI3-ClosenessSpace
 : ((k , i) : ℤ × ℤ) → is-closeness-space (CompactInterval3 (k , i))
CI3-ClosenessSpace (k , i) 
 = Σ-clospace (CI3-criteria (k , i)) (CI3-prop (k , i))
     (discrete-seq-clospace (λ _ → ℤ-is-discrete))

𝟚ᴺ = ℕ → 𝟚

down-to-𝟚 : (a b : ℤ) → a split-below b → 𝟚
down-to-𝟚 a b (inl dL) = ₀
down-to-𝟚 a b (inr dR) = ₁

𝟚-to-down : (a : 𝟚) → (ℤ → ℤ)
𝟚-to-down ₀ = downLeft
𝟚-to-down ₁ = downRight

𝟚-to-down-is-below : (a : 𝟚) (k : ℤ) → 𝟚-to-down a k split-below k
𝟚-to-down-is-below ₀ k = inl refl
𝟚-to-down-is-below ₁ k = inr refl

𝟚-down-eq : (a b : ℤ) (d : a split-below b)
          → 𝟚-to-down (down-to-𝟚 a b d) b ＝ a 
𝟚-down-eq a b (inl dL) = dL ⁻¹
𝟚-down-eq a b (inr dR) = dR ⁻¹

down-𝟚-eq : (a : 𝟚) (b : ℤ) (e : 𝟚-to-down a b split-below b)
          → down-to-𝟚 (𝟚-to-down a b) b e ＝ a 
down-𝟚-eq ₀ b (inl e) = refl
down-𝟚-eq ₁ b (inl e) = 𝟘-elim (downLeft≠downRight b b refl (e ⁻¹))
down-𝟚-eq ₀ b (inr e) = 𝟘-elim (downLeft≠downRight b b refl e)
down-𝟚-eq ₁ b (inr e) = refl

CI3-to-𝟚ᴺ
 : ((k , i) : ℤ × ℤ) → CompactInterval3 (k , i) → 𝟚ᴺ
CI3-to-𝟚ᴺ (k , i) (χ , b₀ , bₛ) 0
 = down-to-𝟚 (χ 0) k b₀
CI3-to-𝟚ᴺ (k , i) (χ , b₀ , bₛ) (succ n)
 = down-to-𝟚 (χ (succ n)) (χ n) (bₛ n)

𝟚ᴺ-to-CI3 : ((k , i) : ℤ × ℤ) → 𝟚ᴺ → CompactInterval3 (k , i)
𝟚ᴺ-to-CI3 (k , i) α = χ , b₀ , bₛ
 where
  χ  : ℕ → ℤ
  χ 0        = 𝟚-to-down (α 0) k
  χ (succ n) = 𝟚-to-down (α (succ n)) (χ n)
  b₀ : χ 0 split-below k
  b₀ = 𝟚-to-down-is-below (α 0) k
  bₛ : (n : ℕ) → χ (succ n) split-below χ n
  bₛ n = 𝟚-to-down-is-below (α (succ n)) (χ n)

CompactInterval3-cantor
 : ((k , i) : ℤ × ℤ) → CompactInterval3 (k , i) ≃ 𝟚ᴺ
CompactInterval3-cantor (k , i)
 = qinveq (CI3-to-𝟚ᴺ (k , i)) (𝟚ᴺ-to-CI3 (k , i) , η , μ)
 where
  η : (𝟚ᴺ-to-CI3 (k , i)) ∘ (CI3-to-𝟚ᴺ (k , i)) ∼ id
  η (χ , b₀ , bₛ)
   = to-subtype-＝ (CI3-prop (k , i)) (dfunext (fe _ _) γ)
   where
    χ' = pr₁ (𝟚ᴺ-to-CI3 (k , i) (CI3-to-𝟚ᴺ (k , i) (χ , b₀ , bₛ))) 
    γ : χ' ∼ χ
    γ 0 = 𝟚-down-eq (χ 0) k b₀
    γ (succ n)
     = ap (𝟚-to-down (down-to-𝟚 (χ (succ n)) (χ n) (bₛ n))) (γ n)
     ∙ 𝟚-down-eq (χ (succ n)) (χ n) (bₛ n)
  μ : (CI3-to-𝟚ᴺ (k , i)) ∘ (𝟚ᴺ-to-CI3 (k , i)) ∼ id
  μ α = dfunext (fe _ _) γ
   where
    α' = 𝟚ᴺ-to-CI3 (k , i) α
    γ : CI3-to-𝟚ᴺ (k , i) α' ∼ α
    γ 0 = down-𝟚-eq (α 0) k (𝟚-to-down-is-below (α 0) k)
    γ (succ n) = down-𝟚-eq (α (succ n)) _ _
```

[⇐ Index](../html/TWA.Thesis.index.html)
