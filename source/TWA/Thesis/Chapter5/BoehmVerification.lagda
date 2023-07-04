\begin{code}
{-# OPTIONS --allow-unsolved-metas --exact-split --without-K --auto-inline
            --lossy-unification #-}

open import Integers.Addition renaming (_+_ to _ℤ+_;  _-_ to _ℤ-_)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Negation renaming (-_ to ℤ-_ )
open import Integers.Order
open import Integers.Type
open import MLTT.Spartan -- renaming (_+_ to _∔_)
open import Notation.Order
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order hiding (≤-refl)
open import Naturals.Order
  renaming (max to ℕmax) hiding (≤-refl ; ≤-trans ; ≤-split)
open import UF.Base
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropTrunc
open import UF.Quotient
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import TWA.Thesis.AndrewSneap.DyadicRationals
 renaming (normalise to ι)
open import TWA.Thesis.Chapter5.PLDIPrelude

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

downLeft downMid downRight : ℤ → ℤ
downLeft  k = (k ℤ+ k)
downMid   k = (k ℤ+ k) +pos 1
downRight k = (k ℤ+ k) +pos 2

upRight upLeft : ℤ → ℤ
upRight k = sign k (num k /2)
upLeft  k = upRight (predℤ k)

_below_ : ℤ → ℤ → 𝓤₀ ̇
a below b = downLeft b ≤ℤ a ≤ℤ downRight b

fully-ternary : (ℤ → ℤ) → 𝓤₀  ̇
fully-ternary x = (δ : ℤ) → x (succℤ δ) below x δ

𝕋 : 𝓤₀ ̇ 
𝕋 = Σ x ꞉ (ℤ → ℤ) , fully-ternary x

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

nested locatable : (ℤ → ℤ[1/2]ᴵ) → 𝓤₀ ̇
nested      ζ = (n : ℤ) → (ζ n) covers (ζ (succℤ n))
locatable     ζ = (ϵ : ℤ[1/2]) → is-positive ϵ
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

-- By Andrew Sneap
⦅_⦆ : (χ : ℤ → ℤ[1/2]ᴵ) → nested χ → locatable χ → ℝ-d
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
              , ∣ (pos 0) , (ℤ[1/2]<-neg (ld (χ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2]) ∣ ∣
  
  inhabited-r : inhabited-right R
  inhabited-r = ∣ (rd (χ (pos 0)) +𝔻 1ℤ[1/2])
              , ∣ pos 0  , ℤ[1/2]<-+ (rd (χ (pos 0))) 1ℤ[1/2] 0<1ℤ[1/2] ∣ ∣
  
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
        II : Σ n ꞉ ℤ , (p' <ℤ[1/2] ld (χ n)) → Σ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))
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
   = ∥∥-rec (<ℤ[1/2]-is-prop p q) I (binary-choice tp<x tx<q)
   where
    I : (Σ n ꞉ ℤ , (p <ℤ[1/2] ld (χ n))) × (Σ n' ꞉ ℤ , (rd (χ n') <ℤ[1/2] q))
      → p <ℤ[1/2] q
    I ((n , p<l) , (n' , r<q)) with ℤ-dichotomous n n'
    ... | inl n≤n'
           = let p<l' = ℤ[1/2]<-≤ p (ld (χ n)) (ld (χ n')) p<l
                          (pr₁ (nested-implies-fully-nested χ τ n n' n≤n'))
                 l<q' = ℤ[1/2]≤-< (ld (χ n')) (rd (χ n')) q (ld≤rd (χ n')) r<q 
           in trans p (ld (χ n')) q p<l' l<q'
    ... | inr n'≤n
           = let p<r' = ℤ[1/2]<-≤ p (ld (χ n)) (rd (χ n)) p<l (ld≤rd (χ n))
                 r<q' = ℤ[1/2]≤-< (rd (χ n)) (rd (χ n')) q
                          (pr₂ (nested-implies-fully-nested χ τ n' n n'≤n))
                             r<q
           in trans p (rd (χ n)) q p<r' r<q'
 
  is-located : located L R
  is-located p q p<q
   = I (π (1/2ℤ[1/2] * (q - p))
         (ℤ[1/2]<-positive-mult 1/2ℤ[1/2] (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)))
   where
    0<ε : 0ℤ[1/2] < (1/2ℤ[1/2] * (q - p))
    0<ε = <-pos-mult' 1/2ℤ[1/2] (q - p) 0<1/2ℤ[1/2] (diff-positive p q p<q)
    I : (Σ n ꞉ ℤ , ((rd (χ n) - ld (χ n)) ≤ℤ[1/2] (1/2ℤ[1/2] * (q - p))))
      → (L p holds) ∨ (R q holds)
    I (n , l₁) = II (ℤ[1/2]-ordering-property (rd (χ n)) (ld (χ n)) q p l₂)
     where
      l₂ :(rd (χ n) - ld (χ n)) < (q - p)
      l₂ = ℤ[1/2]≤-< (rd (χ n) - ld (χ n)) (1/2ℤ[1/2] * (q - p)) (q - p) l₁
             (ℤ[1/2]-1/2-< (q - p) (diff-positive p q p<q))
      II : (rd (χ n) < q) + (p < ld (χ n)) → (L p holds) ∨ (R q holds) 
      II (inl ζ<q) = ∣ inr ∣ n , ζ<q ∣ ∣
      II (inr p<ζ) = ∣ inl ∣ n , p<ζ ∣ ∣
  
ℤ³ : 𝓤₀ ̇
ℤ³ = Σ ((l , r) , p) ꞉ ((ℤ × ℤ) × ℤ) , l ≤ r

ℤ³-to-ℤ[1/2]ᴵ : ℤ³ → ℤ[1/2]ᴵ
ℤ³-to-ℤ[1/2]ᴵ (((l , r) , p) , i)
 = ((ι (l , p)) , ι (r , p)) , normalise-≤2 l r p i

⦅_⦆' : (χ : ℤ → ℤ³)
      → nested (ℤ³-to-ℤ[1/2]ᴵ ∘ χ) → locatable (ℤ³-to-ℤ[1/2]ᴵ ∘ χ)
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
      → locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
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

normalised-locatable : (χ : ℤ → ℤ²)
                   → normalised χ
                   → locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
normalised-locatable χ η ϵ ϵ⁺
 = q , transport (_≤ ϵ) (ℤ²-width (χ q) ⁻¹)
         (transport (λ - → ι (pos 2 , -) ≤ ϵ) (η q ⁻¹) γ)
 where
  q : ℤ
  q = pr₁ (ℤ[1/2]-find-lower ϵ ϵ⁺)
  γ : ι (pos 2 , q) ≤ ϵ
  γ = <-is-≤ℤ[1/2] _ _ (pr₂ (ℤ[1/2]-find-lower ϵ ϵ⁺))

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
               → fully-ternary (pr₁ ∘ χ)
               ⇔ nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
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
 = from-normalise-≤-same-denom _ _ _ γ
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
 = ℤ≤-pred _ _ (ℤ≤-pred _ _ (from-normalise-≤-same-denom _ _ _ γ))
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
nested-is-prop χ = Π-is-prop (fe _ _) (λ _ → covers-is-prop _ _)

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

fully-ternary-is-prop : (χ : ℤ → ℤ) → is-prop (fully-ternary χ)
fully-ternary-is-prop χ
 = Π-is-prop (fe _ _) λ _ → below-is-prop _ _

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
    γ : to-interval-seq (ternary-normalised→𝕋 (χ , _)) ∼ χ
    γ i = ap (pr₁ (χ i) ,_) (π i ⁻¹)
  μ : (ternary-normalised→𝕋 ∘ 𝕋→nested-normalised) ∼ id
  μ (χ , b) = to-subtype-＝ fully-ternary-is-prop (dfunext (fe _ _) γ)
   where
    γ : (λ x → pr₁ (pr₁ (𝕋→nested-normalised (χ , b)) x)) ∼ χ
    γ i = refl

𝕋→nested-locatable
 : 𝕋
 → Σ χ ꞉ (ℤ → ℤ²) , (nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                  × locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
𝕋→nested-locatable χ
 = χ' , τ , normalised-locatable χ' π
 where
  γ = 𝕋→nested-normalised χ
  χ' = pr₁ γ 
  τ  = pr₁ (pr₂ γ)
  π  = pr₂ (pr₂ γ)

⟦_⟧ : 𝕋 → ℝ-d
⟦ χ ⟧ = ⦅ χ' ⦆'' τ π
 where
  γ = 𝕋→nested-locatable χ
  χ' = pr₁ γ 
  τ  = pr₁ (pr₂ γ)
  π  = pr₂ (pr₂ γ)

\end{code}
l
prenormalised : (ℤ → ℤ²) → 𝓤₀ ̇
prenormalised χ = (n : ℤ) → pr₂ (χ n) ≥ n

normalised-prenormalised : (χ : ℤ → ℤ²)
                         → normalised χ
                         → prenormalised χ 
normalised-prenormalised χ η n = 0 , (η n ⁻¹)

prenormalised-locatable : (χ : ℤ → ℤ²)
                      → prenormalised χ
                      → locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
prenormalised-locatable χ p ϵ ϵ⁺
 = q
 , transport (_≤ ϵ) (ℤ²-width (χ q) ⁻¹)
     (trans' (ι (pos 2 , pr₂ (χ q))) (ι (pos 2 , q)) ϵ
       (normalise-denom-≤ 2 q (pr₂ (χ q)) (p q)) γ) 
 where
  q : ℤ
  q = pr₁ (ℤ[1/2]-find-lower ϵ ϵ⁺)
  γ : ι (pos 2 , q) ≤ ϵ
  γ = <-≤ℤ[1/2] _ _ (pr₂ (ℤ[1/2]-find-lower ϵ ϵ⁺))

Prenormalising

prenormalise : (χ : ℤ → ℤ²) → locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
             → ℤ → ℤ²
prenormalise χ π n = χ (pr₁ (π (ι (pos 1 , {!pos!})) {!!}))

prenormalise-prenormalised
 : (χ : ℤ → ℤ²) (π : locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
 → prenormalised (prenormalise χ π)
prenormalise-prenormalised = {!!}

prenormalise-nested : (χ : ℤ → ℤ²) (π : locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
                    → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                    → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ prenormalise χ π)
prenormalise-nested = {!!}

prenormalise-same-real
 : (χ : ℤ → ℤ²)
 → (τ : nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) (π : locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
 → Id (⦅ χ ⦆'' τ π)
      (⦅ prenormalise χ π ⦆''
          (prenormalise-nested χ π τ)
          (prenormalised-locatable (prenormalise χ π)
            (prenormalise-prenormalised χ π)))
prenormalise-same-real = {!!}

-- Normalising

normalise' : (χ : ℤ → ℤ²) → prenormalised χ → (ℤ → ℤ²)
normalise' = {!!} -- in other file

normalise'-normalised : (χ : ℤ → ℤ²) (p : prenormalised χ)
                      → normalised (normalise' χ p)
normalise'-normalised = {!!} -- in other file

normalise'-nested : (χ : ℤ → ℤ²) (p : prenormalised χ)
                  → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                  → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ normalise' χ p)
normalise'-nested = {!!} -- in other file

normalise'-same-real
 : (χ : ℤ → ℤ²)
 → (τ : nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
 → (p : prenormalised χ)
 → Id (⦅ χ ⦆'' τ (prenormalised-locatable χ p))
      (⦅ normalise' χ p ⦆''
          (normalise'-nested χ p τ)
          (normalised-locatable (normalise' χ p)
            (normalise'-normalised χ p)))
normalise'-same-real = {!!}


-- Prenormalising composed with normalising


normalise : (χ : ℤ → ℤ²) → locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ) → (ℤ → ℤ²)
normalise χ π
 = normalise' (prenormalise χ π)
     (prenormalise-prenormalised χ π)

normalise-normalised : (χ : ℤ → ℤ²) (π : locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
                     → normalised (normalise χ π)
normalise-normalised χ π
 = normalise'-normalised (prenormalise χ π)
     (prenormalise-prenormalised χ π)

normalise-nested : (χ : ℤ → ℤ²) (π : locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
                 → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                 → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ normalise χ π)
normalise-nested χ π τ
 = normalise'-nested (prenormalise χ π)
     (prenormalise-prenormalised χ π)
     (prenormalise-nested χ π τ)

normalise-same-real
 : (χ : ℤ → ℤ²)
 → (τ : nested  (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
 → (π : locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ χ))
 → Id (⦅ χ ⦆'' τ π)
      (⦅ normalise χ π ⦆''
          (normalise-nested χ π τ)
          (normalised-locatable (normalise χ π)
            (normalise-normalised χ π)))
normalise-same-real χ τ π
 = {!!}


-- From normalised sequences to ternary boehm encodings

-- Exact real arithmetic

join' : ℤ³ → ℤ²
join' = {!!}

join : (ℤ → ℤ³) → (ℤ → ℤ²)
join χ n = join' (χ n)

join'-covers : (a : ℤ³) → (ℤ²-to-ℤ[1/2]ᴵ ∘ join') a covers (ℤ³-to-ℤ[1/2]ᴵ a)
join'-covers = {!!}

join'-needed : (a b : ℤ³)
             → ℤ³-to-ℤ[1/2]ᴵ a covers ℤ³-to-ℤ[1/2]ᴵ b
             → (ℤ²-to-ℤ[1/2]ᴵ ∘ join') a covers (ℤ²-to-ℤ[1/2]ᴵ ∘ join') b
join'-needed = {!!}

join-nested : (χ : ℤ → ℤ³) → nested (ℤ³-to-ℤ[1/2]ᴵ ∘ χ) → nested (ℤ²-to-ℤ[1/2]ᴵ ∘ join χ)
join-nested χ τ n = join'-needed (χ n) (χ (succℤ n)) (τ n) 

join-locatable : (χ : ℤ → ℤ³) → locatable (ℤ³-to-ℤ[1/2]ᴵ ∘ χ) → locatable (ℤ²-to-ℤ[1/2]ᴵ ∘ join χ)
join-locatable χ π = {!!}

join-same-real : (χ : ℤ → ℤ³)
               → (τ : nested  (ℤ³-to-ℤ[1/2]ᴵ ∘ χ))
               → (π : locatable (ℤ³-to-ℤ[1/2]ᴵ ∘ χ))
               → Id (⦅ χ ⦆' τ π)
                    (⦅ (join χ) ⦆'' (join-nested _ τ) (join-locatable _ π))
join-same-real = {!!}
\end{code} 
module _
  {d : ℕ}
  (f : Vec ℝ-d d → ℝ-d)
  (A : Vec ℤ³  d → ℤ³ )
  (A-function : (as : Vec ℤ³ d) (ws : Vec ℝ-d d) -- DIFFERS FROM PAPER
              → pairwise₂
                  (λ (a , b) w → (ℤ[1/2]-to-ℝ-d a) ℝ-d≤ w
                               × w ℝ-d≤ (ℤ[1/2]-to-ℝ-d b))
                  (vec-map η as) ws
              → ((ℤ[1/2]-to-ℝ-d ((pr₁ ∘ pr₁ ∘ η) (A as))) ℝ-d≤ f ws)
              × (f ws ℝ-d≤ (ℤ[1/2]-to-ℝ-d ((pr₂ ∘ pr₁ ∘ η) (A as)))))
  (A-nested   : (as bs : Vec ℤ³ d)
              → pairwise₂ _covers_ (vec-map (pr₁ ∘ η) as) (vec-map (pr₁ ∘ η) bs)
              → (pr₁ ∘ η) (A as) covers (pr₁ ∘ η) (A bs))
  (A-locatable  : (as : Vec ℤ³ d)
              → (ϵ : ℤ[1/2]) → positive ϵ → Σ δs ꞉ Vec ℤ[1/2] d
              , ((bs : Vec ℤ³ d)
                → pairwise₂ _covers_ (vec-map (pr₁ ∘ η) as) (vec-map (pr₁ ∘ η) bs)
                → pairwise₂ _≤_ (vec-map ((λ (x , y) → y - x) ∘ pr₁ ∘ η) as) δs
                → let ((Ak , Ac) , _) = η (A as) in (Ac - Ak) ≤ ϵ))
  -- DIFFERS FROM PAPER
  where

 f' : Vec (ℤ → ℤ³) d → (ℤ → ℤ³)
 f' χs n = A (vec-map (λ χ → χ n) χs)

 f'-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                        , nested  (pr₁ ∘ η ∘ χ)
                        × locatable (pr₁ ∘ η ∘ χ)) d)
           → nested (pr₁ ∘ η ∘ f' (vec-map pr₁ χs))
 f'-nested χs n = A-nested
                    (vec-map (λ χ → χ n) (vec-map pr₁ χs))
                    (vec-map (λ χ → χ (succℤ n)) (vec-map pr₁ χs))
                    (γ χs)
  where
   γ : {m : ℕ} → (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                      , nested  (pr₁ ∘ η ∘ χ)
                      × locatable (pr₁ ∘ η ∘ χ)) m)
     → pairwise₂ _covers_
       (vec-map (pr₁ ∘ η) (vec-map (λ χ → χ n) (vec-map pr₁ χs)))
       (vec-map (pr₁ ∘ η) (vec-map (λ χ → χ (succℤ n)) (vec-map pr₁ χs)))
   γ [] = ⋆
   γ ((x , τ , _) ∷ χs) = τ n , γ χs

 vec-fold : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ}
          → B → (A → B → B) → Vec A n → B
 vec-fold b f [] = b
 vec-fold b f (x ∷ as) = vec-fold (f x b) f as

 f'-locatable : (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                        , nested  (pr₁ ∘ η ∘ χ)
                        × locatable (pr₁ ∘ η ∘ χ)) d)
            → locatable (pr₁ ∘ η ∘ f' (vec-map pr₁ χs))
 f'-locatable χs ϵ i = {!!}

 f'-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ³)
                    , nested  (pr₁ ∘ η ∘ χ)
                    × locatable (pr₁ ∘ η ∘ χ)) d)
              → Id (f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆' τ π) χs))
                   (⦅ f' (vec-map pr₁ χs) ⦆' (f'-nested χs) (f'-locatable χs))
 f'-same-real χs = {!!} {- same-cuts-gives-equality _ _
                     (λ p p≤f → pr₁ (A-function {!!} {!!} {!!}))
                     {!!} {!!} {!!} -}

 f''-aux : Vec (ℤ → ℤ²) d → (ℤ → ℤ³)
 f''-aux χs = f' (vec-map (to-dcode ∘_) χs)

 f''-aux-transport
  : {n : ℕ} → (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                         × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) n)
  → Id (vec-map
         (pr₁ {𝓤₀} {𝓤₀} {(x : ℤ) → ℤ³}
              {λ χ → nested (pr₁ ∘ η ∘ χ) × locatable (pr₁ ∘ η ∘ χ)})
         (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs))
       (vec-map (to-dcode ∘_) (vec-map pr₁ χs))
 f''-aux-transport [] = refl
 f''-aux-transport ((x , _) ∷ χs) = ap ((to-dcode ∘ x) ∷_)
                                      (f''-aux-transport χs)

 f''-aux-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                        , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                        × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
                → nested (pr₁ ∘ η ∘ f''-aux (vec-map pr₁ χs))
 f''-aux-nested χs
  = transport nested
      (dfunext (fe _ _ )
      (λ n → ap (λ - → (pr₁ ∘ η ∘ f' -) n)
        (f''-aux-transport χs)))
      (f'-nested (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs))

 f''-aux-locatable : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                        , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                        × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
            → locatable (pr₁ ∘ η ∘ f''-aux (vec-map pr₁ χs))
 f''-aux-locatable χs
  = transport locatable
      (dfunext (fe _ _ )
      (λ n → ap (λ - → (pr₁ ∘ η ∘ f' -) n)
        (f''-aux-transport χs)))
      (f'-locatable (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs))

 f''-aux-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                    , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                    × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
              → Id (f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs))
                   (⦅ f''-aux (vec-map pr₁ χs) ⦆'
                       (f''-aux-nested χs) (f''-aux-locatable χs))
 f''-aux-same-real χs
  = ap f (vec-map-∼
      (λ (χ , τ , π) → to-dcode ∘ χ , τ , π)
      (λ (χ , τ , π) → ⦅ χ ⦆' τ π) χs)
  ∙ f'-same-real
      (vec-map (λ (χ , τ , π) → to-dcode ∘ χ , τ , π) χs)
  ∙ {!!}

 f'' : Vec (ℤ → ℤ²) d → (ℤ → ℤ²)
 f'' = join ∘ f''-aux

 f''-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                         × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
            → nested (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ f'' (vec-map pr₁ χs))
 f''-nested χs = join-nested (f''-aux (vec-map pr₁ χs))
                   (f''-aux-nested χs)

 f''-locatable : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                        , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                        × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
            → locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ f'' (vec-map pr₁ χs))
 f''-locatable χs = join-locatable (f''-aux (vec-map pr₁ χs))
                    (f''-aux-locatable χs)

 f''-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
               , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
               × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
               → Id (f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs))
                     (⦅ f'' (vec-map pr₁ χs) ⦆''
                       (f''-nested χs) (f''-locatable χs))
 f''-same-real χs = {!!} {- join-same-real (f''-aux (vec-map pr₁ χs))
                      (join-nested (f''-aux (vec-map pr₁ χs))
                        (f''-aux-nested χs))
                      (join-locatable (f''-aux (vec-map pr₁ χs))
                        (f''-aux-locatable χs)) -}

 f*-aux : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
              , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
              × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
        → (ℤ → ℤ²)
 f*-aux χs = normalise (f'' (vec-map pr₁ χs)) (f''-locatable χs)

 f*-aux-nested : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                         × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
               → nested (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ f*-aux χs)
 f*-aux-nested χs = normalise-nested (f'' (vec-map pr₁ χs))
                      (f''-locatable χs)
                      (f''-nested χs)

 f*-aux-normalised : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                         , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                         × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
                   → normalised (f*-aux χs)
 f*-aux-normalised χs = normalise-normalised _ (f''-locatable χs)

 f*-aux-locatable : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                      , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                      × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
                → locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ f*-aux χs)
 f*-aux-locatable χs = normalised-locatable (f*-aux χs)
                       (f*-aux-normalised χs)

 f*-aux-same-real : (χs : Vec (Σ χ ꞉ (ℤ → ℤ²)
                      , nested  (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)
                      × locatable (pr₁ ∘ ℤ²-to-ℤ[1/2]ᴵ ∘ χ)) d)
                  → f (vec-map (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs)
                  ＝ ⦅ f*-aux χs ⦆'' (f*-aux-nested χs) (f*-aux-locatable χs)
 f*-aux-same-real χs
  = f''-same-real χs
  ∙ normalise-same-real (f'' (vec-map pr₁ χs))
      (f''-nested χs)
      (f''-locatable χs)

 f* : Vec 𝕋 d → 𝕋
 f* χs = ternary-normalised→𝕋
           ( f*-aux            ζs
           , f*-aux-nested     ζs
           , f*-aux-normalised ζs)
  where
   ζs  = vec-map 𝕋→nested-locatable χs

 f*-same-real : (χs : Vec 𝕋 d)
              → f (vec-map ⟦_⟧ χs) ＝ ⟦ f* χs ⟧
 f*-same-real χs
  = ap f (vec-map-∼ 𝕋→nested-locatable (λ (χ , τ , π) → ⦅ χ ⦆'' τ π) χs)
  ∙ f*-aux-same-real (vec-map 𝕋→nested-locatable χs)
  ∙ {!!}

\end{code}
