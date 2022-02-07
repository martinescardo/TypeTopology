Andrew Sneap - 27th April 2021

In this file I define common divisors, and HCF's, along with a proof that the Euclidean Algorithm produces HCF's.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalsAddition --TypeTopology
open import NaturalNumbers-Properties --TypeTopology
open import NaturalsOrder --TypeTopoology
open import OrderNotation --TypeTopology
open import UF-Base --TypeTopology
open import UF-FunExt --TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-Subsingletons-FunExt --TypeTopology
 
open import NaturalsDivision
open import NaturalsMultiplication
open import NaturalsOrderExtended
open import MoreNaturalProperties

module HCF where

is-common-divisor : (d x y : ℕ) → 𝓤₀ ̇
is-common-divisor d x y = (d ∣ x) × (d ∣ y)

is-common-divisor-is-prop : (d x y : ℕ) → is-prop (is-common-divisor (succ d) x y)
is-common-divisor-is-prop d x y = ×-is-prop (d ∣ x -is-prop) (d ∣ y -is-prop)

is-hcf : (d x y : ℕ) → 𝓤₀ ̇
is-hcf d x y = (is-common-divisor d x y) × ((f : ℕ) →  is-common-divisor f x y → f ∣ d)

is-hcf-gives-is-common-divisor : (d x y : ℕ) → is-hcf d x y → is-common-divisor d x y
is-hcf-gives-is-common-divisor d x y (a , p) = a

is-hcf-is-prop : Fun-Ext → (d x y : ℕ) → is-prop (is-hcf (succ d) x y)
is-hcf-is-prop fe d x y p q = ×-is-prop (is-common-divisor-is-prop d x y) g p q
  where
    h : (f : ℕ) → is-common-divisor f x y → is-prop (f ∣ succ d)
    h 0        i x = 𝟘-elim (zero-does-not-divide-positive d x)
    h (succ f) i   = f ∣ (succ d) -is-prop
  
    g : is-prop ((f : ℕ) → is-common-divisor f x y → f ∣ succ d)
    g p' q' = Π₂-is-prop fe h p' q'

has-hcf : (x y : ℕ) → 𝓤₀ ̇
has-hcf x y = Σ d ꞉ ℕ , is-hcf (succ d) x y

has-hcf-is-prop : Fun-Ext → (x y : ℕ) → is-prop (has-hcf x y)
has-hcf-is-prop fe x y (a , p , p') (b , q , q') = to-subtype-≡ I II
 where
  I : (d : ℕ) → is-prop (is-hcf (succ d) x y)
  I d = is-hcf-is-prop fe d x y

  II : a ≡ b
  II = succ-lc (∣-anti (succ a) (succ b) α β)
   where
    α : succ a ∣ succ b
    α = q' (succ a) p

    β : succ b ∣ succ a
    β = p' (succ b) q

hcflemma : (a b c d : ℕ) → a * b ≡ a * c + d → a ∣ d
hcflemma a b c d e = subtraction-gives-factor (dichotomy-split (≥-dichotomy b c))
 where
  dichotomy-split : b ≥ c ∔ b ≤ c → (Σ f ꞉ ℕ , f + c ≡ b) ∔ (Σ f ꞉ ℕ , f + b ≡ c)
  dichotomy-split (inl x) = inl (subtraction c b x)
  dichotomy-split (inr x) = inr (subtraction b c x)

  subtraction-gives-factor : (Σ f ꞉ ℕ , f + c ≡ b) ∔ (Σ f ꞉ ℕ , f + b ≡ c) → a ∣ d
  subtraction-gives-factor (inl (f , p)) = f , addition-left-cancellable (a * f) d (a * c) I
   where
    I : a * c + a * f ≡ a * c + d
    I = a * c + a * f ≡⟨ distributivity-mult-over-nat a c f ⁻¹  ⟩
        a * (c + f)   ≡⟨ ap (a *_) (addition-commutativity c f) ⟩
        a * (f + c)   ≡⟨ ap (a *_) p                            ⟩
        a * b         ≡⟨ e                                      ⟩
        a * c + d ∎
  subtraction-gives-factor (inr (f , p)) = 0 , (sum-to-zero-gives-zero (a * f) d II ⁻¹)
   where
    I : a * f + d + a * b ≡ 0 + a * b
    I = a * f + d + a * b ≡⟨ trivial-addition-rearrangement (a * f) d (a * b)         ⟩
        a * f + a * b + d ≡⟨ ap (λ z → z + d) (distributivity-mult-over-nat a f b ⁻¹) ⟩
        a * (f + b) + d   ≡⟨ ap (λ z → a * z + d) p                                   ⟩
        a * c + d         ≡⟨ e ⁻¹                                                     ⟩
        a * b             ≡⟨ zero-left-neutral (a * b) ⁻¹                             ⟩
        0 + a * b         ∎

    II : a * f + d ≡ 0
    II = addition-right-cancellable (a * f + d) 0 (a * b) I

--using hints from cubical agda and strong induction cornell lecture
HCF : (a b : ℕ) → Σ h ꞉ ℕ , is-hcf h a b
HCF = course-of-values-induction (λ n → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h n b) step
 where
  step : (n : ℕ) → ((m : ℕ) → m < n → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h m b) → (b : ℕ) → Σ h ꞉ ℕ , is-hcf h n b
  step zero IH b = b , ((zero , refl) , 1 , refl) , (λ x → pr₂)
  step (succ n) IH b = I (division b n)
   where
    I : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (b ≡ q * succ n + r) × (r < succ n) → Σ h ꞉ ℕ , is-hcf h (succ n) b
    I (q , r , e₀ , l) = II (IH r l (succ n))
     where
      II : Σ h ꞉ ℕ , is-hcf h r (succ n) → Σ h ꞉ ℕ , is-hcf h (succ n) b
      II (h , ((x , xₚ) , y , yₚ) , γ) = h , ((y , yₚ) , i) , ii
       where
        i : h ∣ b
        i = (q * y + x) , e₁
         where
          e₁ : h * (q * y + x) ≡ b
          e₁ = h * (q * y + x)         ≡⟨ distributivity-mult-over-nat h (q * y) x      ⟩ 
               h * (q * y) + h * x     ≡⟨ ap (λ z → h * (q * y) + z) xₚ                 ⟩
               h * (q * y) + r         ≡⟨ ap (_+ r) (mult-associativity h q y) ⁻¹       ⟩
               h * q * y + r           ≡⟨ ap (λ z → z * y + r) (mult-commutativity h q) ⟩
               q * h * y + r           ≡⟨ ap (_+ r) (mult-associativity q h y)          ⟩
               q * (h * y) + r         ≡⟨ ap (λ z → q * z + r) yₚ                       ⟩
               q * succ n + r          ≡⟨ e₀ ⁻¹ ⟩
               b                       ∎

        ii : (f : ℕ) → is-common-divisor f (succ n) b → f ∣ h
        ii f ((α , αₚ) , β , βₚ) = γ f ((hcflemma f β (q * α) r e₂) , (α , αₚ))
         where
          e₂ : f * β ≡ f * (q * α) + r
          e₂ = f * β           ≡⟨ βₚ                                             ⟩
               b               ≡⟨ e₀                                             ⟩
               q * succ n + r  ≡⟨ ap (λ z → q * z + r) (αₚ ⁻¹)                  ⟩
               q * (f * α) + r ≡⟨ ap (_+ r) (mult-associativity q f α ⁻¹)       ⟩
               q * f * α + r   ≡⟨ ap (λ z → z * α + r) (mult-commutativity q f) ⟩
               f * q * α + r   ≡⟨ ap (_+ r ) (mult-associativity f q α)         ⟩
               f * (q * α) + r ∎

hcf : (a b : ℕ) → ℕ
hcf a b = pr₁ (HCF a b)

coprime : (a b : ℕ) → 𝓤₀ ̇
coprime a b = is-hcf 1 a b

coprime-is-prop : Fun-Ext → (a b : ℕ) → is-prop (coprime a b)
coprime-is-prop fe a b = is-hcf-is-prop fe zero a b

divbyhcf : (a b : ℕ) → Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h * x ≡ a) × (h * y ≡ b)) × coprime x y
divbyhcf zero     b = b , (zero , (1 , ((refl , refl) , ((zero , refl) , 1 , refl) , I)))
 where
  I : (f : ℕ) → is-common-divisor f 0 1 → f ∣ 1
  I f (_ , β) = β
divbyhcf (succ a) b = I (HCF (succ a) b)
 where
  I : Σ c ꞉ ℕ , is-hcf c (succ a) b → Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h * x ≡ (succ a)) × (h * y ≡ b)) × coprime x y 
  I (zero , ((x , xₚ) , y , yₚ) , γ) = have positive-not-zero a which-contradicts II
   where
    II : succ a ≡ 0
    II = succ a  ≡⟨ xₚ ⁻¹                     ⟩
         0 * x   ≡⟨ mult-commutativity zero x ⟩
         0       ∎
  I (succ h , ((x , xₚ) , y , yₚ) , γ) = (succ h) , (x , (y , ((xₚ , yₚ) , (((x , mult-commutativity 1 x) , y , (mult-commutativity 1 y)) , II))))
   where
    II : (f' : ℕ) → is-common-divisor f' x y → f' ∣ 1
    II f' ((α , αₚ) , β , βₚ) = III (γ (succ h * f') ((α , αₚ') , β , βₚ'))
     where
      αₚ' : succ h * f' * α ≡ succ a
      αₚ' = succ h * f' * α     ≡⟨ mult-associativity (succ h) f' α ⟩
            succ h * (f' * α)   ≡⟨ ap (succ h *_) αₚ                ⟩
            succ h * x          ≡⟨ xₚ                               ⟩
            succ a              ∎

      βₚ' : succ h * f' * β ≡ b
      βₚ' = succ h * f' * β   ≡⟨ mult-associativity (succ h) f' β ⟩
            succ h * (f' * β) ≡⟨ ap (succ h *_) βₚ                ⟩
            succ h * y        ≡⟨ yₚ                               ⟩
            b                 ∎

      III : (succ h) * f' ∣ (succ h) → f' ∣ 1
      III (δ , δₚ) = 1 , product-one-gives-one f' δ (mult-left-cancellable (f' * δ) 1 h e)
       where
        e : succ h * (f' * δ) ≡ succ h * 1
        e = succ h * (f' * δ) ≡⟨ mult-associativity (succ h) f' δ ⁻¹ ⟩
            succ h * f' * δ   ≡⟨ δₚ ⟩
            succ h            ∎

hcf-unique : (a b : ℕ) → ((h , p) : Σ h ꞉ ℕ , is-hcf h a b) → ((h' , p') : Σ h' ꞉ ℕ , is-hcf h' a b) → h ≡ h'
hcf-unique a b (h , h-icd , f) (h' , h'-icd , f') = ∣-anti h h' I II
 where
  I : h ∣ h'
  I = f' h h-icd

  II : h' ∣ h
  II = f h' h'-icd

\end{code}

Sketch code to formalise rationals stuff 

\begin{code}

HCF' : (a b : ℕ) → Σ h ꞉ ℕ , is-hcf (succ h) a (succ b)
HCF' a b = I (HCF a (succ b))
 where
  I : (Σ h ꞉ ℕ , is-hcf h a (succ b)) → Σ h ꞉ ℕ , is-hcf (succ h) a (succ b)
  I (zero , ((α , αₚ) , β , βₚ) , γ) = 𝟘-elim (zero-not-positive b (zero-left-is-zero β ⁻¹ ∙ βₚ))
  I (succ h , α) = h , α

hcf' : (a b : ℕ) → ℕ
hcf' a b = pr₁ (HCF' a b)

new-numerator : Fun-Ext → (x a : ℕ) → Σ x' ꞉ ℕ , x ≡ succ (hcf' x a) * x'
new-numerator fe x a = I (HCF' x a)
 where
  I : (Σ h ꞉ ℕ , is-hcf (succ h) x (succ a)) → Σ x' ꞉ ℕ , x ≡ succ (hcf' x a) * x'
  I (h , ((α , αₚ) , β , βₚ) , γ) = α ,(transport (λ - → succ - * α ≡ x) h-is-hcf αₚ ⁻¹)
   where
    h-is-hcf' : h , ((α , αₚ) , β , βₚ) , γ ≡ HCF' x a
    h-is-hcf' = has-hcf-is-prop fe x (succ a) (h , (((α , αₚ) , β , βₚ) , γ)) (HCF' x a)
    
    h-is-hcf : h ≡ pr₁ (HCF' x a)
    h-is-hcf = (pr₁ (from-Σ-≡ h-is-hcf'))
    
new-denominator : Fun-Ext → (x a : ℕ) → Σ a' ꞉ ℕ , succ a ≡ succ (hcf' x a) * succ a'
new-denominator fe x a = I (HCF' x a)
 where
  I : (Σ h ꞉ ℕ , is-hcf (succ h) x (succ a)) → Σ a' ꞉ ℕ , succ a ≡ succ (hcf' x a) * succ a'
  I (h , ((α , αₚ) , 0 , βₚ) , γ) = 𝟘-elim (positive-not-zero a (βₚ ⁻¹))
  I (h , ((α , αₚ) , succ β , βₚ) , γ) = β , transport (λ - → succ a ≡ succ - * succ β) h-is-hcf (βₚ ⁻¹)
   where
    h-is-hcf' : h , ((α , αₚ) , succ β , βₚ) , γ ≡ HCF' x a
    h-is-hcf' = has-hcf-is-prop fe x (succ a) (h , ((α , αₚ) , succ β , βₚ) , γ) (HCF' x a)

    h-is-hcf : h ≡ pr₁ (HCF' x a)
    h-is-hcf = pr₁ (from-Σ-≡ h-is-hcf')
{-
divbyhcf-gives-coprime : (x a : ℕ) → {!!}
divbyhcf-gives-coprime = {!!}
-}
\end{code}
