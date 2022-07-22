Andrew Sneap

In this file I define rational numbers.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) 

open import Notation.CanonicalMap 
open import TypeTopology.DiscreteAndSeparated 
open import TypeTopology.SigmaDiscreteAndTotallySeparated 
open import Naturals.Properties 
open import UF.Base hiding (_≈_)
open import UF.FunExt 
open import UF.Miscelanea 
open import UF.Subsingletons 

open import Naturals.HCF
open import DedekindReals.IntegersAbs
open import DedekindReals.IntegersB
open import DedekindReals.IntegersMultiplication renaming (_*_ to _ℤ*_)
open import DedekindReals.IntegersNegation
open import DedekindReals.IntegersOrder
open import DedekindReals.NaturalsDivision
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import DedekindReals.ncRationals

module DedekindReals.Rationals where

ℚ : 𝓤₀ ̇
ℚ = Σ q ꞉ ℚₙ , is-in-lowest-terms q

ℚ-is-discrete : Fun-Ext → is-discrete ℚ
ℚ-is-discrete fe = Σ-is-discrete ℚₙ-is-discrete (λ q x y → inl (is-in-lowest-terms-is-prop fe q x y))

ℚ-is-set : Fun-Ext → is-set ℚ
ℚ-is-set fe = discrete-types-are-sets (ℚ-is-discrete fe)

toℚₙ : ℚ → ℚₙ
toℚₙ (q , _) = q

\end{code}

I would like to rewrite this function to move h out of a sigma type (h = hcf' x (succ a))

\begin{code}
{-
toℚ' : ℚₙ → ℚ
toℚ' (x , a) = {!!}
-}
toℚlemma : ((x , a) : ℚₙ) → Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ＝ (pos (succ h)) ℤ* x') × (succ a ＝ (succ h) ℕ* succ a'))
toℚlemma (pos a , b) = f (divbyhcf a (succ b))
 where
  f : Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ＝ a) × (h ℕ* y ＝ succ b)) × coprime x y → _
  f (h      , x , zero   , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
  f (0      , x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹ ∙ zero-left-base (succ y)))
  f (succ h , x , succ y , (γ₁ , γ₂) , r) = (((pos x) , y) , r) , h , I , (γ₂ ⁻¹)
   where
    I : pos a ＝ pos (succ h) ℤ* pos x
    I = pos a                 ＝⟨ ap pos γ₁ ⁻¹                                 ⟩                               
        pos (succ h ℕ* x)     ＝⟨ pos-multiplication-equiv-to-ℕ (succ h) x ⁻¹ ⟩
        pos (succ h) ℤ* pos x ∎
toℚlemma (negsucc a , b) = f (divbyhcf (succ a) (succ b))
 where
  f : ((Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h ℕ* x ＝ (succ a)) × (h ℕ* y ＝ succ b)) × coprime x y)) → _
  f (h      , x      , 0      , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹))
  f (h      , 0      , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero a (γ₁ ⁻¹))
  f (0      , succ x , succ y , (γ₁ , γ₂) , r) = 𝟘-elim (positive-not-zero b (γ₂ ⁻¹ ∙ zero-left-base (succ y)))
  f (succ h , succ x , succ y , (γ₁ , γ₂) , r) = (((negsucc x) , y) , r) , (h , (I , (γ₂ ⁻¹)))
   where
    i : pos (succ a) ＝ (pos (succ h) ℤ* pos (succ x))
    i = pos (succ a)                 ＝⟨ ap pos γ₁ ⁻¹                                       ⟩
        pos (succ h ℕ* succ x)       ＝⟨ pos-multiplication-equiv-to-ℕ (succ h) (succ x) ⁻¹ ⟩
        pos (succ h) ℤ* pos (succ x) ∎

    I : negsucc a ＝ pos (succ h) ℤ* negsucc x
    I = negsucc a                          ＝⟨ ap -_ i                                                     ⟩
        - (pos (succ h) ℤ* pos (succ x))   ＝⟨ subtraction-dist-over-mult (pos (succ h)) (pos (succ x)) ⁻¹ ⟩
        pos (succ h) ℤ* (- pos (succ x))   ∎

toℚ : ℚₙ → ℚ
toℚ q = pr₁ (toℚlemma q)

0ℚ : ℚ
0ℚ = toℚ (pos 0 , 0)

1ℚ : ℚ
1ℚ = toℚ (pos 1 , 0)

-1ℚ : ℚ
-1ℚ = toℚ (negsucc 0 , 0)

1/3 2/3 : ℚ
1/3 = toℚ (pos 1 , 2)
2/3 = toℚ (pos 2 , 2)

1/2 : ℚ
1/2 = toℚ (pos 1 , 1)

1/5 : ℚ
1/5 = toℚ (pos 1 , 4)

2/5 : ℚ
2/5 = toℚ (pos 2 , 4)

3/5 : ℚ
3/5 = toℚ (pos 3 , 4)

1/4 : ℚ
1/4 = toℚ (pos 1 , 3)

3/4 : ℚ
3/4 = toℚ (pos 3 , 3)

\end{code}
I would like to rewrite the following proof as it is difficult to
follow, and having ⇔ introduces many projections later in the code.
\begin{code}

equiv-equality : Fun-Ext → (p q : ℚₙ) → p ≈ q ⇔ toℚ p ＝ toℚ q
equiv-equality fe (x , a) (y , b) = I , II
 where
  α : Σ ((x' , a') , p)  ꞉ ℚ , Σ h ꞉ ℕ  , (x ＝ pos (succ h) ℤ* x')  × (succ a ＝ succ h ℕ* succ a')
  α = toℚlemma (x , a)

  β : Σ ((y' , b') , p') ꞉ ℚ , Σ h' ꞉ ℕ , (y ＝ pos (succ h') ℤ* y') × (succ b ＝ succ h' ℕ* succ b')
  β = toℚlemma (y , b)

  h h' : ℕ
  h = pr₁ (pr₂ α)
  h' = pr₁ (pr₂ β)

  a' b' : ℕ
  a' = pr₂ (pr₁ (pr₁ α))
  b' = pr₂ (pr₁ (pr₁ β))

  x' y' : ℤ
  x' = pr₁ (pr₁ (pr₁ α))
  y' = pr₁ (pr₁ (pr₁ β))

  p : is-in-lowest-terms (x' , a')
  p = pr₂ (pr₁ α)

  p' : is-in-lowest-terms (y' , b')
  p' = pr₂ (pr₁ β)

  αₚ₁ : x ＝ pos (succ h) ℤ* x'
  αₚ₁ = pr₁ (pr₂ (pr₂ α))

  αₚ₂ : succ a ＝ succ h ℕ* succ a'
  αₚ₂ = pr₂ (pr₂ (pr₂ α))

  αₚ₂' : pos (succ a) ＝ pos (succ h) ℤ* pos (succ a')
  αₚ₂' = pos (succ a)                  ＝⟨ ap pos αₚ₂                                          ⟩
         pos (succ h ℕ* succ a')       ＝⟨ pos-multiplication-equiv-to-ℕ (succ h) (succ a') ⁻¹ ⟩
         pos (succ h) ℤ* pos (succ a') ∎

  βₚ₁ : y ＝ pos (succ h') ℤ* y'
  βₚ₁ = pr₁ (pr₂ (pr₂ β))

  βₚ₂ : succ b ＝ succ h' ℕ* succ b'
  βₚ₂ = pr₂ (pr₂ (pr₂ β))

  βₚ₂' : pos (succ b) ＝ pos (succ h') ℤ* pos (succ b')
  βₚ₂' = pos (succ b)                   ＝⟨ ap pos βₚ₂                                           ⟩
         pos (succ h' ℕ* succ b')       ＝⟨ pos-multiplication-equiv-to-ℕ (succ h') (succ b') ⁻¹ ⟩
         pos (succ h') ℤ* pos (succ b') ∎

  I : (x , a) ≈ (y , b) → (x' , a') , p ＝ (y' , b') , p'
  I e = to-subtype-＝ (λ z → is-in-lowest-terms-is-prop fe z) (equiv-with-lowest-terms-is-equal (x' , a') (y' , b') f p p')
   where
    f : x' ℤ* pos (succ b') ＝ y' ℤ* pos (succ a')
    f = ℤ-mult-left-cancellable (x' ℤ* pos (succ b')) (y' ℤ* pos (succ a')) (pos (succ h)) id g
     where
      g : pos (succ h) ℤ* (x' ℤ* pos (succ b')) ＝ pos (succ h) ℤ* (y' ℤ* pos (succ a'))
      g = ℤ-mult-left-cancellable (pos (succ h) ℤ* (x' ℤ* pos (succ b'))) (pos (succ h) ℤ* (y' ℤ* pos (succ a'))) (pos (succ h')) id k
       where
        k : pos (succ h') ℤ* (pos (succ h) ℤ* (x' ℤ* pos (succ b'))) ＝ pos (succ h') ℤ* (pos (succ h) ℤ* (y' ℤ* pos (succ a')))
        k = pos (succ h') ℤ* (pos (succ h) ℤ* (x' ℤ* pos (succ b')))     ＝⟨ ap (pos (succ h') ℤ*_) (ℤ*-assoc (pos (succ h)) x' (pos (succ b')) ⁻¹)             ⟩
            pos (succ h') ℤ* (pos (succ h) ℤ* x' ℤ* pos (succ b'))       ＝⟨ ap (λ z → pos (succ h') ℤ* (z ℤ* pos (succ b'))) (αₚ₁ ⁻¹)                          ⟩
            pos (succ h') ℤ* (x ℤ* pos (succ b'))                        ＝⟨ ℤ-mult-rearrangement''' (pos (succ h')) x (pos (succ b'))                          ⟩
            x ℤ* (pos (succ h') ℤ* pos (succ b'))                        ＝⟨ ap (x ℤ*_) (βₚ₂' ⁻¹)                                                               ⟩
            x ℤ* pos (succ b)                                            ＝⟨ e                                                                                  ⟩
            y ℤ* pos (succ a)                                            ＝⟨ ap₂ _ℤ*_ βₚ₁ αₚ₂'                                                                   ⟩
            pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))       ＝⟨ ℤ*-assoc (pos (succ h')) y' (pos (succ h) ℤ* pos (succ a'))                        ⟩
            pos (succ h') ℤ* (y' ℤ* (pos (succ h) ℤ* pos (succ a')))     ＝⟨ ap (pos (succ h') ℤ*_) (ℤ-mult-rearrangement''' y' (pos (succ h)) (pos (succ a'))) ⟩
            pos (succ h') ℤ* (pos (succ h) ℤ* (y' ℤ* pos (succ a')))     ∎

  II : toℚ (x , a) ＝ toℚ (y , b) → (x , a) ≈ (y , b)
  II e = x ℤ* pos (succ b)                                              ＝⟨ ap₂ _ℤ*_ αₚ₁ (ap pos βₚ₂)                                                            ⟩
         pos (succ h) ℤ* x' ℤ* pos (succ h' ℕ* succ b')                 ＝⟨ ap₂ (λ z z' → (pos (succ h) ℤ* z ℤ* pos (succ h' ℕ* succ z'))) iv (v ⁻¹)            ⟩
         pos (succ h) ℤ* y' ℤ* pos (succ h' ℕ* succ a')                 ＝⟨ ap (pos (succ h) ℤ* y' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h') (succ a')) ⁻¹  ⟩
         pos (succ h) ℤ* y' ℤ* (pos (succ h') ℤ* pos (succ a'))         ＝⟨ ℤ-mult-rearrangement'' (pos (succ h')) (pos (succ h)) y' (pos (succ a'))            ⟩
         pos (succ h') ℤ* y' ℤ* (pos (succ h) ℤ* pos (succ a'))         ＝⟨ ap (pos (succ h') ℤ* y' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a'))     ⟩ 
         pos (succ h') ℤ* y' ℤ* pos (succ h ℕ* succ a')                 ＝⟨ ap₂ _ℤ*_ (βₚ₁ ⁻¹) (ap pos (αₚ₂ ⁻¹))                                                  ⟩
         y ℤ* pos (succ a)                                              ∎
    where
     i : Σ δ ꞉ (x' , a') ＝ (y' , b') , _
     i = from-Σ-＝ e

     ii : x' , a' ＝ y' , b'
     ii = pr₁ i

     iii : (x' ＝ y') × (a' ＝ b')
     iii = from-×-＝' ii

     iv = pr₁ iii
     v = pr₂ iii

equiv→equality : Fun-Ext → (p q : ℚₙ) → p ≈ q → toℚ p ＝ toℚ q
equiv→equality fe p q = I
 where
  I : p ≈ q → toℚ p ＝ toℚ q
  I = pr₁ (equiv-equality fe p q)

equality→equiv : Fun-Ext → (p q : ℚₙ) → toℚ p ＝ toℚ q → p ≈ q
equality→equiv fe p q = I
 where
  I : toℚ p ＝ toℚ q → p ≈ q
  I = pr₂ (equiv-equality fe p q)

≈-toℚ : (p : ℚₙ) → p ≈ toℚₙ (toℚ p)
≈-toℚ (x , a) = conclusion
 where
  right-l : Σ ((x' , a') , p) ꞉ ℚ , (Σ h ꞉ ℕ , (x ＝ pos (succ h) ℤ* x') × (succ a ＝ (succ h) ℕ* succ a'))
  right-l = toℚlemma (x , a)

  right : ℚ
  right = toℚ (x , a)

  x' : ℤ
  x' = pr₁ (pr₁ right)
  a' : ℕ
  a' = pr₂ (pr₁ right)

  h : ℕ
  h = pr₁ (pr₂ right-l)

  a'' = pos (succ a')
  h' = pos (succ h)

  e₁ : x ＝ pos (succ h) ℤ* x'
  e₁ = pr₁ (pr₂ (pr₂ right-l))

  e₂ : succ a ＝ (succ h) ℕ* succ a'
  e₂ = pr₂ (pr₂ (pr₂ right-l))
    
  conclusion : x ℤ* a'' ＝ x' ℤ* pos (succ a)
  conclusion = x ℤ* a''                           ＝⟨ ap (_ℤ* a'') e₁                                                ⟩
               h' ℤ* x' ℤ* a''                    ＝⟨ ap (_ℤ* a'') (ℤ*-comm h' x')                                   ⟩
               x' ℤ* h' ℤ* a''                    ＝⟨ ℤ*-assoc x' h' a''                                             ⟩
               x' ℤ* (h' ℤ* a'')                  ＝⟨ ap (x' ℤ*_) (pos-multiplication-equiv-to-ℕ (succ h) (succ a')) ⟩
               x' ℤ* pos ((succ h) ℕ* succ a')    ＝⟨ ap (x' ℤ*_) (ap pos e₂ ⁻¹)                                     ⟩
               x' ℤ* pos (succ a)                 ∎

q-has-qn : Fun-Ext → (q : ℚ) → Σ q' ꞉ ℚₙ , q ＝ toℚ q'
q-has-qn fe (q , p) = q , (to-subtype-＝ (is-in-lowest-terms-is-prop fe) (equiv-with-lowest-terms-is-equal q q' (≈-toℚ q) p (pr₂ right)))
 where
  right : ℚ
  right = toℚ q

  q' : ℚₙ
  q' = pr₁ right

ℚ-zero-not-one : Fun-Ext → ¬ (0ℚ ＝ 1ℚ)
ℚ-zero-not-one fe e = positive-not-zero 0 (pos-lc V ⁻¹)
 where
  I : (pos 0 , 0) ≈ (pos 1 , 0) ⇔ toℚ (pos 0 , 0) ＝ toℚ (pos 1 , 0) 
  I = equiv-equality fe ((pos 0) , 0) ((pos 1) , 0)

  II : toℚ (pos 0 , 0) ＝ toℚ (pos 1 , 0) → (pos 0 , 0) ≈ (pos 1 , 0)
  II = pr₂ I

  III : (pos 0 , 0) ≈ (pos 1 , 0)
  III = II e

  IV : pos 0 ℤ* pos 1 ＝ pos 1 ℤ* pos 1
  IV = III

  V : pos 0 ＝ pos 1
  V = pos 0          ＝⟨ refl ⟩
      pos 0 ℤ* pos 1 ＝⟨ IV   ⟩
      pos 1 ℤ* pos 1 ＝⟨ refl ⟩
      pos 1          ∎

numerator-zero-is-zero : Fun-Ext → (((x , a) , p) : ℚ) → x ＝ pos zero → (x , a) , p ＝ 0ℚ
numerator-zero-is-zero fe ((negsucc x , a) , p) e = 𝟘-elim (negsucc-not-pos e)
numerator-zero-is-zero fe ((pos zero  , a) , (_ , icd) , f) e = to-subtype-＝ (is-in-lowest-terms-is-prop fe) I
 where
  I : pos zero , a ＝ pos zero , 0
  I = ap₂ _,_ refl (succ-lc II)
   where    
    II : succ a ＝ 1
    II = ∣-anti (succ a) 1 (f (succ a) ((0 , refl) , 1 , refl)) icd
numerator-zero-is-zero fe ((pos (succ x) , a) , p) e = 𝟘-elim (positive-not-zero x (pos-lc e))

toℚ-toℚₙ : Fun-Ext → ((r , p) : ℚ) → r , p ＝ toℚ r
toℚ-toℚₙ fe (r , p) = II
 where
  rp' = toℚ r
  r' = pr₁ (toℚ r)
  r'lt = pr₂ (toℚ r)
  I = equiv-with-lowest-terms-is-equal r r' (≈-toℚ r) p r'lt
  II : r , p ＝ toℚ r
  II = to-subtype-＝ (is-in-lowest-terms-is-prop fe) I

instance
 canonical-map-ℚₙ-to-ℚ : Canonical-Map ℚₙ ℚ
 ι {{canonical-map-ℚₙ-to-ℚ}} = toℚ

ℤ-to-ℚ : ℤ → ℚ
ℤ-to-ℚ z = ι (ι z)

instance
 canonical-map-ℤ-to-ℚ : Canonical-Map ℤ ℚ
 ι {{canonical-map-ℤ-to-ℚ}} = ℤ-to-ℚ

ℕ-to-ℚ : ℕ → ℚ
ℕ-to-ℚ n = ι {{ canonical-map-ℤ-to-ℚ }} (ι n)

instance
 canonical-map-ℕ-to-ℚ : Canonical-Map ℕ ℚ 
 ι {{canonical-map-ℕ-to-ℚ}} = ℕ-to-ℚ


