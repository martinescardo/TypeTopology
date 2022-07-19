Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalsAddition renaming (_+_ to _ℕ+_) --TypeTopology
open import NaturalNumbers-Properties --TypeTopology
open import NaturalsOrder --TypeTopology
open import OrderNotation --TypeTopology
open import UF-Base --TypeTopology
open import UF-Subsingletons --TypeTopology

open import IntegersAddition
open import IntegersB
open import IntegersAbs
open import IntegersNegation
open import IntegersOrder
open import IntegersMultiplication renaming (_*_ to _ℤ*_) 
open import NaturalsDivision renaming (_∣_ to _ℕ∣_)
open import NaturalsMultiplication renaming (_*_ to _ℕ*_) 

ppnnp-lemma : (a b : ℕ) → Σ c ꞉ ℕ , negsucc a + negsucc b ≡ negsucc c
ppnnp-lemma a = induction base step
 where
  base : Σ c ꞉ ℕ , negsucc a + negsucc 0 ≡ negsucc c
  base = succ a , refl

  step : (k : ℕ) → Σ c ꞉ ℕ , negsucc a + negsucc k ≡ negsucc c
                 → Σ c ꞉ ℕ , negsucc a + negsucc (succ k) ≡ negsucc c
  step k (c , IH) = succ c , ap predℤ IH

product-positive-negative-not-positive : (a b c : ℕ) → ¬ (pos a ℤ* negsucc b ≡ pos (succ c))
product-positive-negative-not-positive 0 0 c e        = 𝟘-elim (positive-not-zero c (pos-lc e ⁻¹))
product-positive-negative-not-positive 0 (succ b) c e = 𝟘-elim (positive-not-zero c (pos-lc I ⁻¹))
 where
  I : pos 0 ≡ pos (succ c)
  I = pos 0                     ≡⟨ ℤ-zero-left-is-zero (negsucc (succ b)) ⁻¹ ⟩
      pos 0 ℤ* negsucc (succ b) ≡⟨ e                                         ⟩
      pos (succ c)              ∎
product-positive-negative-not-positive (succ a) (succ b) c e₁ = I (pos-mult-is-succ a b)
  where
   I : ¬ (Σ z ꞉ ℕ , succ z ≡ succ a ℕ* succ b)
   I (z , e₂) = II (ppnnp-lemma a z)
    where
     II : ¬ (Σ d ꞉ ℕ , negsucc a + negsucc z ≡ negsucc d)
     II (d , e₃) = neg-not-positive IV
      where
       III : negsucc z ≡ pos (succ a) ℤ* negsucc b
       III = negsucc z                      ≡⟨ refl                                                        ⟩
             - pos (succ z)                 ≡⟨ ap (λ α → -_ (pos α)) e₂                                    ⟩
             - pos (succ a ℕ* succ b)       ≡⟨ ap -_ (pos-multiplication-equiv-to-ℕ (succ a) (succ b)) ⁻¹  ⟩
             - pos (succ a) ℤ* pos (succ b) ≡⟨ subtraction-dist-over-mult (pos (succ a)) (pos (succ b)) ⁻¹ ⟩
             pos (succ a) ℤ* negsucc b      ∎
       IV : negsucc d ≡ pos (succ c)
       IV = negsucc d                                 ≡⟨ e₃ ⁻¹                 ⟩
            negsucc a + negsucc z                     ≡⟨ ap (negsucc a +_) III ⟩
            negsucc a + pos (succ a) ℤ* negsucc b     ≡⟨ refl                  ⟩
            pos (succ a) ℤ* negsucc (succ b)          ≡⟨ e₁                    ⟩
            pos (succ c)                              ∎

_∣_ : ℤ → ℤ → 𝓤₀ ̇
a ∣ b = Σ x ꞉ ℤ , a ℤ* x ≡ b

_ℤ∣_-is-prop : (a b : ℤ) → not-zero a → is-prop (a ∣ b)
_ℤ∣_-is-prop a b nz (x , p) (x' , p') = to-subtype-≡ (λ _ → ℤ-is-set) II
 where
  I : x ℤ* a ≡ x' ℤ* a
  I = x ℤ* a   ≡⟨ ℤ*-comm x a  ⟩
      a ℤ* x   ≡⟨ p            ⟩
      b        ≡⟨ p' ⁻¹        ⟩
      a ℤ* x'  ≡⟨ ℤ*-comm a x' ⟩
      x' ℤ* a  ∎
 
  II : x ≡ x'
  II = ℤ-mult-right-cancellable x x' a nz I

div-equiv-to-pos-div : (a b : ℕ) → a ℕ∣ b → pos a ∣ pos b
div-equiv-to-pos-div a b (x , p) = pos x , goal
 where
  goal : pos a ℤ* pos x ≡ pos b
  goal = pos a ℤ* pos x ≡⟨ pos-multiplication-equiv-to-ℕ a x ⟩
         pos (a ℕ* x)   ≡⟨ ap pos p                          ⟩
         pos b          ∎

sign-split : (x : ℤ) → positive x ∔ negative x
sign-split (pos x)     = inl ⋆
sign-split (negsucc x) = inr ⋆

pos-div-to-nat-div : (a b : ℕ) → pos a ∣ pos b → a ℕ∣ b
pos-div-to-nat-div a b (pos x , p) = x , pos-lc I
 where
  I : pos (a ℕ* x) ≡ pos b
  I = pos (a ℕ* x)   ≡⟨ pos-multiplication-equiv-to-ℕ a x ⁻¹ ⟩
      pos a ℤ* pos x ≡⟨ p                                    ⟩
      pos b          ∎
pos-div-to-nat-div a 0 (negsucc x , p) = 0 , refl
pos-div-to-nat-div 0 (succ b) (negsucc x , p) = 𝟘-elim (positive-not-zero b (pos-lc I))
 where
  I : pos (succ b) ≡ pos 0
  I = pos (succ b)        ≡⟨ p ⁻¹                            ⟩
      pos 0 ℤ* negsucc x  ≡⟨ ℤ-zero-left-is-zero (negsucc x) ⟩
      pos 0 ∎
pos-div-to-nat-div (succ a) (succ b) (negsucc x , p) = 𝟘-elim (product-positive-negative-not-positive (succ a) x b p)

ℤ-division : (a : ℤ) → (d : ℕ) → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (a ≡ q ℤ* pos (succ d) + pos r) × r < succ d
ℤ-division (pos a) d = f (division a d)
 where
  f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q ℕ* succ d ℕ+ r) × r < succ d
    → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (pos a ≡ q ℤ* pos (succ d) + pos r) × r < succ d
  f (q , r , e , l) = (pos q) , r , I , l
   where
    I : pos a ≡ pos q ℤ* pos (succ d) + pos r
    I = pos a                         ≡⟨ ap pos e                                                    ⟩
        pos (q ℕ* succ d ℕ+ r)        ≡⟨ pos-addition-equiv-to-ℕ (q ℕ* (succ d)) r ⁻¹                ⟩
        pos (q ℕ* succ d) + pos r     ≡⟨ ap (_+ pos r) (pos-multiplication-equiv-to-ℕ q (succ d) ⁻¹) ⟩
        pos q ℤ* pos (succ d) + pos r ∎
ℤ-division (negsucc a) d = f (division (succ a) d)
 where
  f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q ℕ* succ d ℕ+ r) × r < succ d
    → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (negsucc a ≡ q ℤ* pos (succ d) + pos r) × r < succ d
  f (0 , 0 , e , l) = 𝟘-elim (positive-not-zero a I)
   where
    I : succ a ≡ 0
    I = succ a           ≡⟨ e                          ⟩
        0 ℕ* succ d ℕ+ 0 ≡⟨ zero-left-base (succ d) ⟩
        0                ∎
  f (succ q , 0 , e , l) = negsucc q , 0 , I , l
   where
    I : negsucc a ≡ negsucc q ℤ* pos (succ d)
    I = negsucc a                        ≡⟨ refl                                                         ⟩
        - pos (succ a)                   ≡⟨ ap -_ (ap pos e)                                             ⟩
        - pos (succ q ℕ* succ d)         ≡⟨ ap -_ (pos-multiplication-equiv-to-ℕ (succ q) (succ d) ⁻¹)   ⟩
        - pos (succ q) ℤ* pos (succ d)   ≡⟨ subtraction-dist-over-mult' (pos (succ q)) (pos (succ d)) ⁻¹ ⟩
        (- pos (succ q)) ℤ* pos (succ d) ≡⟨ refl                                                         ⟩
        negsucc q ℤ* pos (succ d)        ∎
  f (0 , succ r , e₁ , l₁) = negsucc 0 , I (subtraction' (succ r) (succ d) l₁)
   where
    I : Σ k ꞉ ℕ , k ℕ+ succ r ≡ succ d
      → Σ r ꞉ ℕ , (negsucc a ≡ negsucc 0 ℤ* pos (succ d) + pos r) × r < succ d
    I (k , e₂) = k , III (cosubtraction k d (r , succ-lc II))
     where
      II : succ (r ℕ+ k) ≡ succ d
      II = succ (r ℕ+ k) ≡⟨ ap succ (addition-commutativity r k) ⟩
           succ (k ℕ+ r) ≡⟨ e₂                                   ⟩
           succ d        ∎
      III : k < succ d → (negsucc a ≡ negsucc 0 ℤ* pos (succ d) + pos k) × k < succ d
      III l₂ = V , l₂
       where
        IV : succ a ≡ succ r
        IV = succ a                ≡⟨ e₁                                                ⟩
             0 ℕ* succ d ℕ+ succ r ≡⟨ ap succ (ap (_ℕ+ r) (zero-left-base (succ d))) ⟩
             succ (0 ℕ+ r)         ≡⟨ ap succ (zero-left-neutral r)                     ⟩
             succ r                ∎
     
        V : negsucc a ≡ negsucc 0 ℤ* pos (succ d) + pos k
        V = negsucc a                                              ≡⟨ ap negsucc (succ-lc IV)                                                            ⟩
            negsucc r                                              ≡⟨ ℤ-zero-left-neutral (negsucc r) ⁻¹                                                 ⟩
            pos 0 + negsucc r                                      ≡⟨ ap (_+ (negsucc r)) (ℤ-sum-of-inverse-is-zero (pos k) ⁻¹)                          ⟩
            pos k + (- pos k) + negsucc r                          ≡⟨ ℤ+-assoc (pos k) (- pos k) (negsucc r)                                             ⟩
            pos k + ((- pos k) + negsucc r)                        ≡⟨ ℤ+-comm (pos k) ((- pos k) + negsucc r)                                            ⟩
            (- pos k) + negsucc r + pos k                          ≡⟨ ap (λ z → (z + negsucc r) + pos k) (mult-inverse (pos k))                          ⟩
            negsucc 0 ℤ* pos k + (- pos (succ r)) + pos k          ≡⟨ ap (λ z →  (negsucc 0 ℤ* pos k + z) + pos k) (mult-inverse (pos (succ r)))         ⟩
            negsucc 0 ℤ* pos k + negsucc 0 ℤ* pos (succ r) + pos k ≡⟨ ap (_+ pos k) (distributivity-mult-over-ℤ' (pos k) (pos (succ r)) (negsucc 0) ⁻¹)  ⟩
            negsucc 0 ℤ* (pos k + pos (succ r)) + pos k            ≡⟨ ap (λ z → negsucc 0 ℤ* z + pos k) (pos-addition-equiv-to-ℕ k (succ r))             ⟩
            negsucc 0 ℤ* pos (k ℕ+ succ r) + pos k                 ≡⟨ ap (λ z → negsucc 0 ℤ* pos z + pos k) e₂                                           ⟩
            negsucc 0 ℤ* pos (succ d) + pos k                      ∎
 
  f (succ q , succ r , e₁ , l₁) = negsucc (succ q) , I (subtraction' (succ r) (succ d) l₁)
   where
    I : Σ k ꞉ ℕ , k ℕ+ succ r ≡ succ d
      → Σ r ꞉ ℕ , (negsucc a ≡ negsucc (succ q) ℤ* pos (succ d) + pos r) × r < succ d
    I (k , e₂) =  k , III (cosubtraction k d (r , succ-lc II))
     where
      II : succ (r ℕ+ k) ≡ succ d
      II = succ (r ℕ+ k) ≡⟨ ap succ (addition-commutativity r k) ⟩
           succ (k ℕ+ r) ≡⟨ e₂                                   ⟩
           succ d        ∎
      III : k < succ d → (negsucc a ≡ negsucc (succ q) ℤ* pos (succ d) + pos k) × k < (succ d)
      III l₂ = V , l₂
       where
        IV : - pos (succ r) ≡ pos k - pos (succ d)
        IV = - pos (succ r)                     ≡⟨ refl                                                      ⟩
             negsucc r                          ≡⟨ ℤ-zero-left-neutral (negsucc r) ⁻¹                        ⟩
             pos 0 + negsucc r                  ≡⟨ ap (_+  negsucc r) (ℤ-sum-of-inverse-is-zero (pos k) ⁻¹)  ⟩
             pos k + (- pos k) + negsucc r      ≡⟨ ℤ+-assoc (pos k) (- pos k) (negsucc r)                    ⟩
             pos k + ((- pos k) - pos (succ r)) ≡⟨ ap (pos k +_) (negation-dist (pos k) (pos (succ r)))      ⟩
             pos k - (pos k + pos (succ r))     ≡⟨ ap (λ z → pos k - z) (pos-addition-equiv-to-ℕ k (succ r)) ⟩
             pos k - pos (k ℕ+ succ r)          ≡⟨ ap (λ z → pos k - pos z) e₂ ⟩
             pos k - pos (succ d)               ∎
        V : negsucc a ≡ negsucc (succ q) ℤ* pos (succ d) + pos k
        V = negsucc a                                                          ≡⟨ refl               ⟩
            - pos (succ a)                                                     ≡⟨ ap -_ (ap pos e₁)  ⟩
            - pos (succ q ℕ* succ d ℕ+ succ r)                                 ≡⟨ i                  ⟩
            - (pos (succ q ℕ* succ d) + pos (succ r))                          ≡⟨ ii                 ⟩
            (- pos (succ q ℕ* succ d)) - pos (succ r)                          ≡⟨ iii                ⟩
            (- pos (succ q) ℤ* pos (succ d)) - pos (succ r)                    ≡⟨ iv                 ⟩
            (- pos (succ q) ℤ* pos (succ d)) + (pos k - pos (succ d))          ≡⟨ v                  ⟩
            (- pos (succ q) ℤ* pos (succ d)) - pos (succ d) + pos k            ≡⟨ vi                 ⟩
            (- pos (succ d) ℤ* pos (succ q)) - pos (succ d) + pos k            ≡⟨ vii                ⟩             
            (- pos (succ d)) ℤ* pos (succ q) - pos (succ d) + pos k            ≡⟨ viii               ⟩
            (- pos (succ d)) ℤ* pos (succ q) - pos (succ d) ℤ* pos 1 + pos k   ≡⟨ ix                 ⟩
            (- pos (succ d)) ℤ* (pos (succ q) + pos 1) + pos k                 ≡⟨ refl               ⟩
            (- pos (succ d)) ℤ* pos (succ (succ q)) + pos k                    ≡⟨ x                  ⟩
            (- pos (succ d) ℤ* pos (succ (succ q))) + pos k                    ≡⟨ xi                 ⟩
            (- pos (succ (succ q)) ℤ* pos (succ d)) + pos k                    ≡⟨ xii                ⟩
            negsucc (succ q) ℤ* pos (succ d) + pos k                           ∎
             where
              i    = ap -_ (pos-addition-equiv-to-ℕ (succ q ℕ* (succ d)) (succ r) ⁻¹)
              ii   = negation-dist (pos (succ q ℕ* succ d)) (pos (succ r)) ⁻¹
              iii  = ap (λ z → (- z) - pos (succ r)) (pos-multiplication-equiv-to-ℕ (succ q) (succ d) ⁻¹)
              iv   = ap ((- pos (succ q) ℤ* pos (succ d)) +_) IV
              v    = ℤ+-rearrangement (- (pos (succ q) ℤ* pos (succ d))) (pos k) (- pos (succ d)) ⁻¹
              vi   = ap (λ z → ((- z) + (- pos (succ d))) + pos k) (ℤ*-comm (pos (succ q)) (pos (succ d)))
              vii  = ap (λ z → (z + (- pos (succ d))) + pos k) (subtraction-dist-over-mult' (pos (succ d)) (pos (succ q)) ⁻¹)
              viii = ap (λ z → ((- pos (succ d)) ℤ* pos (succ q) + z) + pos k) (ℤ-mult-right-id (- pos (succ d))) ⁻¹
              ix   = ap (_+ pos k) (distributivity-mult-over-ℤ' (pos (succ q)) (pos 1) (- pos (succ d)) ⁻¹)
              x    = ap (_+ pos k) (subtraction-dist-over-mult' (pos (succ d)) (pos (succ (succ q))))
              xi   = ap (λ z → (- z) + pos k) (ℤ*-comm (pos (succ d)) (pos (succ (succ q))))
              xii  = ap (_+ pos k) (subtraction-dist-over-mult' (pos (succ (succ q))) (pos (succ d)) ⁻¹)

ℤ-∣-respects-addition : (x y z : ℤ) → x ∣ y → x ∣ z → x ∣ y + z
ℤ-∣-respects-addition x y z (α , αₚ) (β , βₚ) = α + β , I
 where
  I : x ℤ* (α + β) ≡ y + z
  I = x ℤ* (α + β)    ≡⟨ distributivity-mult-over-ℤ' α β x ⟩
      x ℤ* α + x ℤ* β ≡⟨ ap₂ _+_ αₚ βₚ                      ⟩  
      y + z           ∎

ℤ-∣-respects-addition-of-multiples : (x y z k l : ℤ) → x ∣ y → x ∣ z → x ∣ (y ℤ* k + z ℤ* l)
ℤ-∣-respects-addition-of-multiples x y z k l (α , αₚ) (β , βₚ) = α ℤ* k + β ℤ* l , I
 where
  I : x ℤ* (α ℤ* k + β ℤ* l) ≡ y ℤ* k + z ℤ* l
  I = x ℤ* (α ℤ* k + β ℤ* l)        ≡⟨ distributivity-mult-over-ℤ' (α ℤ* k) (β ℤ* l) x ⟩
      x ℤ* (α ℤ* k) + x ℤ* (β ℤ* l) ≡⟨ ap₂ _+_ (ℤ*-assoc x α k ⁻¹) (ℤ*-assoc x β l ⁻¹) ⟩
      x ℤ* α ℤ* k + x ℤ* β ℤ* l     ≡⟨ ap₂ _+_ (ap (_ℤ* k) αₚ) (ap (_ℤ* l) βₚ)          ⟩
      y ℤ* k + z ℤ* l               ∎

\end{code}
