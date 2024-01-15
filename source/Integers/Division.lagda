Andrew Sneap, 27 April 2021

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Properties
open import Naturals.Order
open import Notation.Order
open import UF.Base
open import UF.Subsingletons

open import Integers.Addition
open import Integers.Type
open import Integers.Abs
open import Integers.Negation
open import Integers.Order
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Naturals.Division renaming (_∣_ to _ℕ∣_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)

module Integers.Division where

_∣_ : ℤ → ℤ → 𝓤₀ ̇
a ∣ b = Σ x ꞉ ℤ , a ℤ* x ＝ b

_ℤ∣_-is-prop : (a b : ℤ) → not-zero a → is-prop (a ∣ b)
_ℤ∣_-is-prop a b nz (x , p) (x' , p') = to-subtype-＝ (λ _ → ℤ-is-set) II
 where
  I : x ℤ* a ＝ x' ℤ* a
  I = x ℤ* a   ＝⟨ ℤ*-comm x a  ⟩
      a ℤ* x   ＝⟨ p            ⟩
      b        ＝⟨ p' ⁻¹        ⟩
      a ℤ* x'  ＝⟨ ℤ*-comm a x' ⟩
      x' ℤ* a  ∎

  II : x ＝ x'
  II = ℤ-mult-right-cancellable x x' a nz I

div-equiv-to-pos-div : (a b : ℕ) → a ℕ∣ b → pos a ∣ pos b
div-equiv-to-pos-div a b (x , p) = pos x , goal
 where
  goal : pos a ℤ* pos x ＝ pos b
  goal = pos a ℤ* pos x ＝⟨ pos-multiplication-equiv-to-ℕ a x ⟩
         pos (a ℕ* x)   ＝⟨ ap pos p                          ⟩
         pos b          ∎

sign-split : (x : ℤ) → positive x ∔ negative x
sign-split (pos x)     = inl ⋆
sign-split (negsucc x) = inr ⋆

pos-div-to-nat-div : (a b : ℕ) → pos a ∣ pos b → a ℕ∣ b
pos-div-to-nat-div a b (pos x , p) = x , pos-lc I
 where
  I : pos (a ℕ* x) ＝ pos b
  I = pos (a ℕ* x)   ＝⟨ pos-multiplication-equiv-to-ℕ a x ⁻¹ ⟩
      pos a ℤ* pos x ＝⟨ p                                    ⟩
      pos b          ∎
pos-div-to-nat-div a 0 (negsucc x , p) = 0 , refl
pos-div-to-nat-div 0 (succ b) (negsucc x , p) = 𝟘-elim γ
 where
  I : pos (succ b) ＝ pos 0
  I = pos (succ b)        ＝⟨ p ⁻¹                         ⟩
      pos 0 ℤ* negsucc x  ＝⟨ ℤ-zero-left-base (negsucc x) ⟩
      pos 0               ∎

  γ : 𝟘
  γ = positive-not-zero b (pos-lc I)
pos-div-to-nat-div (succ a) (succ b) (negsucc x , p) = 𝟘-elim γ
 where
  γ : 𝟘
  γ = product-positive-negative-not-positive (succ a) x b p

\end{code}

TODO : Break apart ℤ-division into 4 subproofs

\begin{code}

ℤ-division : (a : ℤ) → (d : ℕ)
           → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (a ＝ q ℤ* pos (succ d) + pos r) × r < succ d
ℤ-division (pos a) d = f (division a d)
 where
  f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ＝ q ℕ* succ d ℕ+ r) × r < succ d
    → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (pos a ＝ q ℤ* pos (succ d) + pos r) × r < succ d
  f (q , r , e , l) = (pos q) , r , I , l
   where
    I : pos a ＝ pos q ℤ* pos (succ d) + pos r
    I = pos a                         ＝⟨ ap pos e ⟩
        pos (q ℕ* succ d ℕ+ r)        ＝⟨ i        ⟩
        pos (q ℕ* succ d) + pos r     ＝⟨ ii       ⟩
        pos q ℤ* pos (succ d) + pos r ∎
     where
      i = distributivity-pos-addition (q ℕ* (succ d)) r ⁻¹
      ii = ap (_+ pos r) (pos-multiplication-equiv-to-ℕ q (succ d) ⁻¹)
ℤ-division (negsucc a) d = f (division (succ a) d)
 where
  a' = negsucc a
  d' = succ d

  f : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ＝ q ℕ* d' ℕ+ r) × r < d'
    → Σ q ꞉ ℤ , Σ r ꞉ ℕ , (a' ＝ q ℤ* pos d' + pos r) × r < d'
  f (0 , 0 , e , l) = 𝟘-elim (positive-not-zero a I)
   where
    I : succ a ＝ 0
    I = succ a       ＝⟨ e                 ⟩
        0 ℕ* d' ℕ+ 0 ＝⟨ zero-left-base d' ⟩
        0            ∎
  f (succ q , 0 , e , l) = negsucc q , 0 , I , l
   where
    I : a' ＝ negsucc q ℤ* pos d'
    I = a'                         ＝⟨ refl ⟩
        - pos (succ a)             ＝⟨ i    ⟩
        - pos (succ q ℕ* d')       ＝⟨ ii   ⟩
        - pos (succ q) ℤ* pos d'   ＝⟨ iii  ⟩
        (- pos (succ q)) ℤ* pos d' ＝⟨ refl ⟩
        negsucc q ℤ* pos d'        ∎
     where
      i   = ap -_ (ap pos e)
      ii  = ap -_ (pos-multiplication-equiv-to-ℕ (succ q) d' ⁻¹)
      iii = negation-dist-over-mult' (pos (succ q)) (pos d') ⁻¹
  f (0 , succ r , e₁ , l₁) = negsucc 0 , I (subtraction' (succ r) (succ d) l₁)
   where
    n1 : ℤ
    n1 = negsucc 0

    I : Σ k ꞉ ℕ , k ℕ+ succ r ＝ succ d
      → Σ r ꞉ ℕ , (a' ＝ n1 ℤ* pos (succ d) + pos r) × r < succ d
    I (k , e₂) = k , III (cosubtraction k d (r , succ-lc II))
     where
      k' = pos k
      II : succ (r ℕ+ k) ＝ succ d
      II = succ (r ℕ+ k) ＝⟨ ap succ (addition-commutativity r k) ⟩
           succ (k ℕ+ r) ＝⟨ e₂                                   ⟩
           succ d        ∎
      III : k < succ d
          → (a' ＝ n1 ℤ* pos (succ d) + k')
          × k < succ d
      III l₂ = V , l₂
       where
        IV : succ a ＝ succ r
        IV = succ a                ＝⟨ e₁ ⟩
             0 ℕ* succ d ℕ+ succ r ＝⟨ i  ⟩
             succ (0 ℕ+ r)         ＝⟨ ii ⟩
             succ r                ∎
         where
         i  = ap succ (ap (_ℕ+ r) (zero-left-base (succ d)))
         ii = ap succ (zero-left-neutral r)

        V : a' ＝ n1 ℤ* pos (succ d) + k'
        V = a'                                 ＝⟨ i    ⟩
            negsucc r                          ＝⟨ ii   ⟩
            pos 0 + negsucc r                  ＝⟨ iii  ⟩
            k' + (- k') + negsucc r            ＝⟨ iv   ⟩
            k' + ((- k') + negsucc r)          ＝⟨ v    ⟩
            (- k') + negsucc r + k'            ＝⟨ vi   ⟩
            n1 ℤ* k' + (- pos (succ r)) + k'   ＝⟨ vii  ⟩
            n1 ℤ* k' + n1 ℤ* pos (succ r) + k' ＝⟨ viii ⟩
            n1 ℤ* (k' + pos (succ r)) + k'     ＝⟨ ix   ⟩
            n1 ℤ* pos (k ℕ+ succ r) + k'       ＝⟨ x    ⟩
            n1 ℤ* pos (succ d) + k'            ∎
         where
          i    = ap negsucc (succ-lc IV)
          ii   = ℤ-zero-left-neutral (negsucc r) ⁻¹
          iii  = ap (_+ (negsucc r)) (ℤ-sum-of-inverse-is-zero k' ⁻¹)
          iv   = ℤ+-assoc k' (- k') (negsucc r)
          v    = ℤ+-comm k' ((- k') + negsucc r)
          vi   = ap (λ z → (z + negsucc r) + k') (mult-negation k')
          vii  = ap (λ z →  (n1 ℤ* k' + z) + k') (mult-negation (pos (succ r)))
          viii = ap (_+ k') (distributivity-mult-over-ℤ' k' (pos (succ r)) n1 ⁻¹)
          ix   = ap (λ z → n1 ℤ* z + k') (distributivity-pos-addition k (succ r))
          x    = ap (λ z → n1 ℤ* pos z + k') e₂

  f (succ q , succ r , e₁ , l₁) = negsucc (succ q) , γ
   where
    I : Σ k ꞉ ℕ , k ℕ+ succ r ＝ d'
      → Σ r ꞉ ℕ , (a' ＝ negsucc (succ q) ℤ* pos d' + pos r) × r < d'
    I (k , e₂) =  k , III (cosubtraction k d (r , succ-lc II))
     where
      k' = pos k
      q' = pos (succ q)

      II : succ (r ℕ+ k) ＝ d'
      II = succ (r ℕ+ k) ＝⟨ ap succ (addition-commutativity r k) ⟩
           succ (k ℕ+ r) ＝⟨ e₂                                   ⟩
           d'        ∎
      III : k < d' → (a' ＝ negsucc (succ q) ℤ* pos d' + k') × k < d'
      III l₂ = V , l₂
       where
        IV : - pos (succ r) ＝ k' - pos d'
        IV = - pos (succ r)               ＝⟨ refl ⟩
             negsucc r                    ＝⟨ i    ⟩
             pos 0 + negsucc r            ＝⟨ ii   ⟩
             k' + (- k') + negsucc r      ＝⟨ iii  ⟩
             k' + ((- k') - pos (succ r)) ＝⟨ iv   ⟩
             k' - (k' + pos (succ r))     ＝⟨ v    ⟩
             k' - pos (k ℕ+ succ r)       ＝⟨ vi   ⟩
             k' - pos d'                  ∎
         where
          i   = ℤ-zero-left-neutral (negsucc r) ⁻¹
          ii  = ap (_+  negsucc r) (ℤ-sum-of-inverse-is-zero k' ⁻¹)
          iii = ℤ+-assoc k' (- k') (negsucc r)
          iv  = ap (k' +_) (negation-dist k' (pos (succ r)))
          v   = ap (λ z → k' - z) (distributivity-pos-addition k (succ r))
          vi  = ap (λ z → k' - pos z) e₂

        V : a' ＝ negsucc (succ q) ℤ* pos d' + k'
        V = a'                                      ＝⟨ refl               ⟩
            - pos (succ a)                          ＝⟨ ap -_ (ap pos e₁)  ⟩
            - pos (succ q ℕ* d' ℕ+ succ r)          ＝⟨ i                  ⟩
            - (pos (succ q ℕ* d') + pos (succ r))   ＝⟨ ii                 ⟩
            (- pos (succ q ℕ* d')) - pos (succ r)   ＝⟨ iii                ⟩
            (- q' ℤ* pos d') - pos (succ r)         ＝⟨ iv                 ⟩
            (- q' ℤ* pos d') + (k' - pos d')        ＝⟨ v                  ⟩
            (- q' ℤ* pos d') - pos d' + k'          ＝⟨ vi                 ⟩
            (- pos d' ℤ* q') - pos d' + k'          ＝⟨ vii                ⟩
            (- pos d') ℤ* q' - pos d' + k'          ＝⟨ viii               ⟩
            (- pos d') ℤ* q' - pos d' ℤ* pos 1 + k' ＝⟨ ix                 ⟩
            (- pos d') ℤ* (q' + pos 1) + k'         ＝⟨ refl               ⟩
            (- pos d') ℤ* pos (succ (succ q)) + k'  ＝⟨ x                  ⟩
            (- pos d' ℤ* pos (succ (succ q))) + k'  ＝⟨ xi                 ⟩
            (- pos (succ (succ q)) ℤ* pos d') + k'  ＝⟨ xii                ⟩
            negsucc (succ q) ℤ* pos d' + k'         ∎
             where
              iₐₚ    = distributivity-pos-addition (succ q ℕ* d') (succ r) ⁻¹
              iiiₐₚ  = pos-multiplication-equiv-to-ℕ (succ q) d' ⁻¹
              viiₐₚ  = negation-dist-over-mult' (pos d') q' ⁻¹
              viiiₐₚ = ℤ-mult-right-id (- pos d')
              ixₐₚ   = distributivity-mult-over-ℤ' q' (pos 1) (- pos d') ⁻¹
              xₐₚ    = negation-dist-over-mult' (pos d') (pos (succ (succ q)))
              xiₐₚ   = ℤ*-comm (pos d') (pos (succ (succ q)))
              xiiₐₚ  = negation-dist-over-mult' (pos (succ (succ q))) (pos d') ⁻¹

              i    = ap -_ iₐₚ
              ii   = negation-dist (pos (succ q ℕ* d')) (pos (succ r)) ⁻¹
              iii  = ap (λ z → (- z) - pos (succ r)) iiiₐₚ
              iv   = ap ((- q' ℤ* pos d') +_) IV
              v    = ℤ+-rearrangement (- (q' ℤ* pos d')) k' (- pos d') ⁻¹
              vi   = ap (λ z → ((- z) + (- pos d')) + k') (ℤ*-comm q' (pos d'))
              vii  = ap (λ z → (z + (- pos d')) + k') viiₐₚ
              viii = ap (λ z → ((- pos d') ℤ* q' + z) + k') viiiₐₚ ⁻¹
              ix   = ap (_+ k') ixₐₚ
              x    = ap (_+ k') xₐₚ
              xi   = ap (λ z → (- z) + k') xiₐₚ
              xii  = ap (_+ k') xiiₐₚ

    γ : Σ r ꞉ ℕ , (a' ＝ negsucc (succ q) ℤ* pos d' + pos r) × r < d'
    γ = I (subtraction' (succ r) (succ d) l₁)

ℤ-∣-respects-addition : (x y z : ℤ) → x ∣ y → x ∣ z → x ∣ y + z
ℤ-∣-respects-addition x y z (α , αₚ) (β , βₚ) = α + β , I
 where
  I : x ℤ* (α + β) ＝ y + z
  I = x ℤ* (α + β)    ＝⟨ distributivity-mult-over-ℤ' α β x ⟩
      x ℤ* α + x ℤ* β ＝⟨ ap₂ _+_ αₚ βₚ                      ⟩
      y + z           ∎

ℤ-∣-respects-addition-of-multiples : (x y z k l : ℤ)
                                  → x ∣ y
                                  → x ∣ z
                                  → x ∣ (y ℤ* k + z ℤ* l)
ℤ-∣-respects-addition-of-multiples x y z k l (α , αₚ) (β , βₚ) = γ
 where
  I : x ℤ* (α ℤ* k + β ℤ* l) ＝ y ℤ* k + z ℤ* l
  I = x ℤ* (α ℤ* k + β ℤ* l)        ＝⟨ i   ⟩
      x ℤ* (α ℤ* k) + x ℤ* (β ℤ* l) ＝⟨ ii  ⟩
      x ℤ* α ℤ* k + x ℤ* β ℤ* l     ＝⟨ iii ⟩
      y ℤ* k + z ℤ* l               ∎
   where
    i   = distributivity-mult-over-ℤ' (α ℤ* k) (β ℤ* l) x
    ii  = ap₂ _+_ (ℤ*-assoc x α k ⁻¹) (ℤ*-assoc x β l ⁻¹)
    iii = ap₂ _+_ (ap (_ℤ* k) αₚ) (ap (_ℤ* l) βₚ)

  γ : Σ v ꞉ ℤ , x ℤ* v ＝ y ℤ* k + z ℤ* l
  γ = α ℤ* k + β ℤ* l , I

\end{code}
