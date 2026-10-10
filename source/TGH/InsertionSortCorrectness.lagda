Theo Hepburn, started February 2025.

Provides an implementation of insertion sort
in our language.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt

module TGH.InsertionSortCorrectness (fe : naive-funext 𝓤₀ 𝓤₀) where

open import TGH.Strategy
open import Naturals.Addition
 renaming (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Subtraction
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin hiding (pred)
open import MLTT.List hiding (concat)
open import UF.Base
open import TGH.Thunk
open import TGH.Language fe
open import TGH.AFP2024.InsertionSort ℕ _<_ <-trichotomous
 renaming (insert to insert')

call-intermediate-l-n : {σ : LType} → Closed (list ⇒ nat ⇒ σ)
                      → (strategy : Strategy) → List ℕ → ℕ → ⟦ σ ⟧ᵢ
call-intermediate-l-n t s l n
 = (pr₁ ((pr₁ ([] [ t ]ᵢ s)) (0 , (return l)))) (0 , return n)

subtract : {n : ℕ} {Γ : Ctx n} → Term Γ (nat ⇒ nat ⇒ nat)
subtract = lam nat (lam nat (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))

concat : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ list ⇒ list)
concat = lam list (lam list (lrec (var 𝟏) (var 𝟎)
         (lam list (lam nat (cons (var 𝟎) (var 𝟏))))))

remove-greater-than-from-end : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ nat ⇒ list)
remove-greater-than-from-end
 = lam list (lam nat (lrec (var 𝟏) nil (lam list (lam nat
   (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else cons (var 𝟎) (var 𝟏))))))

remove-less-than-from-start : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ nat ⇒ list)
remove-less-than-from-start
 = lam list (lam nat (lrec (var 𝟏) nil (lam list (lam nat
   (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else var 𝟏)))))

insert : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ nat ⇒ list)
insert
 = lam list (lam nat (concat ∙
   (remove-greater-than-from-end ∙ (var 𝟏) ∙ (var 𝟎))
   ∙ (cons (var 𝟎) (remove-less-than-from-start ∙ (var 𝟏) ∙ (var 𝟎)))))

sort : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ list)
sort
 = lam list (lrec (var 𝟎) nil (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎)))))

concat-env-lemma : {n₁ n₂ : ℕ} → {Γ₁ : Ctx n₁}
                 → {Γ₂ : Ctx n₂} → {env₁ : Env Γ₁} → {env₂ : Env Γ₂}
                 → {ys : List ℕ}
                 → (xs : List ℕ)
                 → list-rec (ys ∷E env₁) xs (var 𝟎)
                   (lam list (lam nat (cons (var 𝟎) (var 𝟏))))
                 ＝
                   list-rec (ys ∷E env₂) xs (var 𝟎)
                   (lam list (lam nat (cons (var 𝟎) (var 𝟏))))
concat-env-lemma [] = refl
concat-env-lemma (x ∷ xs) = ap (x ∷_) (concat-env-lemma xs)

concat-correctness : {n : ℕ} {Γ : Ctx n} {env : Env Γ}
                   → (xs : List ℕ) → (ys : List ℕ)
                   → (env [ concat ]ₑ) xs ys ＝ xs ++ ys
concat-correctness [] ys = refl
concat-correctness {_} {_} {env} (x ∷ xs) ys = x ∷
      list-rec (ys ∷E (x ∷ xs) ∷E env) xs (var 𝟎)
      (lam list (lam nat (cons (var 𝟎) (var 𝟏))))
      ＝⟨ ap (x ∷_) (concat-env-lemma xs) ⟩
      (x ∷
      list-rec (ys ∷E xs ∷E env) xs (var 𝟎)
      (lam list (lam nat (cons (var 𝟎) (var 𝟏)))))
      ＝⟨ ap (x ∷_) (concat-correctness xs ys) ⟩
      x ∷ (xs ++ ys) ∎

ℕ-subtract : ℕ → ℕ → ℕ
ℕ-subtract n zero = n
ℕ-subtract n (succ m) = pred' (ℕ-subtract n m)

subtract-env-lemma : {n₁ n₂ : ℕ} → {Γ₁ : Ctx n₁} → {Γ₂ : Ctx n₂}
                   → {env₁ : Env Γ₁} → {env₂ : Env Γ₂}
                   → {y₁ y₂ : ℕ}
                   → (x y : ℕ)
                   → nat-rec (y₁ ∷E x ∷E env₁) y (var 𝟏)
                     (lam nat (pred (var 𝟎)))
                   ＝ nat-rec (y₂ ∷E x ∷E env₂)
                      y (var 𝟏) (lam nat (pred (var 𝟎)))
subtract-env-lemma x zero = refl
subtract-env-lemma x (succ y) = ap pred' (subtract-env-lemma x y)

subtract-correctness : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (x y : ℕ)
                      → (env [ subtract ]ₑ) x y ＝ ℕ-subtract x y
subtract-correctness x zero = refl
subtract-correctness {_} {_} {env} x (succ y)
 = pred' (nat-rec (succ y ∷E x ∷E env) y (var 𝟏)
       (lam nat (pred (var 𝟎)))) ＝⟨ ap pred' (subtract-env-lemma x y)  ⟩
       pred' (nat-rec (y ∷E x ∷E env) y (var 𝟏)
       (lam nat (pred (var 𝟎)))) ＝⟨ ap pred' (subtract-correctness x y) ⟩
       pred' (ℕ-subtract x y) ∎

ℕ-subtract-lemma-I : (n m : ℕ)
                  → (n ≤ m) → ℕ-subtract n m ＝ 0
ℕ-subtract-lemma-I n zero n≤m = zero-least'' n n≤m
ℕ-subtract-lemma-I n (succ m) n≤m = γ (subtraction n (succ m) n≤m)
 where
  γ : Σ (λ k → k + n ＝ succ m)
    → ℕ-subtract n (succ m) ＝ 0
  γ (zero , eq)
   = ap pred' (transport (λ z → ℕ-subtract z m ＝ 1)
      (( n ＝⟨ (zero-left-neutral n)⁻¹ ⟩
      0 + n ＝⟨ eq ⟩
      succ m ∎ )⁻¹) (γ' 1 m))
   where
    γ' : (k n : ℕ) → ℕ-subtract (n + k) n ＝ k
    γ' k zero = zero-left-neutral k
    γ' k (succ n)
     = pred' (ℕ-subtract (succ n + k) n)
       ＝⟨ ap (λ z → pred' (ℕ-subtract z n)) (succ-left n k) ⟩
       pred' (ℕ-subtract (n + succ k) n) ＝⟨ ap pred' (γ' (succ k) n) ⟩
       pred' (succ k) ＝⟨ refl ⟩
       k ∎
  γ (succ k , eq)
   = ap pred' (ℕ-subtract-lemma-I n m (cosubtraction n m (k ,
     ap pred' (succ (k + n) ＝⟨ (succ-left k n)⁻¹ ⟩
     succ k + n ＝⟨ eq ⟩
     succ m ∎))))

less-than-implies-neq : (n m : ℕ) → (n < m) → m ≠ n
less-than-implies-neq .(succ m) (succ m) le refl = not-less-than-itself m le

ℕ-subtract-lemma-II : (n m : ℕ)
                    → m < n → 0 < ℕ-subtract n m
ℕ-subtract-lemma-II (succ n) zero m<n = ⋆
ℕ-subtract-lemma-II (succ n) (succ m) m<n
 = transport (1 ≤_) (ap pred' (γ n m m<n)⁻¹) IH
 where
  IH : 0 < pred' (succ (ℕ-subtract n m))
  IH = ℕ-subtract-lemma-II n m m<n

  γ : (n m : ℕ) → m < n → ℕ-subtract (succ n) m ＝ succ (ℕ-subtract n m)
  γ n zero m<n = refl
  γ (succ n) (succ m) m<n = pred' (ℕ-subtract (succ (succ n)) m)
                            ＝⟨ ap pred' (γ (succ n) m m≤n) ⟩
                            ℕ-subtract (succ n) m
                            ＝⟨ (succ-pred' (ℕ-subtract (succ n) m)
                            (less-than-implies-neq 0 (ℕ-subtract (succ n) m)
                            (ℕ-subtract-lemma-II (succ n) m m≤n)))⁻¹ ⟩
                            succ (pred' (ℕ-subtract (succ n) m)) ∎
   where
    m≤n : m ≤ n
    m≤n = ≤-trans m (succ m) n (≤-succ m) m<n

subtract-lemma-I : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (y x : ℕ)
                → (y ≤ x) → (env [ subtract ]ₑ) y x ＝ 0
subtract-lemma-I {_} {_} {env} y x y≤x
 = (env [ subtract ]ₑ) y x ＝⟨ subtract-correctness y x ⟩
   ℕ-subtract y x ＝⟨ ℕ-subtract-lemma-I y x y≤x ⟩
   0 ∎

subtract-lemma-II : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (y x : ℕ)
                   → (x < y) → 0 < (env [ subtract ]ₑ) y x
subtract-lemma-II y x x<y
 = transport (0 <_) ((subtract-correctness y x)⁻¹) (ℕ-subtract-lemma-II y x x<y)

remove-less-than-from-start-env-lemma : {n₁ n₂ : ℕ}
                                  → {Γ₁ : Ctx n₁} → {Γ₂ : Ctx n₂}
                                  → {env₁ : Env Γ₁} → {env₂ : Env Γ₂}
                                  → {y : ℕ}
                                  → (xs : List ℕ)
                                  → list-rec (y ∷E env₁) xs nil (lam list
                                    (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
                                    then cons (var 𝟎) (var 𝟏) else var 𝟏)))
                                  ＝ list-rec (y ∷E env₂) xs nil (lam list
                                    (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
                                    then cons (var 𝟎) (var 𝟏) else var 𝟏)))
remove-less-than-from-start-env-lemma [] = refl
remove-less-than-from-start-env-lemma {_} {_} {_} {_} {env₁} {env₂} {y}(x ∷ xs)
 = if' ((x ∷E
         list-rec (y ∷E env₁) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then cons (var 𝟎) (var 𝟏) else var 𝟏)))
         ∷E y ∷E env₁) [ subtract ]ₑ) y x then' (x ∷ list-rec (y ∷E env₁) xs
         nil (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons
         (var 𝟎) (var 𝟏) else var 𝟏))))
    else' list-rec (y ∷E env₁) xs nil (lam list (lam nat (if subtract
    ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else var 𝟏)))
    ＝⟨ ap (λ z → if' z then' (x ∷ list-rec (y ∷E env₁) xs nil
    (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
    then cons (var 𝟎) (var 𝟏) else var 𝟏))))
    else' list-rec (y ∷E env₁) xs nil (lam list (lam nat
    (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else
    var 𝟏)))) (subtract-env-lemma y x) ⟩
    (if' ((x ∷E
         list-rec (y ∷E env₂) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then cons (var 𝟎) (var 𝟏) else var 𝟏)))
         ∷E y ∷E env₂) [ subtract ]ₑ) y x then' (x ∷ list-rec (y ∷E env₁)
         xs nil (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
         then cons (var 𝟎) (var 𝟏) else var 𝟏))))
    else' list-rec (y ∷E env₁) xs nil (lam list (lam nat (if subtract
    ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else var 𝟏))))
    ＝⟨ ap
       (λ z →
            if'
              nat-rec
                (x ∷E
                   y ∷E
                     x ∷E
                       list-rec (y ∷E env₂) xs nil
                         (lam list
                         (lam nat
                           (if
                           lam nat
                             (lam nat
                               (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
                               ∙ var 𝟐
                               ∙ var 𝟎
                         then cons (var 𝟎) (var 𝟏) else var 𝟏)))
                         ∷E y ∷E env₂)
                         x (var 𝟏) (lam nat (pred (var 𝟎)))
                         then' x ∷ z else' z)
              (remove-less-than-from-start-env-lemma xs) ⟩
    if' ((x ∷E
          list-rec (y ∷E env₂) xs nil
          (lam list
           (lam nat
            (if
             lam nat
             (lam nat
              (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
             ∙ var 𝟐
             ∙ var 𝟎
             then cons (var 𝟎) (var 𝟏) else var 𝟏)))
          ∷E y ∷E env₂) [ subtract ]ₑ) y x then' (x ∷ list-rec (y ∷E env₂) xs
          nil (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons
          (var 𝟎) (var 𝟏) else var 𝟏))))
    else' list-rec (y ∷E env₂) xs nil (lam list (lam nat (if subtract ∙ (var 𝟐)
    ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else var 𝟏))) ∎

remove-greater-than-from-end-env-lemma : {n₁ n₂ : ℕ}
                                   → {Γ₁ : Ctx n₁} → {Γ₂ : Ctx n₂}
                                   → {env₁ : Env Γ₁} → {env₂ : Env Γ₂}
                                   → {y : ℕ}
                                   → (xs : List ℕ)
                                   → list-rec (y ∷E env₁) xs nil (lam list
                                     (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
                                     then nil else cons (var 𝟎) (var 𝟏))))
                                    ＝ list-rec (y ∷E env₂) xs nil (lam list
                                     (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
                                     then nil else cons (var 𝟎) (var 𝟏))))
remove-greater-than-from-end-env-lemma [] = refl
remove-greater-than-from-end-env-lemma {_} {_} {_} {_}
 {env₁} {env₂} {y} (x ∷ xs)
 = if' ((x ∷E
         list-rec (y ∷E env₁) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then nil else cons (var 𝟎) (var 𝟏))))
         ∷E y ∷E env₁) [ subtract ]ₑ) y x
   then' []
   else' (x ∷ (list-rec (y ∷E env₁) xs nil (lam list (lam nat
   (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else cons (var 𝟎) (var 𝟏))))))
   ＝⟨ ap (λ z → if' z then' [] else' (x ∷ (list-rec (y ∷E env₁) xs nil
   (lam list
   (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else cons (var 𝟎)
   (var 𝟏))))))) (subtract-env-lemma y x) ⟩
     (if' ((x ∷E
         list-rec (y ∷E env₂) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then nil else cons (var 𝟎) (var 𝟏))))
         ∷E y ∷E env₂) [ subtract ]ₑ) y x
     then' []
     else' (x ∷ (list-rec (y ∷E env₁) xs nil (lam list (lam nat
       (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else cons (var 𝟎) (var 𝟏)))))))
       ＝⟨ ap (λ z → (if' ((x ∷E
         list-rec (y ∷E env₂) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then nil else cons (var 𝟎) (var 𝟏))))
         ∷E y ∷E env₂) [ subtract ]ₑ) y x
         then' []
         else' (x ∷ z))) (remove-greater-than-from-end-env-lemma xs) ⟩
         ((if' ((x ∷E
         list-rec (y ∷E env₂) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then nil else cons (var 𝟎) (var 𝟏))))
         ∷E y ∷E env₂) [ subtract ]ₑ) y x
           then' []
           else' (x ∷ (list-rec (y ∷E env₂) xs nil (lam list (lam nat
                 (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else
                 cons (var 𝟎) (var 𝟏)))))))) ∎

if-then-else-ap : {X : 𝓤₀ ̇ } {x y : X} → {n : ℕ} → (n ＝ 0)
                                                  → if' n then' x else' y ＝ x
if-then-else-ap refl = refl

≤-lemma : (x y : ℕ) → (y ＝ x) ∔ (succ x ≤ y) → x ≤ y
≤-lemma x y (inl eq) = transport (x ≤_) ((eq)⁻¹) (≤-refl x)
≤-lemma x y (inr le) = ≤-trans x (succ x) y (≤-succ x) le

remove-less-than-from-start-≤ : {n : ℕ} {Γ : Ctx n} {env : Env Γ}
                          → (xs : List ℕ) → (x y : ℕ)
                          → (y ≤ x)
                          → Sorted (x ∷ xs)
                          → (env [ remove-less-than-from-start ]ₑ) (x ∷ xs) y
                             ＝ x ∷ xs
remove-less-than-from-start-≤ {n} {Γ} {env} [] x y y≤x srtd
 = if' ((x ∷E
         list-rec (y ∷E (_∷E_ {_} {_} {list} (x ∷ []) env)) [] nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then cons (var 𝟎) (var 𝟏) else var 𝟏)))
         ∷E y ∷E (x ∷ []) ∷E env) [ subtract ]ₑ) y x
   then' x ∷ []
   else' [] ＝⟨ ap (λ z → if' z then' x ∷ [] else' [])
   (subtract-lemma-I y x y≤x) ⟩
         if' 0 then' x ∷ [] else' [] ＝⟨ refl ⟩
         x ∷ [] ∎
remove-less-than-from-start-≤ {n} {Γ} {env} (z ∷ xs) x y y≤x
 (adj-sorted srtd x≤z)
 = if' ((x ∷E
   list-rec (y ∷E (x ∷ z ∷ xs) ∷E _) (z ∷ xs) nil
   (lam list
     (lam nat
     (if
     lam nat
     (lam nat
     (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
     ∙ var 𝟐
     ∙ var 𝟎
     then cons (var 𝟎) (var 𝟏) else var 𝟏)))
   ∷E y ∷E (x ∷ z ∷ xs) ∷E _) [ subtract ]ₑ) y x
   then' x ∷ list-rec (y ∷E (_∷E_ {_} {_} {list} (x ∷ z ∷ xs) env))
   (z ∷ xs) nil (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎)
   then cons (var 𝟎) (var 𝟏) else var 𝟏)))
   else' list-rec (y ∷E (_∷E_ {_} {_} {list} (x ∷ z ∷ xs) env)) (z ∷ xs)
   nil (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then
   cons (var 𝟎) (var 𝟏) else var 𝟏)))
   ＝⟨ if-then-else-ap (subtract-lemma-I y x y≤x) ⟩
   (x ∷ list-rec (y ∷E (x ∷ z ∷ xs) ∷E env) (z ∷ xs) nil (lam list
   (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏)
   else var 𝟏))))
   ＝⟨ ap (x ∷_) (remove-less-than-from-start-env-lemma (z ∷ xs)) ⟩
   (x ∷ list-rec (y ∷E (z ∷ xs) ∷E env) (z ∷ xs) nil (lam list (lam nat
   (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏) else var 𝟏))))
   ＝⟨ ap (x ∷_) (remove-less-than-from-start-≤ xs z y
   (≤-trans y x z y≤x (≤-lemma x z x≤z)) srtd) ⟩
   (x ∷ z ∷ xs) ∎                            

remove-greater-than-from-end-≤ : {n : ℕ} {Γ : Ctx n} {env : Env Γ}
                           → (xs : List ℕ) → (x y : ℕ)
                           → (y ≤ x)
                           → (env [ remove-greater-than-from-end ]ₑ) (x ∷ xs) y
                           ＝ []
remove-greater-than-from-end-≤ {_} {_} {env} xs x y y≤x
 = if' ((x ∷E
   list-rec (y ∷E (x ∷ xs) ∷E env) xs nil
     (lam list
       (lam nat
       (if
       lam nat
       (lam nat
       (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
       ∙ var 𝟐
       ∙ var 𝟎
       then nil else cons (var 𝟎) (var 𝟏))))
       ∷E y ∷E (x ∷ xs) ∷E env) [ subtract ]ₑ) y x
   then' []
   else' _
   ＝⟨ ap (λ z → if' z then' [] else' (x ∷ list-rec (y ∷E (x ∷ xs) ∷E env) xs
      nil
      (lam list
      (lam nat
      (if
      lam nat
      (lam nat
      (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
      ∙ var 𝟐
      ∙ var 𝟎
      then nil else cons (var 𝟎) (var 𝟏)))))) (subtract-lemma-I y x y≤x) ⟩
      (if' 0 then' [] else' ((x ∷ list-rec (y ∷E (x ∷ xs) ∷E env) xs nil
        (lam list
        (lam nat
        (if
        lam nat
        (lam nat
        (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
        ∙ var 𝟐
        ∙ var 𝟎
        then nil else cons (var 𝟎) (var 𝟏))))))) ＝⟨ refl ⟩
   [] ∎

ite-second-branch : {X : 𝓤₀ ̇ } → {x y : X}
                  → (n : ℕ) → 0 < n → if' n then' x else' y ＝ y
ite-second-branch (succ n) 0<n = refl

remove-less-than-from-start-< : {n : ℕ} {Γ : Ctx n} {env : Env Γ}
                          → (xs : List ℕ) → (x y : ℕ)
                           → x < y
                           → (env [ remove-less-than-from-start ]ₑ) (x ∷ xs) y
                           ＝ (env [ remove-less-than-from-start ]ₑ) xs y
remove-less-than-from-start-< {_} {_} {env} xs x y x<y
 = if' ((x ∷E
         list-rec (y ∷E (x ∷ xs) ∷E _) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then cons (var 𝟎) (var 𝟏) else var 𝟏)))
         ∷E y ∷E (x ∷ xs) ∷E _) [ subtract ]ₑ) y x
    then' x ∷ list-rec (y ∷E (_∷E_ {_} {_} {list} (x ∷ xs) env)) xs nil
          (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎)
          (var 𝟏) else var 𝟏)))
    else' list-rec (y ∷E (_∷E_ {_} {_} {list} (x ∷ xs) env)) xs nil (lam list
          (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then cons (var 𝟎) (var 𝟏)
          else var 𝟏))) ＝⟨ ite-second-branch (((x ∷E
         list-rec (y ∷E (x ∷ xs) ∷E _) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then cons (var 𝟎) (var 𝟏) else var 𝟏)))
         ∷E y ∷E (x ∷ xs) ∷E _) [ subtract ]ₑ) y x)
         (subtract-lemma-II y x x<y) ⟩
    list-rec (y ∷E (_∷E_ {_} {_} {list} (x ∷ xs) env)) xs nil
    (lam list (lam nat (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then
    cons (var 𝟎) (var 𝟏) else var 𝟏)))
    ＝⟨ remove-less-than-from-start-env-lemma xs ⟩
    (env [ remove-less-than-from-start ]ₑ) xs y ∎

remove-greater-than-from-end-< : {n : ℕ} {Γ : Ctx n} {env : Env Γ}
                           → (xs : List ℕ)
                           → (x y : ℕ)
                           → x < y
                           → (env [ remove-greater-than-from-end ]ₑ) (x ∷ xs) y
                           ＝ x ∷ ((env [ remove-greater-than-from-end ]ₑ) xs y)
remove-greater-than-from-end-< xs x y x<y
 = if' ((x ∷E
         list-rec (y ∷E (x ∷ xs) ∷E _) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then nil else cons (var 𝟎) (var 𝟏))))
         ∷E y ∷E (x ∷ xs) ∷E _) [ subtract ]ₑ) y x
    then' []
    else' (x ∷ (list-rec (y ∷E (x ∷ xs) ∷E _) xs nil (lam list (lam nat
          (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else cons (var 𝟎)
          (var 𝟏)))))) ＝⟨ ite-second-branch (((x ∷E
         list-rec (y ∷E (x ∷ xs) ∷E _) xs nil
         (lam list
          (lam nat
           (if
            lam nat
            (lam nat
             (nrec (var 𝟎) (var 𝟏) (lam nat (pred (var 𝟎)))))
            ∙ var 𝟐
            ∙ var 𝟎
            then nil else cons (var 𝟎) (var 𝟏))))
         ∷E y ∷E (x ∷ xs) ∷E _) [ subtract ]ₑ) y x)
         (subtract-lemma-II y x x<y) ⟩
    (x ∷ (list-rec (y ∷E (x ∷ xs) ∷E _) xs nil (lam list (lam nat
    (if subtract ∙ (var 𝟐) ∙ (var 𝟎) then nil else cons (var 𝟎) (var 𝟏))))))
    ＝⟨ ap (x ∷_) (remove-greater-than-from-end-env-lemma xs) ⟩
    (x ∷ (_ [ remove-greater-than-from-end ]ₑ) xs y) ∎

insert-lemma : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (xs : List ℕ) → (x y : ℕ)
              → x < y
              → (env [ insert ]ₑ) (x ∷ xs) y ＝ x ∷ ((env [ insert ]ₑ) xs y)
insert-lemma xs x y x<y
 = ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) (((y ∷E (x ∷ xs) ∷E _)
   [ remove-greater-than-from-end ]ₑ) (x ∷ xs) y) (y ∷ (((y ∷E (x ∷ xs) ∷E _)
   [ remove-less-than-from-start ]ₑ) (x ∷ xs) y)) ＝⟨ ap₂ (λ w z
   → ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) w (y ∷ z))
   (remove-greater-than-from-end-< xs x y x<y)
   (remove-less-than-from-start-< xs x y x<y) ⟩
   ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) (x ∷ (((y ∷E (x ∷ xs) ∷E _)
   [ remove-greater-than-from-end ]ₑ) xs y)) (y ∷ (((y ∷E (x ∷ xs) ∷E _)
   [ remove-less-than-from-start ]ₑ) xs y))
   ＝⟨ ap₂ (λ w z → ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) (x ∷ w) (y ∷ z))
   (remove-greater-than-from-end-env-lemma xs)
   (remove-less-than-from-start-env-lemma xs) ⟩
   ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) (x ∷ (((y ∷E xs ∷E _)
   [ remove-greater-than-from-end ]ₑ) xs y)) (y ∷ (((y ∷E xs ∷E _)
   [ remove-less-than-from-start ]ₑ) xs y)) ＝⟨ concat-correctness
   (x ∷ (((y ∷E xs ∷E _) [ remove-greater-than-from-end ]ₑ) xs y))
   (y ∷ (((y ∷E xs ∷E _) [ remove-less-than-from-start ]ₑ) xs y)) ⟩
   x ∷ ((((y ∷E xs ∷E _) [ remove-greater-than-from-end ]ₑ) xs y)
   ++ (y ∷ (((y ∷E xs ∷E _) [ remove-less-than-from-start ]ₑ) xs y)))
   ＝⟨ ap (x ∷_) (concat-correctness (((y ∷E xs ∷E _)
   [ remove-greater-than-from-end ]ₑ) xs y) (y ∷ (((y ∷E xs ∷E _)
   [ remove-less-than-from-start ]ₑ) xs y)))⁻¹  ⟩
   x ∷ ((y ∷E xs ∷E _) [ concat ]ₑ)
   (((y ∷E xs ∷E _) [ remove-greater-than-from-end ]ₑ) xs y)
   (y ∷ (((y ∷E xs ∷E _) [ remove-less-than-from-start ]ₑ) xs y)) ∎

insert-correctness : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (xs : List ℕ)
                   → (y : ℕ)
                   → Sorted xs
                   → (env [ insert ]ₑ) xs y ＝ insert' y xs
insert-correctness [] y srtd = refl
insert-correctness {_} {_} {env} (x ∷ xs) y srtd = γ (<-trichotomous x y)
 where
  γ : (trich : ((x < y) ∔ (x ＝ y) ∔ (y < x)))
    → (env [ insert ]ₑ) (x ∷ xs) y
    ＝ (insert-trich y x xs trich)
  γ (inl x<y)
   = (env [ insert ]ₑ) (x ∷ xs) y ＝⟨ insert-lemma xs x y x<y ⟩
      x ∷ ((env [ insert ]ₑ) xs y)
      ＝⟨ ap (x ∷_) (insert-correctness xs y (srtd' srtd)) ⟩
      x ∷ (insert' y xs) ∎
   where
    srtd' : Sorted (x ∷ xs) → Sorted xs
    srtd' sing-sorted = nil-sorted
    srtd' (adj-sorted srtd _) = srtd
  γ (inr y≤x)
   = ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) (((y ∷E (x ∷ xs) ∷E _)
     [ remove-greater-than-from-end ]ₑ) (x ∷ xs) y) (y ∷ (((y ∷E (x ∷ xs) ∷E _)
     [ remove-less-than-from-start ]ₑ) (x ∷ xs) y)) ＝⟨ ap₂ (λ w z
     → ((y ∷E (x ∷ xs) ∷E _) [ concat ]ₑ) w (y ∷ z))
     (remove-greater-than-from-end-≤ xs x y (≤-lemma y x y≤x))
     (remove-less-than-from-start-≤ xs x y (≤-lemma y x y≤x) srtd) ⟩
     ((y ∷E (_∷E_ {_} {_} {list} (x ∷ xs) env)) [ concat ]ₑ) []
     (y ∷ x ∷ xs) ＝⟨ concat-correctness {_} {_} {y ∷E
     (_∷E_ {_} {_} {list} (x ∷ xs) env)} [] (y ∷ x ∷ xs) ⟩
     [] ++ (y ∷ x ∷ xs) ＝⟨ refl ⟩
     y ∷ x ∷ xs ∎

insert-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                 → (xs : List ℕ) → (x : ℕ)
                 → (env₁ [ insert ]ₑ) xs x ＝ (env₂ [ insert ]ₑ) xs x
insert-env-lemma {_} {_} {_} {_} {env₁} {env₂} xs x
 = ((x ∷E xs ∷E env₁) [ concat ]ₑ) (((x ∷E xs ∷E env₁)
   [ remove-greater-than-from-end ]ₑ) xs x) (x ∷ (((x ∷E xs ∷E env₁)
   [ remove-less-than-from-start ]ₑ) xs x)) ＝⟨ concat-env-lemma
   ((((x ∷E xs ∷E env₁) [ remove-greater-than-from-end ]ₑ) xs x)) ⟩
   ((x ∷E xs ∷E env₂) [ concat ]ₑ) (((x ∷E xs ∷E env₁)
   [ remove-greater-than-from-end ]ₑ) xs x) (x ∷ (((x ∷E xs ∷E env₁)
   [ remove-less-than-from-start ]ₑ) xs x)) ＝⟨ ap₂ (λ w z → ((x ∷E xs ∷E env₂)
   [ concat ]ₑ) w (x ∷ z)) (remove-greater-than-from-end-env-lemma xs)
   (remove-less-than-from-start-env-lemma xs) ⟩
   ((x ∷E xs ∷E env₂) [ concat ]ₑ) (((x ∷E xs ∷E env₂)
   [ remove-greater-than-from-end ]ₑ) xs x) (x ∷ (((x ∷E xs ∷E env₂)
   [ remove-less-than-from-start ]ₑ) xs x)) ∎

sort-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 {env₁ : Env Γ₁} {env₂ : Env Γ₂} (xs : List ℕ)
               → (list-rec env₁ xs nil (lam list (lam nat
                 (insert ∙ (var 𝟏) ∙ (var 𝟎)))))
                 ＝ (list-rec env₂ xs nil (lam list
                    (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎)))))
sort-env-lemma [] = refl
sort-env-lemma {_} {_} {_} {_} {env₁} {env₂} (x ∷ xs)
 = ((x ∷E
   list-rec env₁ xs nil
   (lam list
   (lam nat
   (lam list
   (lam nat
   (lam list
   (lam list
   (lrec (var 𝟏) (var 𝟎)
   (lam list (lam nat (cons (var 𝟎) (var 𝟏))))))
   ∙
   (lam list
   (lam nat
   (lrec (var 𝟏) nil
   (lam list
   (lam nat
   (if subtract ∙ var 𝟐 ∙ var 𝟎 then nil else
   cons (var 𝟎) (var 𝟏))))))
   ∙ var 𝟏
   ∙ var 𝟎)
   ∙
   cons (var 𝟎)
   (remove-less-than-from-start ∙ var 𝟏 ∙ var 𝟎)))
   ∙ var 𝟏
   ∙ var 𝟎)))
   ∷E env₁) [ insert ]ₑ) (list-rec env₁ xs nil
   (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎))))) x ＝⟨ ap (λ z → ((x ∷E
   list-rec env₁ xs nil
   (lam list
   (lam nat
   (lam list
   (lam nat
   (lam list
   (lam list
   (lrec (var 𝟏) (var 𝟎)
   (lam list (lam nat (cons (var 𝟎) (var 𝟏))))))
   ∙
   (lam list
   (lam nat
   (lrec (var 𝟏) nil
   (lam list
   (lam nat
   (if subtract ∙ var 𝟐 ∙ var 𝟎 then nil else
   cons (var 𝟎) (var 𝟏))))))
   ∙ var 𝟏
   ∙ var 𝟎)
   ∙
   cons (var 𝟎)
   (remove-less-than-from-start ∙ var 𝟏 ∙ var 𝟎)))
   ∙ var 𝟏
   ∙ var 𝟎)))
   ∷E env₁) [ insert ]ₑ) z x) (sort-env-lemma xs) ⟩
   ((x ∷E
   list-rec _ xs nil
   (lam list
   (lam nat
   (lam list
   (lam nat
   (lam list
   (lam list
   (lrec (var 𝟏) (var 𝟎)
   (lam list (lam nat (cons (var 𝟎) (var 𝟏))))))
   ∙
   (lam list
   (lam nat
   (lrec (var 𝟏) nil
   (lam list
   (lam nat
   (if subtract ∙ var 𝟐 ∙ var 𝟎 then nil else
   cons (var 𝟎) (var 𝟏))))))
   ∙ var 𝟏
   ∙ var 𝟎)
   ∙
   cons (var 𝟎)
   (remove-less-than-from-start ∙ var 𝟏 ∙ var 𝟎)))
   ∙ var 𝟏
   ∙ var 𝟎)))
   ∷E env₁) [ insert ]ₑ) (list-rec env₂ xs nil (lam list (lam nat
   (insert ∙ (var 𝟏) ∙ (var 𝟎))))) x ＝⟨ insert-env-lemma
   (list-rec env₂ xs nil (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎))))) x ⟩
   ((x ∷E
   list-rec env₂ xs nil
   (lam list
   (lam nat
   (lam list
   (lam nat
   (lam list
   (lam list
   (lrec (var 𝟏) (var 𝟎)
   (lam list (lam nat (cons (var 𝟎) (var 𝟏))))))
   ∙
   (lam list
   (lam nat
   (lrec (var 𝟏) nil
   (lam list
   (lam nat
   (if subtract ∙ var 𝟐 ∙ var 𝟎 then nil else
   cons (var 𝟎) (var 𝟏))))))
   ∙ var 𝟏
   ∙ var 𝟎)
   ∙
   cons (var 𝟎)
   (remove-less-than-from-start ∙ var 𝟏 ∙ var 𝟎)))
   ∙ var 𝟏
   ∙ var 𝟎)))
   ∷E env₂) [ insert ]ₑ) (list-rec env₂ xs nil
   (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎))))) x ∎

sort-correctness : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (xs : List ℕ)
                 → (env [ sort ]ₑ) xs ＝ insertion-sort xs
sort-correctness [] = refl
sort-correctness {_} {_} {env} (x ∷ xs)
 = (env [ sort ]ₑ) (x ∷ xs) ＝⟨ refl ⟩
   list-rec ((x ∷ xs) ∷E env) (x ∷ xs) nil
   (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎)))) ＝⟨ refl ⟩
   ((x ∷E (list-rec ((x ∷ xs) ∷E env) xs nil (lam list (lam nat
   (insert ∙ (var 𝟏) ∙ (var 𝟎))))) ∷E (x ∷ xs) ∷E env) [ insert ]ₑ)
   (list-rec ((x ∷ xs) ∷E env) xs nil (lam list (lam nat (insert
   ∙ (var 𝟏) ∙ (var 𝟎))))) x ＝⟨ ap (λ z → ((x ∷E (list-rec ((x ∷ xs)
   ∷E env) xs nil (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎))))) ∷E (x ∷ xs)
   ∷E env) [ insert ]ₑ) z x) (sort-env-lemma xs) ⟩
   ((x ∷E (list-rec ((x ∷ xs) ∷E env) xs nil (lam list (lam nat (insert
   ∙ (var 𝟏) ∙ (var 𝟎))))) ∷E (x ∷ xs) ∷E env) [ insert ]ₑ) (list-rec
   (xs ∷E env) xs nil (lam list (lam nat (insert ∙ (var 𝟏) ∙ (var 𝟎))))) x
   ＝⟨ ap (λ z → ((x ∷E (list-rec ((x ∷ xs) ∷E env) xs nil (lam list (lam nat
   (insert ∙ (var 𝟏) ∙ (var 𝟎))))) ∷E (x ∷ xs) ∷E env) [ insert ]ₑ) z x)
   (sort-correctness xs) ⟩
   ((x ∷E (list-rec ((x ∷ xs) ∷E env) xs nil (lam list (lam nat (insert
   ∙ (var 𝟏) ∙ (var 𝟎))))) ∷E (x ∷ xs) ∷E env) [ insert ]ₑ)
   (insertion-sort xs) x ＝⟨ insert-correctness
   (insertion-sort xs) x (insertion-sort-is-sorted xs) ⟩
   insert' x (insertion-sort xs) ＝⟨ refl ⟩
   insertion-sort (x ∷ xs) ∎

\end{code}
