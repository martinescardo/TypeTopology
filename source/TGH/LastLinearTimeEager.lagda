Theo Hepburn, started February 2025.

A proof that the last function, when eager evaluation is used,
is linear time.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.LastLinearTimeEager (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec) hiding (head)
open import MLTT.Fin
open import MLTT.List
open import UF.Base
open import TGH.Thunk
open import TGH.BigO
open import TGH.NatOrder
open import TGH.Language fe
open import TGH.HeadExample fe
open import TGH.LastCorrectness fe
open import TGH.LastTimeListValueIndependent fe
open import TGH.ComplexityDefinitionsResults fe
open import TGH.P fe

last-comp : {n : ℕ} → {Γ : Ctx n} → Term (list ∷ Γ) nat
last-comp = (head ∙ (lrec (var 𝟎) nil (lam list (lam nat
            (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))))

length'-linear-time : {n : ℕ} {Γ : Ctx n} → is-linear-time length' (inl refl)
length'-linear-time {n} {Γ} = 4 , (1 , f')
 where
  f : (x : ℕ)
    → (l : List ℕ)
    → (env : Envᵢ Γ)
    → pr₁ (pr₁ (env [ length' ]ᵢ eager) (thunk-type (x ∷ l))) ≤
      (4 * length (x ∷ l))
  f x [] env = ⋆
  f x (y ∷ xs) env
   = γ₈ 
   where
    IH : pr₁ (pr₁ (env [ length' ]ᵢ eager) (thunk-type (y ∷ xs)))
         ≤ 4 * (length (y ∷ xs))
    IH = f y xs env
    
    γ₁ : pr₁
         (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
         (lam nat (lam nat (suc (var 𝟏)))) eager))
         (0 , return y)
         ＝ pr₁
         (eager-function-nat-helper ((0 , return (y ∷ xs)) ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (list-recᵢ ((0 , return (y ∷ xs)) ∷Eᵢ env) xs zero
         (lam nat (lam nat (suc (var 𝟏)))) eager))
         (0 , return y)
    γ₁ = length'-comp-same-env (y ∷ xs)

    γ₂ : succ (pr₁ (pr₁
         (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
           (lam nat (suc (var 𝟏)))
           (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
           (lam nat (lam nat (suc (var 𝟏)))) eager))
           (0 , return y))) ≤ 4 * length (y ∷ xs)
    γ₂ = transport (_≤ 4 * length (y ∷ xs)) (ap (succ ∘ pr₁) γ₁ ⁻¹) IH

    γ₃ : pr₁ (pr₁
         (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
           (lam nat (suc (var 𝟏)))
           (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
           (lam nat (lam nat (suc (var 𝟏)))) eager))
           (0 , return y)) ≤ 4 * length (y ∷ xs)
    γ₃ = ≤-trans (pr₁ (pr₁
         (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
           (lam nat (suc (var 𝟏)))
           (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
           (lam nat (lam nat (suc (var 𝟏)))) eager))
           (0 , return y)))
           (succ (pr₁ (pr₁
           (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
           (lam nat (suc (var 𝟏)))
           (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
           (lam nat (lam nat (suc (var 𝟏)))) eager))
           (0 , return y))))
           (4 * length (y ∷ xs))
           (≤-succ (pr₁ (pr₁
           (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
           (lam nat (suc (var 𝟏)))
           (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
           (lam nat (lam nat (suc (var 𝟏)))) eager))
           (0 , return y))))
           γ₂

    γ₄ : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
       → (l : Σ t ꞉ ℕ , Thunk t ℕ)
       → (x : ℕ)
       → pr₁ (pr₁ (eager-function-nat-helper env (lam nat (suc (var 𝟏))) l)
         (thunk-type x))
       ＝ 2 + (pr₁ l)
    γ₄ env (zero , return x₁) x = refl
    γ₄ env (succ pr₃ , (√ x₁)) x = ap succ (γ₄ env (pr₃ , x₁) x)

    γ₅ : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
       → (l : Σ t ꞉ ℕ , Thunk t ℕ)
       → (x : ℕ)
       → succ (pr₁ (pr₁ (eager-function-nat-helper env
         (lam nat (suc (var 𝟏))) l)
           (thunk-type x)))
         ＝ 3 + (pr₁ l)
    γ₅ env l x
     = succ (pr₁ (pr₁ (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       l) (thunk-type x))) ＝⟨ ap succ (γ₄ env l x) ⟩
       succ (2 + (pr₁ l)) ＝⟨ succ-left 2 (pr₁ l) ⁻¹ ⟩
       3 + (pr₁ l) ∎

    γ₆ : succ
         (pr₁
         (pr₁
         (eager-function-nat-helper (((0 , return (x ∷ y ∷ xs))) ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (pr₁
         (eager-function-nat-helper (((0 , return (x ∷ y ∷ xs)))
         ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (list-recᵢ (((0 , return (x ∷ y ∷ xs))) ∷Eᵢ env) xs zero
         (lam nat (lam nat (suc (var 𝟏)))) eager))
         (0 , return y)))
         (thunk-type x)))
         ＝
         3 +
         pr₁
         (pr₁
         (eager-function-nat-helper (_ ∷Eᵢ env) (lam nat (suc (var 𝟏)))
         (list-recᵢ (_ ∷Eᵢ env) xs zero
         (lam nat (lam nat (suc (var 𝟏)))) eager))
         (0 , return y))
    γ₆ = γ₅ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) (pr₁
         (eager-function-nat-helper ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (list-recᵢ ((0 , return (x ∷ y ∷ xs)) ∷Eᵢ env) xs zero
         (lam nat (lam nat (suc (var 𝟏)))) eager))
         (0 , return y)) x

    γ₇ : 3 +
          pr₁
            (pr₁
            (eager-function-nat-helper (_ ∷Eᵢ env) (lam nat (suc (var 𝟏)))
              (list-recᵢ (_ ∷Eᵢ env) xs zero
                (lam nat (lam nat (suc (var 𝟏)))) eager))
              (0 , return y))
            ≤ 4 + (4 * (length (y ∷ xs)))
    γ₇ = ≤-adding 3 4 (pr₁
          (pr₁
            (eager-function-nat-helper (_ ∷Eᵢ env) (lam nat (suc (var 𝟏)))
              (list-recᵢ (_ ∷Eᵢ env) xs zero
                (lam nat (lam nat (suc (var 𝟏)))) eager))
              (0 , return y))) (4 * length (y ∷ xs))
            ⋆
            γ₃

    γ₈ : succ
          (pr₁
            (pr₁
              (eager-function-nat-helper (((0 , return (x ∷ y ∷ xs))) ∷Eᵢ env)
              (lam nat (suc (var 𝟏)))
                (pr₁
                (eager-function-nat-helper (((0 , return (x ∷ y ∷ xs))) ∷Eᵢ env)
                (lam nat (suc (var 𝟏)))
                  (list-recᵢ (((0 , return (x ∷ y ∷ xs))) ∷Eᵢ env) xs zero
                  (lam nat (lam nat (suc (var 𝟏)))) eager))
                (0 , return y)))
              (thunk-type x)))
            ≤ 4 + (4 * length (y ∷ xs))
    γ₈ = transport (_≤ 4 + (4 * (length (y ∷ xs)))) (γ₆ ⁻¹) γ₇
        
  f' : Pi (List ℕ)
        (λ l →
           Pi (Envᵢ Γ)
           (λ env →
              is-polytime 1 4 1 (length l)
              (get-time (inl refl)
                (pr₁ (env [ length' ]ᵢ eager) (thunk-type l)))))
  f' (x ∷ xs) env ⋆ = f x xs env

recursive-call-linear-time : {n : ℕ} {Γ : Ctx n}
                           → is-linear-time-n (lam list
                             (lam nat recursive-call)) (inr refl)
recursive-call-linear-time {n} {Γ} = 9 , (1 , f)
 where
  f : (xs : List ℕ)
    → (x : ℕ)
    → (env : Envᵢ Γ)
    → (1 ≤ length xs)
    → get-time (inr refl)
      (pr₁
        (pr₁ (env [ lam list (lam nat recursive-call) ]ᵢ eager)
          (thunk-type xs))
        (thunk-type x))
        ≤ (9 * length xs ^ 1)
  f xs x env le = γ₉
   where
    fₗ : (xs : List ℕ)
       → is-polytime 1 4
         1 (length xs)
         (get-time (inl refl)
         (pr₁ ((_ ∷Eᵢ _ ∷Eᵢ env) [ length' ]ᵢ eager) (thunk-type xs)))
    fₗ xs = (pr₂ (pr₂ length'-linear-time)) xs ((0 , return x) ∷Eᵢ
            (0 , return xs) ∷Eᵢ env)

    γ₁ : pr₁ (thunk-if {list} (list-recᵢ ((0 , return xs) ∷Eᵢ (0 , return x)
         ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat (lam nat
         (suc (var 𝟏)))) eager) (3 , (√ (√ (√ return (x ∷ [])))))
         (1 , (√ return xs)))
         ≤ 3 + succ (pr₁ (list-recᵢ ((0 , return xs) ∷Eᵢ (0 , return x)
         ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat (lam nat (suc (var 𝟏)
         ))) eager))
    γ₁ = thunk-if-lemma (inr refl) (list-recᵢ ((0 , return xs) ∷Eᵢ
         (0 , return x) ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat
         (lam nat (suc (var 𝟏)))) eager) (3 , (√ (√ (√ return (x ∷ [])))))
         (1 , (√ return xs))

    γ₂ : succ (pr₁ (list-recᵢ ((0 , return xs) ∷Eᵢ (0 , return x) ∷Eᵢ
         (0 , return xs) ∷Eᵢ env) xs zero (lam nat (lam nat (suc (var 𝟏))))
         eager)) ≤ 4 * length xs
    γ₂ = fₗ xs le

    γ₃ : 3 + succ (pr₁ (list-recᵢ ((0 , return xs) ∷Eᵢ (0 , return x) ∷Eᵢ
         (0 , return xs) ∷Eᵢ env) xs zero (lam nat (lam nat (suc (var 𝟏))))
         eager)) ≤
         3 + 4 * length xs
    γ₃ = ≤-n-monotone-left (succ (pr₁ (list-recᵢ ((0 , return xs) ∷Eᵢ
         (0 , return x) ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat
         (lam nat (suc (var 𝟏)))) eager))) (4 * length xs) 3 γ₂

    γ₄ : pr₁ (thunk-if {list} (list-recᵢ ((0 , return xs) ∷Eᵢ
         (0 , return x) ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat
         (lam nat (suc (var 𝟏)))) eager) (3 , (√ (√ (√ return (x ∷ [])))))
         (1 , (√ return xs))) ≤ 3 + 4 * length xs
    γ₄ = ≤-trans (pr₁ (thunk-if {list} (list-recᵢ ((0 , return xs) ∷Eᵢ
         (0 , return x) ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat
         (lam nat (suc (var 𝟏)))) eager) (3 , (√ (√ (√ return (x ∷ [])))))
         (1 , (√ return xs))))
         (3 + succ (pr₁ (list-recᵢ ((0 , return xs) ∷Eᵢ (0 , return x)
         ∷Eᵢ (0 , return xs) ∷Eᵢ env) xs zero (lam nat (lam nat (suc (var 𝟏))))
         eager)))
         (3 + 4 * length xs)
         γ₁
         γ₃

    γ₅ : (3 + 4 * length xs) + 2 ＝ 5 + 4 * length xs
    γ₅ = (3 + 4 * length xs) + 2 ＝⟨ +-comm (3 + 4 * length xs) 2 ⟩
         2 + (3 + 4 * length xs) ＝⟨ +-assoc 2 3 (4 * length xs) ⁻¹ ⟩
         5 + 4 * length xs ∎

    γ₆ : succ
         (succ
         (pr₁
         (thunk-if {list}
         (list-recᵢ
         (_∷Eᵢ_ {_} {_} {list} (0 , return xs) (_∷Eᵢ_ {_} {_} {nat}
         (0 , return x) (_∷Eᵢ_ {_} {_} {list} (0 , return xs) env))) xs
         zero (lam nat (lam nat (suc (var 𝟏)))) eager)
         (3 , (√ (√ (√ return (x ∷ []))))) (1 , (√ return xs)))))
         ≤ 5 + 4 * length xs
    γ₆ = transport (succ
         (succ
         (pr₁
         (thunk-if {list}
         (list-recᵢ
         (_∷Eᵢ_ {_} {_} {list} (0 , return xs) (_∷Eᵢ_ {_} {_} {nat}
         (0 , return x) (_∷Eᵢ_ {_} {_} {list} (0 , return xs) env))) xs
         zero (lam nat (lam nat (suc (var 𝟏)))) eager)
         (3 , (√ (√ (√ return (x ∷ []))))) (1 , (√ return xs))))) ≤_)
         γ₅ γ₄

    γ₇ : 5 ≤ 5 * length xs
    γ₇ = multiplication-preserves-order-left 5 1 (length xs) le

    γ₈ : 5 + 4 * length xs
         ≤ 9 * length xs
    γ₈ = transport (5 + 4 * length xs ≤_) (distributivity-mult-over-addition'
         5 4 (length xs) ⁻¹)
         (≤-n-monotone-right 5 (5 * length xs) (4 * length xs) γ₇)

    γ₉ : get-time (inr refl)
         (pr₁
         (pr₁ (env [ lam list (lam nat recursive-call) ]ᵢ eager)
         (thunk-type xs))
         (thunk-type x))
         ≤ (9 * length xs)
    γ₉ = ≤-trans
         (get-time (inr refl)
           (pr₁
             (pr₁ (env [ lam list (lam nat recursive-call) ]ᵢ eager)
               (thunk-type xs))
             (thunk-type x)))
           (5 + 4 * length xs)
           (9 * length xs)
           γ₆
         γ₈

last-list'-length-1 : (x : ℕ) (xs : List ℕ) → length (last-list' (x ∷ xs)) ＝ 1
last-list'-length-1 x [] = refl
last-list'-length-1 x (y ∷ xs) = last-list'-length-1 y xs

last-list'-length-1' : (xs : List ℕ) → (0 < length xs)
                     → length (last-list' xs) ＝ 1
last-list'-length-1' (x ∷ xs) eq = last-list'-length-1 x xs

last-list-linear-time : {n : ℕ} {Γ : Ctx n}
                      → is-linear-time (lam list last-list) (inr refl)
last-list-linear-time {n} {Γ} = 11 , (1 , f')
 where
  f : (x : ℕ)
    → (xs : List ℕ)
    → (env : Envᵢ Γ)
    → get-time (inr refl)
      (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type (x ∷ xs)))
      ≤ (11 * length (x ∷ xs))
  f x [] env = ⋆
  f x (y ∷ xs) env = goal
   where
    fᵣ : (zs : List ℕ) → (x : ℕ) → is-polytime 1 9
         1 (length zs)
         (pr₁
         (pr₁
         (pr₁
         ((thunk-type (y ∷ xs) ∷Eᵢ env) [ lam list (lam nat recursive-call)
         ]ᵢ eager)
         (thunk-type zs))
         (thunk-type x)))
    fᵣ zs x = pr₂ (pr₂ (recursive-call-linear-time {succ n} {list ∷ Γ}))
              zs x  ((thunk-type (y ∷ xs)) ∷Eᵢ env)

    γ₁ : succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
         (y ∷ xs)) env) [ lam list (lam nat recursive-call) ]ᵢ eager))
         (list-recᵢ
         (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil
         (lam list (lam nat recursive-call)) eager))) (0 , return x)))
       ＝ pr₁ ((thunk-type {nat} (strip-thunk (0 , return x)) ∷Eᵢ (thunk-type
         {list} (strip-thunk {list} (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type
         {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam nat recursive-call))
         eager))) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env))
         [ recursive-call ]ᵢ eager) + succ (pr₁ (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
         (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam nat
         recursive-call)) eager))
    γ₁ = ap succ (adding-times-lemma-l-n-l ((thunk-type (y ∷ xs)) ∷Eᵢ env)
         recursive-call ((list-recᵢ ((thunk-type {list} (y ∷ xs)) ∷Eᵢ env)
         (y ∷ xs) nil (lam list (lam nat recursive-call)) eager))
         (0 , return x))
         ⁻¹

    γ₂ : succ (pr₁ (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs))
         env) (y ∷ xs) nil (lam list (lam nat recursive-call)) eager))
         ≤ 11 * length (y ∷ xs)
    γ₂ = f y xs env

    γ₃ : length (strip-thunk {list} (list-recᵢ ((thunk-type (y ∷ xs)) ∷Eᵢ env)
         (y ∷ xs) nil (lam list (lam nat recursive-call)) eager))
         ＝ 1
    γ₃ = length (strip-thunk {list} (list-recᵢ ((thunk-type (y ∷ xs)) ∷Eᵢ env)
         (y ∷ xs) nil (lam list (lam nat recursive-call)) eager))
         ＝⟨ ap length (equivalent-lrec-lemma _ (y ∷ xs) nil (lam list
         (lam nat recursive-call)) eager) ⟩
         length (list-rec ((y ∷ xs) ∷E (strip-thunk-env env)) (y ∷ xs) nil
         (lam list (lam nat recursive-call)))
         ＝⟨ ap length (last-list-correctness-any-env (y ∷ xs)) ⟩
         length (last-list' (y ∷ xs)) ＝⟨ last-list'-length-1 y xs ⟩
         1 ∎

    γ₄ : pr₁ ((thunk-type {nat} (strip-thunk (0 , return x))
         ∷Eᵢ (thunk-type {list} (strip-thunk {list} (list-recᵢ
         ((thunk-type (y ∷ xs)) ∷Eᵢ env) (y ∷ xs) nil (lam list
         (lam nat recursive-call)) eager))) ∷Eᵢ (thunk-type (y ∷ xs))
         ∷Eᵢ env) [ recursive-call ]ᵢ eager)
         ≤
         (9 *
          length
            (strip-thunk
              (list-recᵢ (_ ∷Eᵢ env) (y ∷ xs) nil
                (lam list (lam nat recursive-call)) eager))
         )
    γ₄ = fᵣ ((strip-thunk {list} (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type
         {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam nat recursive-call))
         eager))) x ((transport (1 ≤_) (γ₃ ⁻¹) (≤-refl 1)))
  
    γ₅ : pr₁ ((thunk-type {nat} (strip-thunk (0 , return x)) ∷Eᵢ (thunk-type
         {list} (strip-thunk {list} (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
         (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam nat
         recursive-call)) eager))) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type
         {list} (y ∷ xs)) env)) [ recursive-call ]ᵢ eager) ≤ 9
    γ₅ = transport (λ z → pr₁ ((thunk-type {nat} (strip-thunk (0 , return x))
         ∷Eᵢ (thunk-type {list} (strip-thunk {list} (list-recᵢ (_∷Eᵢ_ {_} {_}
         {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam
         nat recursive-call)) eager))) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type
         {list} (y ∷ xs)) env)) [ recursive-call ]ᵢ eager) ≤ 9 * z) γ₃ γ₄

    γ₆ : pr₁ ((thunk-type {nat} (strip-thunk (0 , return x)) ∷Eᵢ (thunk-type
         {list} (strip-thunk {list} (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type
         {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam nat recursive-call))
         eager))) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env))
         [ recursive-call ]ᵢ eager) + succ (pr₁ (list-recᵢ (_∷Eᵢ_ {_} {_}
         {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam
         nat recursive-call)) eager)) ≤ 9 + (11 * length (y ∷ xs))
    γ₆ = ≤-adding (pr₁ ((thunk-type {nat} (strip-thunk (0 , return x)) ∷Eᵢ
         (thunk-type {list} (strip-thunk {list} (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
         (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list (lam nat
         recursive-call)) eager))) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
         (y ∷ xs)) env)) [ recursive-call ]ᵢ eager)) 9 (succ (pr₁ (list-recᵢ
         (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil
         (lam list (lam nat recursive-call)) eager))) (11 * length (y ∷ xs))
         γ₅ γ₂

    γ₇ : succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
         (y ∷ xs))
         env) [ lam list (lam nat recursive-call) ]ᵢ eager)) (list-recᵢ
         (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs)
         nil (lam list (lam nat recursive-call)) eager))) (0 , return x)))
         ≤ 9 + (11 * length (y ∷ xs))
    γ₇ = transport (_≤ 9 + (11 * length (y ∷ xs))) (γ₁ ⁻¹) γ₆

    γ₈ : 9 + (11 * length (y ∷ xs)) ≤ 11 + (11 * length (y ∷ xs))
    γ₈ = ≤-n-monotone-right 9 11 (11 * length (y ∷ xs)) ⋆

    γ₉ : succ (pr₁ ((pr₁ ((pr₁ (((thunk-type {list} (y ∷ xs)) ∷Eᵢ env)
         [ lam list (lam nat recursive-call) ]ᵢ eager)) (list-recᵢ (_∷Eᵢ_ {_}
         {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list
         (lam nat recursive-call)) eager))) (0 , return x))) ≤ 11 + (11 * length
         (y ∷ xs))
    γ₉ = ≤-trans (succ (pr₁ ((pr₁ ((pr₁ (((thunk-type {list} (y ∷ xs)) ∷Eᵢ env)
         [ lam list (lam nat recursive-call) ]ᵢ eager)) (list-recᵢ (_∷Eᵢ_ {_}
         {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list
         (lam nat recursive-call)) eager))) (0 , return x)))) (9 + (11 * length
         (y ∷ xs))) (11 + (11 * length (y ∷ xs)))
         γ₇ γ₈

    γ₁₀ : succ (pr₁ ((pr₁ ((pr₁ (((thunk-type {list} (y ∷ xs)) ∷Eᵢ env)
          [ lam list (lam nat recursive-call) ]ᵢ eager)) (list-recᵢ (_∷Eᵢ_ {_}
          {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs) nil (lam list
          (lam nat recursive-call)) eager))) (0 , return x)))
        ＝ succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
          (x ∷ y ∷ xs)) env) [ lam list (lam nat recursive-call) ]ᵢ eager))
          (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (x ∷ y ∷ xs))
          env) (y ∷ xs) nil (lam list (lam nat recursive-call)) eager)))
          (0 , return x)))
    γ₁₀ = succ (pr₁ ((pr₁ ((pr₁ (((thunk-type {list} (y ∷ xs)) ∷Eᵢ env)
          [ lam list (lam nat recursive-call) ]ᵢ eager)) (list-recᵢ
          (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env) (y ∷ xs)
          nil (lam list (lam nat recursive-call)) eager))) (0 , return x)))
          ＝⟨ ap (λ z → succ (pr₁ z)) (eager-function-list-helper-env-lemma
          ((list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env)
          (y ∷ xs) nil (lam list (lam nat recursive-call)) eager)) x) ⟩
          succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
          (x ∷ y ∷ xs)) env) [ lam list (lam nat recursive-call) ]ᵢ eager))
          (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (y ∷ xs)) env)
          (y ∷ xs) nil (lam list (lam nat recursive-call)) eager)))
          (0 , return x))) ＝⟨ ap (λ z → succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_}
          {list} (thunk-type {list} (x ∷ y ∷ xs)) env) [ lam list (lam nat
          recursive-call) ]ᵢ eager)) z)) (0 , return x)))) (last-list-same-env
          (y ∷ xs))  ⟩
          succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
          (x ∷ y ∷ xs)) env) [ lam list (lam nat recursive-call) ]ᵢ eager))
          (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (x ∷ y ∷ xs)) env)
          (y ∷ xs) nil (lam list (lam nat recursive-call)) eager)))
          (0 , return x))) ∎

    goal : succ (pr₁ ((pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type {list}
           (x ∷ y ∷ xs)) env) [ lam list (lam nat recursive-call) ]ᵢ eager))
           (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type {list} (x ∷ y ∷ xs))
           env) (y ∷ xs) nil (lam list (lam nat recursive-call)) eager)))
           (0 , return x))) ≤ 11 + (11 * length (y ∷ xs))
    goal
     = transport (_≤ 11 + (11 * length (y ∷ xs))) γ₁₀ γ₉

  f' : Pi (List ℕ)
        (λ l →
          Pi (Envᵢ Γ)
            (λ env →
              is-polytime 1 11 1 (length l)
              (get-time (inr refl)
              (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type l)))))
  f' (x ∷ xs) env ⋆ = f x xs env

last-linear-time : {n : ℕ} {Γ : Ctx n} → is-linear-time last (inl refl)
last-linear-time {n} {Γ} = 15 , (1 , f)
 where
  f : Pi (List ℕ)
      (λ l →
      Pi (Envᵢ Γ)
      (λ env →
      is-polytime 1 15 1 (length l)
      (get-time (inl refl) (pr₁ (env [ last ]ᵢ eager) (thunk-type l)))))
  f xs env le = γ₁₄
   where
    fₗ : (xs : List ℕ)
       → is-polytime 1 11
         1 (length xs)
         (pr₁ (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type xs)))
    fₗ xs = pr₂ (pr₂ (last-list-linear-time {n} {Γ})) xs env

    fₕ : (l : List ℕ)
       → is-polytime 1 3
         1 (length l)
           (get-time (inl refl)
             (pr₁
               ((_∷Eᵢ_ {_} {_} {list} (thunk-type xs) env) [
                 lam list
                   (lrec (var 𝟎) zero
                   (lam nat
                     (lam nat (var 𝟎))))
         ]ᵢ eager)
         (thunk-type l)))
    fₕ ys le
     = pr₂ (pr₂ (eager-head-linear-time')) ys ((0 , return xs)
       ∷Eᵢ env) le

    γ₁ : succ (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
         ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager)))
       ＝ pr₁ (((thunk-type (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env)
         [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type xs) ∷Eᵢ env) [ head-comp ]ᵢ
         eager) + succ (pr₁ (((thunk-type xs) ∷Eᵢ env) [ last-list ]ᵢ eager))
    γ₁ = ap succ (adding-times-lemma (inr refl) (inl refl) (thunk-type xs ∷Eᵢ
         env) head-comp (((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager)) ⁻¹)

    γ₂ : succ (pr₁ (((thunk-type xs) ∷Eᵢ env) [ last-list ]ᵢ eager))
         ≤ succ (11 * length xs)
    γ₂ = fₗ xs le

    γ₃ : length (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env) [ last-list ]ᵢ
         eager)) ＝ 1
    γ₃ = length (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env) [ last-list ]ᵢ
         eager)) ＝⟨ ap length (equivalent-semantics ((thunk-type xs) ∷Eᵢ env)
         last-list eager) ⟩
         length ((xs ∷E (strip-thunk-env env)) [ last-list ]ₑ)
         ＝⟨ ap length (last-list-correctness-any-env xs) ⟩
         length (last-list' xs) ＝⟨ last-list'-length-1' xs le ⟩
         1 ∎

    γ₄ : pr₁ (((thunk-type (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env)
         [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type xs) ∷Eᵢ env) [ head-comp ]ᵢ
         eager) ≤ 3 * length (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env)
         [ last-list ]ᵢ eager))
    γ₄ = fₕ (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env) [ last-list ]ᵢ
         eager)) (transport (1 ≤_) (γ₃ ⁻¹) (≤-refl 1))

    γ₅ : pr₁ (((thunk-type (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env)
         [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type xs) ∷Eᵢ env) [ head-comp ]ᵢ
         eager) ≤ 3
    γ₅ = transport (λ z → pr₁ (((thunk-type (strip-thunk {list} (((thunk-type
         xs) ∷Eᵢ env) [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type xs) ∷Eᵢ env)
         [ head-comp ]ᵢ eager) ≤ 3 * z) γ₃ γ₄

    γ₆ : pr₁ (((thunk-type (strip-thunk {list} (((thunk-type xs) ∷Eᵢ env)
         [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type xs) ∷Eᵢ env) [ head-comp ]ᵢ
         eager) + succ (pr₁ (((thunk-type xs) ∷Eᵢ env) [ last-list ]ᵢ eager))
         ≤ 3 + (succ (11 * length xs))
    γ₆ = ≤-adding (pr₁ (((thunk-type (strip-thunk {list} (((thunk-type xs)
         ∷Eᵢ env) [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type xs) ∷Eᵢ env)
         [ head-comp ]ᵢ eager)) 3 (succ (pr₁ (((thunk-type xs) ∷Eᵢ env)
         [ last-list ]ᵢ eager))) (succ (11 * length xs)) γ₅ γ₂

    γ₇ : 3 + (succ (11 * length xs)) ＝ 4 + 11 * length xs
    γ₇ = succ-left 3 (11 * length xs) ⁻¹

    γ₈ : 4 + 11 * length xs ≤ 4 * length xs + 11 * length xs
    γ₈ = ≤-n-monotone-right 4 (4 * length xs) (11 * length xs)
         (multiplication-preserves-order-left 4 1 (length xs) le)

    γ₉ : 4 * length xs + 11 * length xs ＝ 15 * length xs
    γ₉ = distributivity-mult-over-addition' 4 11 (length xs) ⁻¹

    γ₁₀ : succ (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))) ≤ 3 +
          (succ (11 * length xs))
    γ₁₀ = transport (_≤ 3 + (succ (11 * length xs))) (γ₁ ⁻¹) γ₆

    γ₁₁ : succ (pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type xs) env) [ head ]ᵢ
          eager)) ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager)))
          ≤ 4 + 11 * length xs
    γ₁₁ = transport (succ (pr₁ ((pr₁ ((_∷Eᵢ_ {_} {_} {list} (thunk-type xs) env)
          [ head ]ᵢ eager)) ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))) ≤_)
          γ₇ γ₁₀

    γ₁₂ : 4 + 11 * length xs ≤ 15 * length xs
    γ₁₂ = transport (4 + 11 * length xs ≤_) γ₉ γ₈

    γ₁₃ : succ (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))) ≤ 15 * length xs
    γ₁₃ = ≤-trans (succ (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))))
          (4 + 11 * length xs)
          (15 * length xs)
          γ₁₁
          γ₁₂

    γ₁₄ : pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))
          ≤ 15 * length xs
    γ₁₄ = ≤-trans
          (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager)))
          (succ (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))))
          (15 * length xs)
          (≤-succ (pr₁ ((pr₁ ((thunk-type xs ∷Eᵢ env) [ head ]ᵢ eager))
          ((thunk-type xs ∷Eᵢ env) [ last-list ]ᵢ eager))))
          γ₁₃
        

last-linear-time' : {n : ℕ} {Γ : Ctx n} (env : Envᵢ Γ)
                  → (list-time-function-naive env (inl refl) last eager)
                    ∈O[ (λ n → n) ]
last-linear-time' {n} {Γ} = is-polytime-to-polybig-o {_} {n} {Γ} (inl refl)
                            last-comp 1 (last-linear-time {n} {Γ})

\end{code}
