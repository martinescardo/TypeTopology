Theo Hepburn, started February 2025.

A proof that the last program, when eager evaluation is used,
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
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec) hiding (head)
open import MLTT.Fin hiding (pred)
open import MLTT.List renaming (length to length')
open import UF.Base
open import TGH.Thunk
open import TGH.BigO
open import TGH.Language fe
open import TGH.HeadExample fe
open import TGH.LastCorrectness fe
open import TGH.LastTimeListValueIndependent fe
open import TGH.ComplexityDefinitionsResults fe
open import TGH.P fe

\end{code}

Proof that, when the eager evaluation strategy is used, `last` is linear time,
according to the Big O definition and our alternative definition.

\begin{code}

last-comp : {n : ℕ} → {Γ : Ctx n} → Term (list ∷ Γ) nat
last-comp = head ∙ (lrec (var 𝟎) nil last-step)

length'-step-applied-time : {n : ℕ} {Γ : Ctx n}
                          → (env : Envᵢ Γ)
                          → (l@(t , _) : Σ t ꞉ ℕ , Thunk t ℕ)
                          → (x : ℕ)
                          → pr₁ (length'-step-applied env l x) ＝ 2 + t
length'-step-applied-time env (zero , return x₁) x = refl
length'-step-applied-time env (succ pr₃ , (√ x₁)) x
 = ap succ (length'-step-applied-time env (pr₃ , x₁) x)

length'-step-applied-time-succ : {n : ℕ} {Γ : Ctx n}
                               → (env : Envᵢ Γ)
                               → (l@(t , _) : Σ t ꞉ ℕ , Thunk t ℕ)
                               → (x : ℕ)
                               → succ (pr₁ (length'-step-applied env l x))
                               ＝ 3 + t
length'-step-applied-time-succ env l@(t , _) x
 = succ (pr₁ (length'-step-applied env l x))
 ＝⟨ ap succ (length'-step-applied-time env l x) ⟩
   succ (2 + t)
 ＝⟨ succ-left 2 t ⁻¹ ⟩
   3 + t
 ∎

length'-linear-time : {n : ℕ} {Γ : Ctx n} → is-program-linear-time length (inl refl)
length'-linear-time {n} {Γ} = 4 , (1 , f')
 where
  f : (x : ℕ)
    → (l : List ℕ)
    → (env : Envᵢ Γ)
    → pr₁ (pr₁ (env [ length ]ᵢ eager) (thunk-type (x ∷ l)))
    ≤ (4 * length' (x ∷ l))
  f x [] env = ⋆
  f x (y ∷ xs) env = γ₈
   where
    env₀ : Envᵢ (list ∷ Γ)
    env₀ = (0 , return (x ∷ y ∷ xs)) ∷Eᵢ env

    env₁ : Envᵢ (list ∷ Γ)
    env₁ = (0 , return (y ∷ xs)) ∷Eᵢ env

    t₀ : Σ t ꞉ ℕ , Thunk t ℕ
    t₀ = length'-step-applied env₀ (list-recᵢ env₀ xs zero length'-step eager) y

    t₁ : Σ t ꞉ ℕ , Thunk t ℕ
    t₁ = length'-step-applied env₁ (list-recᵢ env₁ xs zero length'-step eager) y

    IH : pr₁ (pr₁ (env [ length ]ᵢ eager) (thunk-type (y ∷ xs)))
       ≤ 4 * (length' (y ∷ xs))
    IH = f y xs env

    γ₁ : t₀ ＝ t₁
    γ₁ = length-comp-same-env (y ∷ xs)

    γ₂ : succ (pr₁ t₀) ≤ 4 * length' (y ∷ xs)
    γ₂ = transport (_≤ 4 * length' (y ∷ xs)) (ap (succ ∘ pr₁) γ₁ ⁻¹) IH

    γ₃ : pr₁ t₀ ≤ 4 * length' (y ∷ xs)
    γ₃ = ≤-trans (pr₁ t₀) (succ (pr₁ t₀)) (4 * length' (y ∷ xs))
          (≤-succ (pr₁ t₀)) γ₂

    γ₄ : succ (pr₁ (length'-step-applied env₀ t₀ x)) ＝ 3 + pr₁ t₀
    γ₄ = length'-step-applied-time-succ env₀ t₀ x

    γ₅ : 3 + pr₁ t₀ ≤ 4 + (4 * length' (y ∷ xs))
    γ₅ = ≤-adding 3 4 (pr₁ t₀) (4 * length' (y ∷ xs)) ⋆ γ₃

    γ₈ : succ (pr₁ (length'-step-applied env₀ t₀ x))
       ≤ 4 + (4 * length' (y ∷ xs))
    γ₈ = transport (_≤ 4 + (4 * length' (y ∷ xs))) (γ₄ ⁻¹) γ₅

  f' : Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
     , is-polytime 1 4 1 (length' l)
        (get-time (inl refl)
         (pr₁ (env [ length ]ᵢ eager) (thunk-type l)))
  f' [] env ()
  f' (x ∷ xs) env ⋆ = f x xs env

recursive-call-linear-time : {n : ℕ} {Γ : Ctx n}
                           → is-program-linear-time-n last-step (inr refl)
recursive-call-linear-time {n} {Γ} = 9 , (1 , f)
 where
  f : (xs : List ℕ)
    → (x : ℕ)
    → (env : Envᵢ Γ)
    → (1 ≤ length' xs)
    → get-time (inr refl)
       (pr₁ (pr₁ (env [ last-step ]ᵢ eager) (thunk-type xs)) (thunk-type x))
    ≤ (9 * length' xs ^ 1)
  f xs x env le = γ₉
   where
    env' : Envᵢ (list ∷ nat ∷ list ∷ Γ)
    env' = length-call-env xs x env

    len : Σ t ꞉ ℕ , Thunk t ℕ
    len = list-recᵢ env' xs zero length'-step eager

    cond : Σ t ꞉ ℕ , Thunk t (List ℕ)
    cond = thunk-if {list} len (cons-branch x) (else-branch xs)

    γ₁ : pr₁ cond ≤ 3 + succ (pr₁ len)
    γ₁ = thunk-if-lemma (inr refl) len (cons-branch x) (else-branch xs)

    γ₂ : succ (pr₁ len) ≤ 4 * length' xs
    γ₂ = pr₂ (pr₂ (length'-linear-time {_} {nat ∷ list ∷ Γ})) xs
          ((0 , return x) ∷Eᵢ (0 , return xs) ∷Eᵢ env) le

    γ₃ : 3 + succ (pr₁ len) ≤ 3 + 4 * length' xs
    γ₃ = ≤-n-monotone-left (succ (pr₁ len)) (4 * length' xs) 3 γ₂

    γ₄ : pr₁ cond ≤ 3 + 4 * length' xs
    γ₄ = ≤-trans (pr₁ cond) (3 + succ (pr₁ len)) (3 + 4 * length' xs) γ₁ γ₃

    γ₅ : (3 + 4 * length' xs) + 2 ＝ 5 + 4 * length' xs
    γ₅
     = (3 + 4 * length' xs) + 2
     ＝⟨ +-comm (3 + 4 * length' xs) 2 ⟩
       2 + (3 + 4 * length' xs)
     ＝⟨ +-assoc 2 3 (4 * length' xs) ⁻¹ ⟩
       5 + 4 * length' xs
     ∎

    γ₆ : succ (succ (pr₁ cond)) ≤ 5 + 4 * length' xs
    γ₆ = transport (succ (succ (pr₁ cond)) ≤_) γ₅ γ₄

    γ₇ : 5 ≤ 5 * length' xs
    γ₇ = multiplication-preserves-order-left 5 1 (length' xs) le

    γ₈ : 5 + 4 * length' xs ≤ 9 * length' xs
    γ₈ = transport (5 + 4 * length' xs ≤_)
          (distributivity-mult-over-addition' 5 4 (length' xs) ⁻¹)
          (≤-n-monotone-right 5 (5 * length' xs) (4 * length' xs) γ₇)

    γ₉ : get-time (inr refl)
          (pr₁ (pr₁ (env [ last-step ]ᵢ eager) (thunk-type xs))
           (thunk-type x))
       ≤ (9 * length' xs)
    γ₉ = ≤-trans
          (get-time (inr refl)
           (pr₁ (pr₁ (env [ last-step ]ᵢ eager) (thunk-type xs))
            (thunk-type x)))
          (5 + 4 * length' xs)
          (9 * length' xs)
          γ₆
          γ₈

last-list'-length-1 : (x : ℕ) (xs : List ℕ) → length' (last-list' (x ∷ xs)) ＝ 1
last-list'-length-1 x [] = refl
last-list'-length-1 x (y ∷ xs) = last-list'-length-1 y xs

last-list'-length-1' : (xs : List ℕ)
                     → (0 < length' xs)
                     → length' (last-list' xs) ＝ 1
last-list'-length-1' [] ()
last-list'-length-1' (x ∷ xs) eq = last-list'-length-1 x xs

last-list-linear-time : {n : ℕ} {Γ : Ctx n}
                      → is-program-linear-time (lam list last-list) (inr refl)
last-list-linear-time {n} {Γ} = 11 , (1 , f')
 where
  f : (x : ℕ)
    → (xs : List ℕ)
    → (env : Envᵢ Γ)
    → get-time (inr refl)
       (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type (x ∷ xs)))
    ≤ (11 * length' (x ∷ xs))
  f x [] env = ⋆
  f x (y ∷ xs) env = goal
   where
    E_y : Envᵢ (list ∷ Γ)
    E_y = thunk-type {list} (y ∷ xs) ∷Eᵢ env

    E_x : Envᵢ (list ∷ Γ)
    E_x = thunk-type {list} (x ∷ y ∷ xs) ∷Eᵢ env

    r_y : Σ t ꞉ ℕ , Thunk t (List ℕ)
    r_y = list-recᵢ E_y (y ∷ xs) nil last-step eager

    r_x : Σ t ꞉ ℕ , Thunk t (List ℕ)
    r_x = list-recᵢ E_x (y ∷ xs) nil last-step eager

    fᵣ : (zs : List ℕ)
       → (x : ℕ)
       → is-polytime 1 9 1 (length' zs)
          (pr₁ (last-step-applied E_y (thunk-type zs) x))
    fᵣ zs x = pr₂ (pr₂ (recursive-call-linear-time {succ n} {list ∷ Γ}))
               zs x E_y

    γ₁ : succ (pr₁ (last-step-applied E_y r_y x))
       ＝ recursive-call-time E_y r_y x + succ (pr₁ r_y)
    γ₁ = ap succ
          (adding-times-lemma-l-n-l E_y recursive-call r_y (0 , return x) ⁻¹)

    γ₂ : succ (pr₁ r_y) ≤ 11 * length' (y ∷ xs)
    γ₂ = f y xs env

    γ₃ : length' (strip-thunk {list} r_y) ＝ 1
    γ₃
     = length' (strip-thunk {list} r_y)
     ＝⟨ ap length' (equivalent-lrec-lemma _ (y ∷ xs) nil last-step eager) ⟩
       length' (list-rec ((y ∷ xs) ∷E (strip-thunk-env env)) (y ∷ xs) nil
               last-step)
     ＝⟨ ap length' (last-list-correctness-any-env (y ∷ xs)) ⟩
       length' (last-list' (y ∷ xs))
     ＝⟨ last-list'-length-1 y xs ⟩
       1
     ∎

    γ₄ : recursive-call-time E_y r_y x ≤ 9 * length' (strip-thunk {list} r_y)
    γ₄ = fᵣ (strip-thunk {list} r_y) x (transport (1 ≤_) (γ₃ ⁻¹) (≤-refl 1))

    γ₅ : recursive-call-time E_y r_y x ≤ 9
    γ₅ = transport (λ z → recursive-call-time E_y r_y x ≤ 9 * z) γ₃ γ₄

    γ₆ : recursive-call-time E_y r_y x + succ (pr₁ r_y)
       ≤ 9 + (11 * length' (y ∷ xs))
    γ₆ = ≤-adding (recursive-call-time E_y r_y x) 9 (succ (pr₁ r_y))
          (11 * length' (y ∷ xs)) γ₅ γ₂

    γ₇ : succ (pr₁ (last-step-applied E_y r_y x)) ≤ 9 + (11 * length' (y ∷ xs))
    γ₇ = transport (_≤ 9 + (11 * length' (y ∷ xs))) (γ₁ ⁻¹) γ₆

    γ₈ : 9 + (11 * length' (y ∷ xs)) ≤ 11 + (11 * length' (y ∷ xs))
    γ₈ = ≤-n-monotone-right 9 11 (11 * length' (y ∷ xs)) ⋆

    γ₉ : succ (pr₁ (last-step-applied E_y r_y x))
       ≤ 11 + (11 * length' (y ∷ xs))
    γ₉ = ≤-trans (succ (pr₁ (last-step-applied E_y r_y x)))
          (9 + (11 * length' (y ∷ xs))) (11 + (11 * length' (y ∷ xs)))
          γ₇ γ₈

    γ₁₀ : succ (pr₁ (last-step-applied E_y r_y x))
        ＝ succ (pr₁ (last-step-applied E_x r_x x))
    γ₁₀
     = succ (pr₁ (last-step-applied E_y r_y x))
     ＝⟨ ap (λ z → succ (pr₁ z)) (eager-function-list-helper-env-lemma r_y x) ⟩
       succ (pr₁ (last-step-applied E_x r_y x))
     ＝⟨ ap (λ z → succ (pr₁ (last-step-applied E_x z x)))
          (last-list-same-env (y ∷ xs)) ⟩
       succ (pr₁ (last-step-applied E_x r_x x))
     ∎

    goal : succ (pr₁ (last-step-applied E_x r_x x))
         ≤ 11 + (11 * length' (y ∷ xs))
    goal = transport (_≤ 11 + (11 * length' (y ∷ xs))) γ₁₀ γ₉

  f' : Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
     , is-polytime 1 11 1 (length' l)
        (get-time (inr refl)
         (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type l)))
  f' [] env ()
  f' (x ∷ xs) env ⋆ = f x xs env

last-linear-time : {n : ℕ} {Γ : Ctx n} → is-program-linear-time last (inl refl)
last-linear-time {n} {Γ} = 15 , (1 , f)
 where
  f : Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
    , is-polytime 1 15 1 (length' l)
       (get-time (inl refl) (pr₁ (env [ last ]ᵢ eager) (thunk-type l)))
  f xs env le = γ₁₄
   where
    E : Envᵢ (list ∷ Γ)
    E = thunk-type {list} xs ∷Eᵢ env

    L : Σ t ꞉ ℕ , Thunk t (List ℕ)
    L = E [ last-list ]ᵢ eager

    ht : ℕ
    ht = pr₁ (pr₁ (E [ head ]ᵢ eager) L)

    hct : ℕ
    hct = head-comp-time E (strip-thunk {list} L)

    fₗ : (xs : List ℕ)
       → is-polytime 1 11 1 (length' xs)
          (pr₁ (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type xs)))
    fₗ xs = pr₂ (pr₂ (last-list-linear-time {n} {Γ})) xs env

    fₕ : (l : List ℕ)
       → is-polytime 1 3 1 (length' l)
          (get-time (inl refl) (pr₁ (E [ head ]ᵢ eager) (thunk-type l)))
    fₕ ys le
     = pr₂ (pr₂ (eager-head-linear-time')) ys ((0 , return xs) ∷Eᵢ env) le

    γ₁ : succ ht ＝ hct + succ (pr₁ L)
    γ₁ = ap succ
          (adding-times-lemma (inr refl) (inl refl) E head-comp L ⁻¹)

    γ₂ : succ (pr₁ L) ≤ succ (11 * length' xs)
    γ₂ = fₗ xs le

    γ₃ : length' (strip-thunk {list} L) ＝ 1
    γ₃
     = length' (strip-thunk {list} L)
     ＝⟨ ap length' (equivalent-semantics E last-list eager) ⟩
       length' ((xs ∷E (strip-thunk-env env)) [ last-list ]ₑ)
     ＝⟨ ap length' (last-list-correctness-any-env xs) ⟩
       length' (last-list' xs)
     ＝⟨ last-list'-length-1' xs le ⟩
       1
     ∎

    γ₄ : hct ≤ 3 * length' (strip-thunk {list} L)
    γ₄ = fₕ (strip-thunk {list} L) (transport (1 ≤_) (γ₃ ⁻¹) (≤-refl 1))

    γ₅ : hct ≤ 3
    γ₅ = transport (λ z → hct ≤ 3 * z) γ₃ γ₄

    γ₆ : hct + succ (pr₁ L) ≤ 3 + (succ (11 * length' xs))
    γ₆ = ≤-adding hct 3 (succ (pr₁ L)) (succ (11 * length' xs)) γ₅ γ₂

    γ₇ : 3 + (succ (11 * length' xs)) ＝ 4 + 11 * length' xs
    γ₇ = succ-left 3 (11 * length' xs) ⁻¹

    γ₈ : 4 + 11 * length' xs ≤ 4 * length' xs + 11 * length' xs
    γ₈ = ≤-n-monotone-right 4 (4 * length' xs) (11 * length' xs)
          (multiplication-preserves-order-left 4 1 (length' xs) le)

    γ₉ : 4 * length' xs + 11 * length' xs ＝ 15 * length' xs
    γ₉ = distributivity-mult-over-addition' 4 11 (length' xs) ⁻¹

    γ₁₀ : succ ht ≤ 3 + (succ (11 * length' xs))
    γ₁₀ = transport (_≤ 3 + (succ (11 * length' xs))) (γ₁ ⁻¹) γ₆

    γ₁₁ : succ ht ≤ 4 + 11 * length' xs
    γ₁₁ = transport (succ ht ≤_) γ₇ γ₁₀

    γ₁₂ : 4 + 11 * length' xs ≤ 15 * length' xs
    γ₁₂ = transport (4 + 11 * length' xs ≤_) γ₉ γ₈

    γ₁₃ : succ ht ≤ 15 * length' xs
    γ₁₃ = ≤-trans (succ ht) (4 + 11 * length' xs) (15 * length' xs) γ₁₁ γ₁₂

    γ₁₄ : ht ≤ 15 * length' xs
    γ₁₄ = ≤-trans ht (succ ht) (15 * length' xs) (≤-succ ht) γ₁₃

last-linear-time' : {n : ℕ} {Γ : Ctx n} (env : Envᵢ Γ)
                  → (list-time-function-naive env (inl refl) last eager)
                    ∈O[ (λ n → n) ]
last-linear-time' {n} {Γ}
 = is-polytime-to-polybig-o {_} {n} {Γ} (inl refl)
    last-comp 1 (last-linear-time {n} {Γ})

\end{code}
