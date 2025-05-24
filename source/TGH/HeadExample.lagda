Theo Hepburn, started January 2025.

Contains an implementation of the head
function in our language. We prove that head
is constant time when using a lazy evaluation
strategy but linear time, and not constant time,
when using an eager evaluation strategy.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.HeadExample (fe : naive-funext 𝓤₀ 𝓤₀) where

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
open import TGH.Language fe
open import TGH.ComplexityDefinitionsResults fe

nat-id : Closed (nat ⇒ nat)
nat-id = lam nat (var 𝟎)

nat-id-eager-lazy-equal : (pr₁ ([] [ nat-id ]ᵢ lazy))
                        ∼ (pr₁ ([] [ nat-id ]ᵢ eager))
nat-id-eager-lazy-equal (zero , return x) = refl
nat-id-eager-lazy-equal (succ _ , (√ x))
 = ap inc-nat (nat-id-eager-lazy-equal (_ , x))

list-id : Closed (list ⇒ list)
list-id = lam list (var 𝟎)

list-id-eager-lazy-equal : (pr₁ ([] [ list-id ]ᵢ lazy))
                         ∼ (pr₁ ([] [ list-id ]ᵢ eager))
list-id-eager-lazy-equal (zero , return x) = refl
list-id-eager-lazy-equal (succ _ , (√ x))
 = ap inc-list (list-id-eager-lazy-equal (_ , x))

head : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ nat)
head = lam list (lrec (var 𝟎) zero (lam nat (lam nat (var 𝟎))))

list-head : List ℕ → ℕ
list-head [] = zero
list-head (x ∷ _) = x

head-correctness : {n : ℕ} {Γ : Ctx n} {env : Env Γ} → (l : List ℕ)
                 → (env [ head ]ₑ) l ＝ list-head l
head-correctness [] = refl
head-correctness (_ ∷ _) = refl


head-time-value-env-independent-lazy : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                                → {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                                → pr₁ (env₁ [ head ]ᵢ lazy)
                                ∼ pr₁ (env₂ [ head ]ᵢ lazy)
head-time-value-env-independent-lazy (zero , return []) = refl
head-time-value-env-independent-lazy (zero , return (x ∷ x₁)) = refl
head-time-value-env-independent-lazy {_} {_} {_} {_} {env₁} {env₂}
 (succ pr₃ , (√ x))
 = (inc-nat ∘ inc-nat) (list-rec-builder ((succ pr₃ , (√ x)) ∷Eᵢ env₁) (pr₃ , x)
   zero
   (lam nat (lam nat (var 𝟎))) lazy) ＝⟨ ap (inc-nat ∘ inc-nat) (γ (pr₃ , x)) ⟩
   (inc-nat ∘ inc-nat ) (list-rec-builder ((pr₃ , x) ∷Eᵢ env₁) (pr₃ , x) zero
     (lam nat (lam nat (var 𝟎))) lazy)
     ＝⟨ ap inc-nat (head-time-value-env-independent-lazy (pr₃ , x)) ⟩
    (inc-nat ∘ inc-nat ) (list-rec-builder ((pr₃ , x) ∷Eᵢ env₂) (pr₃ , x) zero
      (lam nat (lam nat (var 𝟎))) lazy)
      ＝⟨ ap (inc-nat ∘ inc-nat) (γ (pr₃ , x))⁻¹ ⟩
    (inc-nat ∘ inc-nat )
    (list-rec-builder ((succ pr₃ , (√ x)) ∷Eᵢ env₂) (pr₃ , x) zero
      (lam nat (lam nat (var 𝟎))) lazy) ∎
 where
  γ : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
    → {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
    → (l : Σ t ꞉ ℕ , Thunk t (List ℕ))
    → (list-rec-builder env₁ l zero
      (lam nat (lam nat (var 𝟎))) lazy)
    ＝ (list-rec-builder env₂ l zero
      (lam nat (lam nat (var 𝟎))) lazy)
  γ (zero , return []) = refl
  γ (zero , return (_ ∷ _)) = refl
  γ ((succ pr₃ , (√ x))) = ap inc-nat (γ (pr₃ , x))


head-list-value-independent-lazy : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                                  → time-independent-of-list-values env
                                    (inl refl) lazy head
head-list-value-independent-lazy env [] [] _ = refl
head-list-value-independent-lazy env (_ ∷ _) (_ ∷ _) _ = refl

lazy-head-constant-time : {n : ℕ} {Γ : Ctx n}
                        → (env : Envᵢ Γ)
                        → (list-time-function-naive env
                          (inl refl) head lazy)
                          ∈O[ (λ n → 1) ]
lazy-head-constant-time env = big-o (2 , (1 , γ))
 where
  γ : (x : ℕ) →
      1 ≤ x →
      pr₁ ((pr₁ (env [ head ]ᵢ lazy)) (thunk-type (gen-naive-list x)))
      ≤ 2
  γ (succ x) _ = ⋆

eager-head-env-lemma-I : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {x : ℕ}
                         {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                       → (n : Σ t ꞉ ℕ , Thunk t ℕ)
                       → pr₁ ((eager-function-nat-helper env₁
                         (lam nat (var 𝟎))) n) (0 , return x)
                       ＝ pr₁ ((eager-function-nat-helper env₂
                       (lam nat (var 𝟎))) n) (0 , return x)
eager-head-env-lemma-I (zero , return x) = refl
eager-head-env-lemma-I (succ _ , (√ x))
 = ap inc-nat (eager-head-env-lemma-I (_ , x))

eager-head-env-lemma-II : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                         {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂} → (l : List ℕ)
                        → (list-recᵢ env₁ l zero
                          (lam nat (lam nat (var 𝟎))) eager)
                        ＝ (list-recᵢ env₂ l zero
                           (lam nat (lam nat (var 𝟎))) eager)
eager-head-env-lemma-II [] = refl
eager-head-env-lemma-II {_} {_} {_} {_} {env₁} {env₂} (x ∷ l)
 = pr₁ (eager-function-nat-helper env₁ (lam nat (var 𝟎))
       (list-recᵢ env₁ l zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return x) ＝⟨ ap (λ z → pr₁ (eager-function-nat-helper env₁
      (lam nat (var 𝟎)) z) (0 , return x)) (eager-head-env-lemma-II l) ⟩
    pr₁
      (eager-function-nat-helper env₁ (lam nat (var 𝟎))
       (list-recᵢ env₂ l zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return x) ＝⟨ eager-head-env-lemma-I (list-recᵢ env₂ l zero
      (lam nat (lam nat (var 𝟎))) eager) ⟩
    pr₁
      (eager-function-nat-helper env₂ (lam nat (var 𝟎))
       (list-recᵢ env₂ l zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return x) ∎

head-list-value-independent-eager : {n : ℕ} {Γ : Ctx n}
                                  → (env : Envᵢ Γ)
                                  → time-independent-of-list-values
                                    env (inl refl) eager head
head-list-value-independent-eager env [] [] eq = refl
head-list-value-independent-eager env (x ∷ l₁) (x₁ ∷ l₂) eq
 = pr₁ (call-intermediate-l env head eager (x ∷ l₁)) ＝⟨ ap (succ ∘ pr₁)
   (eager-head-env-lemma-II (x ∷ l₁))  ⟩
   succ
    (pr₁
     (list-recᵢ (_ ∷Eᵢ env) (x ∷ l₁) zero (lam nat (lam nat (var 𝟎)))
      eager)) ＝⟨ ap succ (γ₀ (list-recᵢ (thunk-type {list} l₁ ∷Eᵢ env) l₁ zero
         (lam nat (lam nat (var 𝟎))) eager) (list-recᵢ
         (thunk-type {list} l₂ ∷Eᵢ env) l₂ zero
         (lam nat (lam nat (var 𝟎))) eager) x x₁ (γ l₁ l₂ (ap pred' eq)))  ⟩
   succ
    (pr₁
     (pr₁
      (eager-function-nat-helper (_ ∷Eᵢ env) (lam nat (var 𝟎))
       (list-recᵢ (_ ∷Eᵢ env) l₂ zero (lam nat (lam nat (var 𝟎)))
        eager))
      (0 , return x₁))) ＝⟨ (ap (succ ∘ pr₁)
      (eager-head-env-lemma-II (x₁ ∷ l₂)))⁻¹ ⟩
   succ
    (pr₁
     (list-recᵢ ((0 , return (x₁ ∷ l₂)) ∷Eᵢ env) (x₁ ∷ l₂) zero
      (lam nat (lam nat (var 𝟎))) eager)) ∎
 where
  IH : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
     → (l₁ l₂ : List ℕ) → (eq : length l₁ ＝ length l₂)
     → pr₁ (eager-function-list-helper env (lrec (var 𝟎) zero
       (lam nat (lam nat (var 𝟎)))) (thunk-type l₁))
     ＝ pr₁ (eager-function-list-helper env (lrec (var 𝟎) zero
       (lam nat (lam nat (var 𝟎)))) (thunk-type l₂))
  IH env l₁ l₂ eq = head-list-value-independent-eager env l₁ l₂ eq

  γ₀ : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
       {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
     → (z₁ z₂ : Σ t ꞉ ℕ , Thunk t ℕ)
     → (m₁ m₂ : ℕ)
     → pr₁ z₁ ＝ pr₁ z₂
     → pr₁ (pr₁ (eager-function-nat-helper env₁ (lam nat (var 𝟎)) z₁)
       (0 , return m₁))
       ＝ pr₁ (pr₁ (eager-function-nat-helper env₂ (lam nat (var 𝟎)) z₂)
       (0 , return m₂))
  γ₀ (zero , return x) (zero , return x₁) m₁ m₂ eq = refl
  γ₀ (succ n , (√ x)) (succ m , (√ x₁)) m₁ m₂ eq
    = ap succ (γ₀ (_ , x) (_ , x₁) m₁ m₂ (ap pred' eq))

  γ : (l₁ l₂ : List ℕ) → length l₁ ＝ length l₂
    → (pr₁
      (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (0 , return l₁) env) l₁
        zero (lam nat (lam nat (var 𝟎))) eager))
    ＝ (pr₁
      (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (0 , return l₂) env) l₂
        zero (lam nat (lam nat (var 𝟎))) eager))
  γ [] [] eq = refl
  γ (x₁ ∷ l₁) (x₂ ∷ l₂) eq = ap pred' (IH env (x₁ ∷ l₁) (x₂ ∷ l₂) eq)

nat-function-lemma : {n : ℕ} {Γ : Ctx n}
                     {env : Envᵢ Γ}
                   → (x : Σ t ꞉ ℕ , Thunk t ℕ)
                   → pr₁ (pr₁ (eager-function-nat-helper env
                     (lam nat (var 𝟎)) x) (0 , return 0))
                     ＝ succ (pr₁ x)
nat-function-lemma (zero , return x) = refl
nat-function-lemma (succ _ , (√ x))
 = ap succ (nat-function-lemma (_ , x))


eager-head-not-constant-time-lemma : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                                   → (m : ℕ)
                                   → ¬ (pr₁ (eager-function-list-helper env
                                     (lrec (var 𝟎) zero
                                     (lam nat (lam nat (var 𝟎))))
             (thunk-type (gen-naive-list (succ m)))) ≤ (succ m))
eager-head-not-constant-time-lemma env (succ m) ineq
 = IH' ((γ₂ (list-recᵢ
       ((0 , return (0 ∷ 0 ∷ gen-naive-list m)) ∷Eᵢ env)
       (0 ∷ gen-naive-list m) zero
       (lam nat (lam nat (var 𝟎))) eager) ineq))
 where
  IH : ¬ ((pr₁ (list-recᵢ
         ((0 , return (0 ∷ gen-naive-list m))
         ∷Eᵢ env)
         (0 ∷ gen-naive-list m) zero
         (lam nat (lam nat (var 𝟎))) eager)) ≤ m)
  IH = eager-head-not-constant-time-lemma env m

  IH' : ¬ ((pr₁ (list-recᵢ
          ((0 , return (0 ∷ 0 ∷ gen-naive-list m))
           ∷Eᵢ env)
          (0 ∷ gen-naive-list m) zero
          (lam nat (lam nat (var 𝟎))) eager))
         ≤ m)
  IH' = transport (λ z → ¬ ((pr₁ z) ≤ m))
        (eager-head-env-lemma-II (0 ∷ gen-naive-list m))  IH

  γ₁ : (x : Σ t ꞉ ℕ , Thunk t ℕ)
     → pr₁
       (pr₁ (eager-function-nat-helper ((0 , return
         (0 ∷ 0 ∷ gen-naive-list m)) ∷Eᵢ env) (lam nat (var 𝟎)) x)
            (0 , return 0))
     ＝ succ (pr₁ x)
  γ₁ x = nat-function-lemma x

  γ₂ : (x : Σ t ꞉ ℕ , Thunk t ℕ)
       → pr₁
          (pr₁ (eager-function-nat-helper _ (lam nat (var 𝟎)) x)
           (0 , return 0))
          ≤ succ m
       → (pr₁ x ≤ m)
  γ₂ x le
   = succ-order-injective (pr₁ x) m ((transport (λ z → z ≤ succ m) (γ₁ x) le))

eager-head-not-constant-time : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                             →  ¬ ((list-time-function-naive env (inl refl)
                                head eager)
                          ∈O[ (λ n → 1) ])
eager-head-not-constant-time env (big-o (C , N₀ , f)) = γ (≤-decidable N₀ C)
 where
  γ : N₀ ≤ C ∔ ¬ (N₀ ≤ C) → 𝟘
  γ (inl ineq) = eager-head-not-constant-time-lemma env C (≤-trans (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list C)) ∷Eᵢ env) (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list C)) ∷Eᵢ env)
        (gen-naive-list C) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0))) (succ (pr₁
      (pr₁
      (eager-function-nat-helper
        ((0 , return (0 ∷ gen-naive-list C)) ∷Eᵢ env) (lam nat (var 𝟎))
        (list-recᵢ ((0 , return (0 ∷ gen-naive-list C)) ∷Eᵢ env)
        (gen-naive-list C) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))) C (≤-succ (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list C)) ∷Eᵢ env) (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list C)) ∷Eᵢ env)
        (gen-naive-list C) zero (lam nat (lam nat (var 𝟎))) eager))
    (0 , return 0)))) (f (succ C) (≤-trans N₀ C (succ C) ineq (≤-succ C))))
             
  γ (inr ineq) = eager-head-not-constant-time-lemma env N₀ (≤-trans (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
      (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))
      (succ (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
      (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))) N₀ (≤-succ (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
      (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))) (≤-trans (succ
    (pr₁
      (pr₁
      (eager-function-nat-helper
        ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (lam nat (var 𝟎))
        (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))) (succ C) N₀ (≤-trans (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
      (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0))) (succ (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
      (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))) C (≤-succ (pr₁
    (pr₁
      (eager-function-nat-helper
      ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
      (lam nat (var 𝟎))
      (list-recᵢ ((0 , return (0 ∷ gen-naive-list N₀)) ∷Eᵢ env)
        (gen-naive-list N₀) zero (lam nat (lam nat (var 𝟎))) eager))
      (0 , return 0)))) (f (succ N₀) (≤-succ N₀))) γ₁))
   where
    γ₁ : succ C ≤ N₀
    γ₁ = not-less-or-equal-is-bigger N₀ C ineq


eager-head-linear-time-big-o : {n : ℕ} {Γ : Ctx n}
                            → Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , ((N : ℕ)
                            → (N₀ ≤ N) → (env : Envᵢ Γ)
                            → (list-time-function-naive env
                              (inl refl) head eager) N ≤ C * N)
eager-head-linear-time-big-o {_} {Γ} = 3 , 1 , γ
 where
  γ₀ : (x : ℕ)
     → (env : Envᵢ Γ)
     → pr₁ (eager-function-list-helper env (lrec (var 𝟎) zero
       (lam nat (lam nat (var 𝟎))))
       (0 , return (0 ∷ gen-naive-list x)))  ≤ 3 + 3 * x
  γ₀ zero _ = ⋆
  γ₀ (succ n) env = γ₉
   where
    γ₁ : (n : ℕ) → pr₁ (eager-function-list-helper env
         (lrec (var 𝟎) zero (lam nat (lam nat (var 𝟎))))
         (0 , return (0 ∷ gen-naive-list n))) ≤ 3 + 3 * n
    γ₁ n = γ₀ n env

    γ₂ : succ
         (pr₁
         (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (0 ,
         return (0 ∷ 0 ∷ gen-naive-list n)) env)
         (0 ∷ gen-naive-list n) zero
         (lam nat (lam nat (var 𝟎))) eager))
         ≤ (3 + 3 * n)
    γ₂ = transport (λ z → succ (pr₁ z) ≤ 3 + 3 * n)
         (eager-head-env-lemma-II (0 ∷ gen-naive-list n)) (γ₁ n)

    γ₃ : 3 + 3 * n ＝ succ (2 + 3 * n)
    γ₃ = 2 + 1 + 3 * n ＝⟨ +-assoc 2 1 (3 * n) ⟩
         2 + (1 + 3 * n) ＝⟨ ap (2 +_) (+-comm 1 (3 * n)) ⟩
         2 + (3 * n + 1) ＝⟨ (+-assoc 2 (3 * n) 1)⁻¹ ⟩
         (2 + 3 * n) + 1 ∎

    γ₄ : succ
         (pr₁
         (pr₁
         (eager-function-nat-helper (_ ∷Eᵢ env) (lam nat (var 𝟎))
         (list-recᵢ (_ ∷Eᵢ env) (gen-naive-list n) zero
         (lam nat (lam nat (var 𝟎))) eager))
         (0 , return 0)))
         ≤ succ (2 + 3 * n)
    γ₄ = transport (λ z → (succ (pr₁ (pr₁ (eager-function-nat-helper
         (_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
           (lam nat (var 𝟎))
           (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
           (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
           (gen-naive-list n) zero
           (lam nat (lam nat (var 𝟎))) eager)) (0 , return 0)))) ≤ z) γ₃ γ₂

    γ₅ : (pr₁
         (pr₁
           (eager-function-nat-helper (_ ∷Eᵢ env) (lam nat (var 𝟎))
             (list-recᵢ (_ ∷Eᵢ env) (gen-naive-list n) zero
               (lam nat (lam nat (var 𝟎))) eager))
               (0 , return 0))) ≤
             (2 + 3 * n)
    γ₅ = succ-order-injective (pr₁ (pr₁ (eager-function-nat-helper
         (_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
         (lam nat (var 𝟎))
           (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
           (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
           (gen-naive-list n) zero
         (lam nat (lam nat (var 𝟎))) eager)) (0 , return 0))) (2 + 3 * n) γ₄

    γ₆ : (x : Σ t ꞉ ℕ , Thunk t ℕ)
       → pr₁ (pr₁ (eager-function-nat-helper (_∷Eᵢ_ {_} {_} {list}
         (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env) (lam nat (var 𝟎)) x)
         (0 , return 0)) ＝ succ (pr₁ x)
    γ₆ x = nat-function-lemma x

    γ₇ : (x : Σ t ꞉ ℕ , Thunk t ℕ) → (pr₁ x ≤ 2 + 3 * n)
       → pr₁ ((pr₁ (eager-function-nat-helper (_∷Eᵢ_ {_} {_} {list}
         (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
         (lam nat (var 𝟎)) x)) (0 , return 0)) ≤ succ (2 + 3 * n)
    γ₇ x le = transport (λ z → z ≤ succ (2 + 3 * n)) ((γ₆ x)⁻¹)
              (succ-monotone (pr₁ x) (2 + 3 * n) le)

    nums₁ : succ (succ (2 + 3 * n)) ＝ succ (3 + 3 * n)
    nums₁ = (2 + 3 * n) + 1 + 1 ＝⟨ refl ⟩
            (2 + 3 * n + 1) + 1 ＝⟨ ap (_+ 1) (+-assoc 2 (3 * n) 1) ⟩
            (2 + ((3 * n) + 1)) + 1
            ＝⟨ ap (λ z → (2 + z) + 1) (+-comm (3 * n) 1) ⟩
            (2 + (1 + (3 * n))) + 1 ＝⟨ ap (_+ 1) ((+-assoc 2 1 (3 * n))⁻¹) ⟩
            (3 + 3 * n) + 1 ＝⟨ refl ⟩
            succ (3 + 3 * n) ∎

    nums₂ : (3 + (3 + 3 * n)) ＝ (3 + 3 * n) + 3
    nums₂ = +-comm 3 (3 + 3 * n)

    ineq : (3 + 3 * n) + 1 ≤ (3 + 3 * n) + 3
    ineq = ≤-adding (3 + 3 * n) (3 + 3 * n) 1 3 (≤-refl (3 + 3 * n)) ⋆

    γ₈ : (x : Σ t ꞉ ℕ , Thunk t ℕ) → (pr₁ x ≤ 2 + 3 * n)
       → succ (pr₁ ((pr₁ (eager-function-nat-helper (_∷Eᵢ_ {_} {_} {list}
         (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
         (lam nat (var 𝟎)) x)) (0 , return 0))) ≤ 3 + (3 + 3 * n)
    γ₈ x le = ≤-trans (succ (pr₁ ((pr₁ (eager-function-nat-helper
              (_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
             (lam nat (var 𝟎)) x)) (0 , return 0)))) ((2 + 3 * n) + 2)
             (3 + (3 + 3 * n))
             (succ-monotone (pr₁ ((pr₁ (eager-function-nat-helper
             (_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
             (lam nat (var 𝟎)) x)) (0 , return 0)))
             (succ (2 + 3 * n)) (γ₇ x le))
             (transport₂ _≤_ ((nums₁)⁻¹) ((nums₂)⁻¹) ineq)

    γ₉ : pr₁ (eager-function-list-helper env
         (lrec (var 𝟎) zero (lam nat (lam nat (var 𝟎))))
           (0 , return (0 ∷ 0 ∷ gen-naive-list n))) ≤ (3 + (3 + 3 * n))
    γ₉ = γ₈ (pr₁
         (eager-function-nat-helper
         (_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
         (lam nat (var 𝟎))
         (list-recᵢ
           (_∷Eᵢ_ {_} {_} {list} (0 , return (0 ∷ 0 ∷ gen-naive-list n)) env)
           (gen-naive-list n) zero
           (lam nat (lam nat (var 𝟎))) eager))
         (0 , return 0)) γ₅

  γ : (x : ℕ) → (1 ≤ x) → (env : Envᵢ Γ)
    → pr₁ (eager-function-list-helper env (lrec (var 𝟎) zero
      (lam nat (lam nat (var 𝟎))))
      (thunk-type (gen-naive-list x))) ≤ 3 * x
  γ (succ x) le env = γ₀ x env

eager-head-linear-time : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                       → (list-time-function-naive env
                         (inl refl) head eager) ∈O[ (λ n → n) ]
eager-head-linear-time env
 = big-o (3 , (1 , (λ n le → pr₂ (pr₂ eager-head-linear-time-big-o) n le env)))

eager-head-linear-time' : {n : ℕ} {Γ : Ctx n}
                        → is-linear-time {_} {n} {Γ} head (inl refl)
eager-head-linear-time'
 = 3 , (1 , λ xs env le → transport (_≤ 3 * length xs)
   (head-list-value-independent-eager env (gen-naive-list (length xs)) xs
   (naive-list-length-lemma (length xs) ⁻¹))
   (pr₂ (pr₂ (eager-head-linear-time-big-o)) (length xs) le env))

\end{code}
