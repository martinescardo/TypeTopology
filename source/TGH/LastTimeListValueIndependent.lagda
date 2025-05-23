Theo Hepburn, started in February 2025

A proof that the value output of the last program
does not depend on the time component of the input.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy


module TGH.LastTimeListValueIndependent (fe : naive-funext 𝓤₀ 𝓤₀) where

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
open import TGH.NatOrder
open import TGH.Language fe
open import TGH.HeadExample fe
open import TGH.LastCorrectness fe
open import TGH.ComplexityDefinitionsResults fe

head-comp : {n : ℕ} {Γ : Ctx n} → Term (list ∷ Γ) nat
head-comp = lrec (var 𝟎) zero (lam nat (lam nat (var 𝟎)))

thunk-if-lemma' : {τ : LType} → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
               → (x : Σ t ꞉ ℕ , Thunk t ℕ)
               → (y : ⟦ τ ⟧ᵢ)
               → (z : ⟦ τ ⟧ᵢ)
               → get-time nat-or-list (thunk-if x y z)
               ＝ succ ((if' (strip-thunk x) then' get-time nat-or-list
                  y else' get-time nat-or-list z) + pr₁ x)
thunk-if-lemma' (inl refl) (zero , return zero) y z = refl
thunk-if-lemma' (inl refl) (zero , return (succ x)) y z = refl
thunk-if-lemma' (inl refl) (succ pr₃ , (√ x)) y z
 = ap succ (thunk-if-lemma' (inl refl) (pr₃ , x) y z)
thunk-if-lemma' (inr refl) (zero , return zero) y z = refl
thunk-if-lemma' (inr refl) (zero , return (succ x)) y z = refl
thunk-if-lemma' (inr refl) (succ pr₃ , (√ x)) y z
 = ap succ (thunk-if-lemma' (inr refl) (pr₃ , x) y z)

head-time-value-env-independent-eager : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                                → {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                                → pr₁ (env₁ [ head ]ᵢ eager)
                                ∼ pr₁ (env₂ [ head ]ᵢ eager)
head-time-value-env-independent-eager (zero , return x)
 = ap inc-nat (eager-head-env-lemma-II x)
head-time-value-env-independent-eager (succ pr₃ , (√ x))
 = ap inc-nat (head-time-value-env-independent-eager (pr₃ , x))


last-list-length-lemma : (xs ys : List ℕ) → (length xs ＝ length ys)
                       → length (last-list' xs) ＝ length (last-list' ys)
last-list-length-lemma [] [] eql = refl
last-list-length-lemma (x ∷ []) (y ∷ []) eql = refl
last-list-length-lemma (x ∷ x₁ ∷ xs) (y ∷ x₂ ∷ ys) eql
 = last-list-length-lemma (x₁ ∷ xs) (x₂ ∷ ys) (ap pred' eql)

last-comp-length-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                        → {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                        → (l₁ l₂ : List ℕ)
                        → (length l₁) ＝ (length l₂)
                        → length ((l₁ ∷E env₁) [ last-list ]ₑ)
                        ＝ length ((l₂ ∷E env₂) [ last-list ]ₑ)
last-comp-length-lemma xs ys eq
 = length ((xs ∷E _) [ last-list ]ₑ)
   ＝⟨ ap length (last-list-correctness-any-env xs) ⟩
   length (last-list' xs) ＝⟨ last-list-length-lemma xs ys eq ⟩
   length (last-list' ys) ＝⟨ ap length (last-list-correctness-any-env ys) ⁻¹ ⟩
   length ((ys ∷E _) [ last-list ]ₑ) ∎

recursive-call : {n : ℕ} {Γ : Ctx n} → Term (nat ∷ list ∷ Γ) list
recursive-call = if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)

nat-helper-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                     → {env₁ : Envᵢ Γ₁}
                     → {env₂ : Envᵢ Γ₂}
                     → (l : Σ t ꞉ ℕ , Thunk t ℕ)
                     → (n : ℕ)
                     → pr₁ (eager-function-nat-helper env₁
                       (lam nat (suc (var 𝟏))) l) (thunk-type n)
                     ＝ pr₁ (eager-function-nat-helper env₂
                       (lam nat (suc (var 𝟏))) l) (thunk-type n)
nat-helper-env-lemma (zero , return x) n = refl
nat-helper-env-lemma (succ pr₃ , (√ x)) n
 = ap inc-nat (nat-helper-env-lemma (pr₃ , x) n)

length'-comp-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                         → {env₁ : Envᵢ Γ₁}
                         → {env₂ : Envᵢ Γ₂}
                         → (l : List ℕ)
                         → list-recᵢ env₁ l zero
                           (lam nat (lam nat (suc (var 𝟏)))) eager
                           ＝
                           list-recᵢ env₂ l zero
                           (lam nat (lam nat (suc (var 𝟏)))) eager
length'-comp-same-env [] = refl
length'-comp-same-env {_} {_} {_} {_} {env₁} {env₂} (x ∷ l)
 = pr₁
      (eager-function-nat-helper env₁ (lam nat (suc (var 𝟏)))
       (list-recᵢ env₁ l zero (lam nat (lam nat (suc (var 𝟏))))
        eager))
      (0 , return x) ＝⟨ ap (λ z → pr₁
      (eager-function-nat-helper env₁ (lam nat (suc (var 𝟏)))
       z) (0 , return x)) (length'-comp-same-env l) ⟩
    pr₁
      (eager-function-nat-helper env₁ (lam nat (suc (var 𝟏)))
       (list-recᵢ env₂ l zero (lam nat (lam nat (suc (var 𝟏))))
        eager))
      (0 , return x) ＝⟨ nat-helper-env-lemma ((list-recᵢ env₂
      l zero (lam nat (lam nat (suc (var 𝟏)))) eager)) x ⟩
    pr₁
      (eager-function-nat-helper env₂ (lam nat (suc (var 𝟏)))
       (list-recᵢ env₂ l zero (lam nat (lam nat (suc (var 𝟏))))
        eager))
      (0 , return x) ∎

length'-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                         → {env₁ : Envᵢ Γ₁}
                         → {env₂ : Envᵢ Γ₂}
                         → (l : Σ t ꞉ ℕ , Thunk t (List ℕ))
                         → pr₁ (pr₁ (env₁ [ length' ]ᵢ eager) l)
                         ＝ pr₁ (pr₁ (env₂ [ length' ]ᵢ eager) l)
length'-same-env (zero , return l) = ap (succ ∘ pr₁) (length'-comp-same-env l)
length'-same-env (succ pr₃ , (√ x)) = ap succ (length'-same-env (pr₃ , x))

recursive-call-comp-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                         → {env₁ : Envᵢ Γ₁}
                         → {env₂ : Envᵢ Γ₂}
                         → (l : (List ℕ))
                         → (x : ℕ)
                         → thunk-if {list} (pr₁ (env₁ [ length' ]ᵢ eager)
                         (thunk-type l)) ((3 , (√ (√ (√ return (x ∷ []))))))
                         ((1 , (√ return l)))
                         ＝ thunk-if {list} (pr₁ (env₂ [ length' ]ᵢ eager)
                         (thunk-type l)) ((3 , (√ (√ (√ return (x ∷ []))))))
                         ((1 , (√ return l)))
recursive-call-comp-same-env l x
 = ap (λ z → inc-list (thunk-if {list} z (3 , (√ (√ (√ return (x ∷ [])))))
   (1 , (√ return l)))) (length'-comp-same-env l)

recursive-call-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                        → {env₁ : Envᵢ Γ₁}
                        → {env₂ : Envᵢ Γ₂}
                        → (l : List ℕ)
                        → (n : ℕ)
                        → (pr₁ (pr₁ (env₁ [ lam list (lam nat recursive-call)]ᵢ
                          eager) (thunk-type l)) (thunk-type n))
                       ＝ (pr₁ (pr₁ (env₂ [ lam list (lam nat recursive-call)]ᵢ
                          eager) (thunk-type l)) (thunk-type n))
recursive-call-same-env {_} {_} {_} {_} {env₁} {env₂} l n
 = ap inc-list ((recursive-call-comp-same-env l n))

eager-function-list-helper-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                         → {env₁ : Envᵢ Γ₁}
                         → {env₂ : Envᵢ Γ₂}
                         → (l : (Σ t ꞉ ℕ , Thunk t (List ℕ)))
                         → (n : ℕ)
                         → (pr₁ (eager-function-list-helper env₁ (lam nat
                          (if
                          lam list
                          (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
                          ∙ var 𝟏
                          then cons (var 𝟎) nil else var 𝟏)) l) (thunk-type n))
                         ＝ (pr₁ (eager-function-list-helper env₂ (lam nat
                           (if
                           lam list
                           (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
                           ∙ var 𝟏
                           then cons (var 𝟎) nil else var 𝟏)) l) (thunk-type n))
eager-function-list-helper-env-lemma (zero , return l) n
 = recursive-call-same-env l n
eager-function-list-helper-env-lemma (succ pr₃ , (√ x)) n
 = ap inc-list (eager-function-list-helper-env-lemma (pr₃ , x) n)

last-list-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                    → {env₁ : Envᵢ Γ₁}
                    → {env₂ : Envᵢ Γ₂}
                    → (l : List ℕ)
                    → list-recᵢ env₁ l nil (lam list (lam nat recursive-call))
                      eager
                    ＝ list-recᵢ env₂ l nil (lam list (lam nat recursive-call))
                      eager
last-list-same-env [] = refl
last-list-same-env {_} {_} {_} {_} {env₁} {env₂} (x ∷ xs)
 = pr₁
      (eager-function-list-helper env₁
       (lam nat
        (if
         lam list
         (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
         ∙ var 𝟏
         then cons (var 𝟎) nil else var 𝟏))
       (list-recᵢ env₁ xs nil
        (lam list
         (lam nat
          (if
           lam list
           (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
           ∙ var 𝟏
           then cons (var 𝟎) nil else var 𝟏)))
        eager))
      (0 , return x) ＝⟨ ap (λ z → pr₁
      (eager-function-list-helper env₁
       (lam nat
        (if
         lam list
         (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
         ∙ var 𝟏
         then cons (var 𝟎) nil else var 𝟏)) z) (0 , return x))
         (last-list-same-env xs) ⟩
    pr₁
      (eager-function-list-helper env₁
       (lam nat
        (if
         lam list
         (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
         ∙ var 𝟏
         then cons (var 𝟎) nil else var 𝟏))
       (list-recᵢ env₂ xs nil
        (lam list
         (lam nat
          (if
           lam list
           (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
           ∙ var 𝟏
           then cons (var 𝟎) nil else var 𝟏)))
        eager))
      (0 , return x) ＝⟨ eager-function-list-helper-env-lemma
      (list-recᵢ env₂ xs nil
        (lam list
         (lam nat
          (if
           lam list
           (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
           ∙ var 𝟏
           then cons (var 𝟎) nil else var 𝟏)))
        eager) x ⟩
    pr₁
      (eager-function-list-helper env₂
       (lam nat
        (if
         lam list
         (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
         ∙ var 𝟏
         then cons (var 𝟎) nil else var 𝟏))
       (list-recᵢ env₂ xs nil
        (lam list
         (lam nat
          (if
           lam list
           (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
           ∙ var 𝟏
           then cons (var 𝟎) nil else var 𝟏)))
        eager))
      (0 , return x) ∎

length'-comp-lemma' : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                   → (y : Σ t ꞉ ℕ , Thunk t ℕ)
                   → (x₁ x₂ : ℕ)
                   → pr₁
      (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       y) (0 , return x₁)
                   ＝ pr₁
      (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       y) (0 , return x₂)
length'-comp-lemma' env (zero , return x) x₁ x₂ = refl
length'-comp-lemma' env (succ pr₃ , (√ x)) x₁ x₂
 = ap inc-nat (length'-comp-lemma' env (pr₃ , x) x₁ x₂)

length'-comp-lemma : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                   → (l₁ l₂ : List ℕ)
                   → (x₁ x₂ : ℕ)
                   → (length l₁ ＝ length l₂)
                   → (pr₁
                     (eager-function-nat-helper env
                     (lam nat (suc (var 𝟏)))
                     (list-recᵢ env l₁ zero
                     (lam nat (lam nat (suc (var 𝟏)))) eager))
                     (0 , return x₁))
                   ＝ (pr₁
                     (eager-function-nat-helper env
                     (lam nat (suc (var 𝟏)))
                     (list-recᵢ env l₂ zero
                     (lam nat (lam nat (suc (var 𝟏)))) eager))
                     (0 , return x₂))
length'-comp-lemma env [] [] x₁ x₂ eq = refl
length'-comp-lemma env (y₁ ∷ l₁) (y₂ ∷ l₂) x₁ x₂ eq
 = pr₁
      (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       (pr₁
        (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
         (list-recᵢ env l₁ zero (lam nat (lam nat (suc (var 𝟏))))
          eager))
        (0 , return y₁)))
      (0 , return x₁) ＝⟨ ap (λ z → pr₁
      (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       z)
      (0 , return x₁)) (length'-comp-lemma env l₁ l₂ y₁ y₂ (ap pred' eq)) ⟩
    pr₁
      (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       (pr₁
        (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
         (list-recᵢ env l₂ zero (lam nat (lam nat (suc (var 𝟏))))
          eager))
        (0 , return y₂)))
      (0 , return x₁) ＝⟨ length'-comp-lemma' env (pr₁
        (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
         (list-recᵢ env l₂ zero (lam nat (lam nat (suc (var 𝟏))))
          eager))
        (0 , return y₂)) x₁ x₂ ⟩
     pr₁
      (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
       (pr₁
        (eager-function-nat-helper env (lam nat (suc (var 𝟏)))
         (list-recᵢ env l₂ zero (lam nat (lam nat (suc (var 𝟏))))
          eager))
        (0 , return y₂)))
      (0 , return x₂) ∎

length'-list-value-independent : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                               → time-independent-of-list-values env
                                 (inl refl) eager length'
length'-list-value-independent env [] [] eq = refl
length'-list-value-independent env (x₁ ∷ l₁) (x₂ ∷ l₂) eq
 = succ
      (pr₁
       (pr₁
        (eager-function-nat-helper ((0 , return (x₁ ∷ l₁)) ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (list-recᵢ ((0 , return (x₁ ∷ l₁)) ∷Eᵢ env) l₁ zero
          (lam nat (lam nat (suc (var 𝟏)))) eager))
        (0 , return x₁)))
        ＝⟨ ap (succ ∘ pr₁) (length'-comp-same-env (x₁ ∷ l₁)) ⟩
    succ
      (pr₁
       (pr₁
        (eager-function-nat-helper env
         (lam nat (suc (var 𝟏)))
         (list-recᵢ env l₁ zero
          (lam nat (lam nat (suc (var 𝟏)))) eager))
        (0 , return x₁))) ＝⟨ ap (succ ∘ pr₁)
        (length'-comp-lemma env l₁ l₂ x₁ x₂ (ap pred' eq)) ⟩
    succ
      (pr₁
       (pr₁
        (eager-function-nat-helper env
         (lam nat (suc (var 𝟏)))
         (list-recᵢ env l₂ zero
          (lam nat (lam nat (suc (var 𝟏)))) eager))
        (0 , return x₂)))
        ＝⟨ ap (succ ∘ pr₁) (length'-comp-same-env (x₂ ∷ l₂)) ⁻¹ ⟩
    succ
      (pr₁
       (pr₁
        (eager-function-nat-helper ((0 , return (x₂ ∷ l₂)) ∷Eᵢ env)
         (lam nat (suc (var 𝟏)))
         (list-recᵢ ((0 , return (x₂ ∷ l₂)) ∷Eᵢ env) l₂ zero
          (lam nat (lam nat (suc (var 𝟏)))) eager))
        (0 , return x₂))) ∎

list-rec-length-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                     → {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                     → (l₁ l₂ : List ℕ)
                     → (length l₁ ＝ length l₂)
                     → list-rec env₁ l₁ zero (lam nat (lam nat (suc (var 𝟏))))
                     ＝ list-rec env₂ l₂ zero (lam nat (lam nat (suc (var 𝟏))))
list-rec-length-lemma [] [] eq = refl
list-rec-length-lemma (x ∷ l₁) (x₁ ∷ l₂) eq
 = ap succ (list-rec-length-lemma l₁ l₂ (ap pred' eq))

if-condition-lemma : {n : ℕ} {Γ : Ctx n} (env : Envᵢ Γ)
                   → (l₁ l₂ : List ℕ)
                   → (n₁ n₂ : ℕ)
                   → (length l₁ ＝ length l₂)
                   →
                   if' strip-thunk (list-recᵢ
                   ((0 , return l₁) ∷Eᵢ (0 , return n₁)
                   ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
                   l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
                   then' 3
                   else' 1
                   ＝
                   if' strip-thunk (list-recᵢ
                   ((0 , return l₂) ∷Eᵢ (0 , return n₂)
                   ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
                   l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
                   then' 3
                   else' 1
if-condition-lemma env l₁ l₂ n₁ n₂ eq
 = if' strip-thunk (list-recᵢ
    ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
    l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
    then' 3
    else' 1 ＝⟨ ap (λ z → if' z then' 3 else' 1)
    (equivalent-lrec-lemma _ l₁ zero _ eager) ⟩
    (if' list-rec (l₁ ∷E n₁ ∷E l₁ ∷E (strip-thunk-env env))
           l₁ zero (lam nat (lam nat (suc (var 𝟏))))
    then' 3
    else' 1) ＝⟨ ap (λ z → if' z then' 3 else' 1)
    (list-rec-length-lemma l₁ l₂ eq) ⟩
    ((if' list-rec (l₂ ∷E n₂ ∷E l₂ ∷E (strip-thunk-env env))
           l₂ zero (lam nat (lam nat (suc (var 𝟏))))
    then' 3
    else' 1)) ＝⟨ ap (λ z → if' z then' 3 else' 1)
    (equivalent-lrec-lemma _ l₂ zero _ eager) ⁻¹ ⟩
    if' strip-thunk (list-recᵢ
    ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
    l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
    then' 3
    else' 1 ∎

recursive-call-list-value-independent : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                                      → time-independent-of-list-values-n env
                                        (inr refl) eager
                                        (lam list (lam nat recursive-call))
recursive-call-list-value-independent env l₁ l₂ eq n₁ n₂
 = succ
      (succ
       (pr₁
        (thunk-if {list}
         (pr₁
          (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
          ,
          pr₂
          (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager))
         (3 , (√ (√ (√ return (n₁ ∷ []))))) (1 , (√ return l₁)))))
         ＝⟨ ap (succ ∘ succ)
         (thunk-if-lemma' (inr refl) (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           (3 , (√ (√ (√ return (n₁ ∷ []))))) (1 , (√ return l₁))) ⟩
     succ (succ (succ ((if' strip-thunk (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           then' 3
           else' 1)
     +
     (pr₁
          (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)))))
           ＝⟨ ap (λ z → succ (succ (succ ((if' strip-thunk (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           then' 3
           else' 1)
     +
     z)))) (ap pred' (length'-list-value-independent ((0 , return n₁)
     ∷Eᵢ (0 , return l₁) ∷Eᵢ env) l₁ l₂ eq)) ⟩
     succ (succ (succ ((if' strip-thunk (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           then' 3
           else' 1)
     +
     (pr₁
          (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)))))
           ＝⟨ ap (λ z → succ (succ (succ ((if' strip-thunk (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           then' 3
           else' 1)
     +
     z)))) (ap pr₁ (length'-comp-same-env l₂)) ⟩
     succ (succ (succ ((if' strip-thunk (list-recᵢ
           ((0 , return l₁) ∷Eᵢ (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env)
           l₁ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           then' 3
           else' 1)
     +
     (pr₁
          (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)))))
           ＝⟨ ap (λ z → succ (succ (succ (z
     +
     (pr₁
          (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager))))))
           (if-condition-lemma env l₁ l₂ n₁ n₂ eq) ⟩
     succ (succ (succ ((if' strip-thunk (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           then' 3
           else' 1)
     +
     (pr₁
          (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)))))
           ＝⟨ ap (succ ∘ succ)
         (thunk-if-lemma' (inr refl) (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
           (3 , (√ (√ (√ return (n₂ ∷ []))))) (1 , (√ return l₂))) ⁻¹ ⟩
     succ
      (succ
       (pr₁
        (thunk-if {list}
         (pr₁
          (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager)
          ,
          pr₂
          (list-recᵢ
           ((0 , return l₂) ∷Eᵢ (0 , return n₂) ∷Eᵢ (0 , return l₂) ∷Eᵢ env)
           l₂ zero (lam nat (lam nat (suc (var 𝟏)))) eager))
         (3 , (√ (√ (√ return (n₂ ∷ []))))) (1 , (√ return l₂))))) ∎

recursive-call-length-lemma : {n : ℕ} {Γ : Ctx n}
                            → (env : Envᵢ Γ)
                            → (x₁ x₂ : ℕ) → (l₁ l₂ : List ℕ)
                            → (length l₁ ＝ length l₂)
                            → length
                              (force
                              (pr₂
                              (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
                              (thunk-type (x₁ ∷ l₁)) env) l₁ nil
                              (lam list
                              (lam nat
                              (if
                              lam list
                              (lrec (var 𝟎) zero (lam nat (lam nat
                              (suc (var 𝟏)))))
                              ∙ var 𝟏
                              then cons (var 𝟎) nil else var 𝟏)))
                              eager)))
                              ＝
                              length
                              (force
                              (pr₂
                              (list-recᵢ (_∷Eᵢ_ {_} {_} {list}
                              (thunk-type (x₂ ∷ l₂)) env) l₂ nil
                              (lam list
                              (lam nat
                              (if
                              lam list
                              (lrec (var 𝟎) zero (lam nat
                              (lam nat (suc (var 𝟏)))))
                              ∙ var 𝟏
                              then cons (var 𝟎) nil else var 𝟏)))
                              eager)))
recursive-call-length-lemma env x₁ x₂ l₁ l₂ eq
 = length
    (force
     (pr₂
      (list-recᵢ (thunk-type (x₁ ∷ l₁) ∷Eᵢ env) l₁ nil
       (lam list
        (lam nat
         (if
          lam list
          (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
          ∙ var 𝟏
          then cons (var 𝟎) nil else var 𝟏)))
       eager))) ＝⟨ ap length (equivalent-lrec-lemma
       ((0 , return (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil _ eager) ⟩
    length (list-rec ((x₁ ∷ l₁) ∷E (strip-thunk-env env)) l₁ nil (lam list
        (lam nat
         (if
          lam list
          (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
          ∙ var 𝟏
          then cons (var 𝟎) nil else var 𝟏))))
          ＝⟨ ap length (last-list-correctness-any-env l₁) ⟩
    length (last-list' l₁) ＝⟨ last-list-length-lemma l₁ l₂ eq ⟩
    length (last-list' l₂) ＝⟨ ap length (last-list-correctness-any-env l₂) ⁻¹ ⟩
    length (list-rec ((x₂ ∷ l₂) ∷E (strip-thunk-env env)) l₂ nil (lam list
        (lam nat
         (if
          lam list
          (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
          ∙ var 𝟏
          then cons (var 𝟎) nil else var 𝟏)))) ＝⟨ ap length
          (equivalent-lrec-lemma ((0 , return
          (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil _ eager) ⁻¹ ⟩
    length
     (force
      (pr₂
       (list-recᵢ (thunk-type (x₂ ∷ l₂) ∷Eᵢ env) l₂ nil
        (lam list
         (lam nat
          (if
           lam list
           (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))
           ∙ var 𝟏
           then cons (var 𝟎) nil else var 𝟏)))
        eager))) ∎

last-list-list-value-independent : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                                 → time-independent-of-list-values env
                                   (inr refl) eager (lam list last-list)
last-list-list-value-independent env [] [] eq = refl
last-list-list-value-independent env (x₁ ∷ l₁) (x₂ ∷ l₂) eq
 = pr₁
    (pr₁ (env [ lam list last-list ]ᵢ eager) (thunk-type (x₁ ∷ l₁))) ＝⟨ refl ⟩
    succ (pr₁ (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) (x₁ ∷ l₁) nil (lam list
    (lam nat recursive-call)) eager)) ＝⟨ refl ⟩
    succ (pr₁ ((pr₁ ((pr₁ (((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) [ lam list (lam nat
    recursive-call) ]ᵢ eager)) (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil
    (lam list (lam nat recursive-call)) eager))) (0 , return x₁))) ＝⟨ ap succ
    ((adding-times-lemma-l-n-l (_∷Eᵢ_ {_} {_} {list} (thunk-type (x₁ ∷ l₁)) env)
    recursive-call (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil (lam list
    (lam nat recursive-call)) eager) (0 , return x₁))) ⁻¹ ⟩
    succ (pr₁ (((0 , return x₁) ∷Eᵢ (thunk-type {list} (strip-thunk {list}
    (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil (lam list (lam nat
    recursive-call)) eager))) ∷Eᵢ (thunk-type (x₁ ∷ l₁)) ∷Eᵢ env)
    [ recursive-call ]ᵢ eager) + pr₁ (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env)
    l₁ nil (lam list (lam nat recursive-call)) eager)) ＝⟨ ap (λ z → succ (pr₁
    (((0 , return x₁) ∷Eᵢ (thunk-type {list} (strip-thunk {list} (list-recᵢ
    ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil (lam list (lam nat recursive-call))
    eager))) ∷Eᵢ (thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) [ recursive-call ]ᵢ eager)
    + pr₁ z)) (last-list-same-env l₁) ⟩
    succ (pr₁ (((0 , return x₁) ∷Eᵢ (thunk-type {list} (strip-thunk (list-recᵢ
    ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil (lam list (lam nat recursive-call))
    eager))) ∷Eᵢ (thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) [ recursive-call ]ᵢ eager) +
    pr₁ (list-recᵢ ((0 , return l₁) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list} (thunk-type
    (x₂ ∷ l₂)) env)) l₁ nil (lam list (lam nat recursive-call)) eager))
    ＝⟨ ap (λ z → succ (pr₁ (((0 , return x₁) ∷Eᵢ (thunk-type {list}
    (strip-thunk (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil (lam list
    (lam nat recursive-call)) eager))) ∷Eᵢ (thunk-type (x₁ ∷ l₁)) ∷Eᵢ env)
    [ recursive-call ]ᵢ eager) + z)) (ap pred' (last-list-list-value-independent
    ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₁ l₂ (ap pred' eq))) ⟩
    succ (pr₁ (((0 , return x₁) ∷Eᵢ (thunk-type {list} (strip-thunk (list-recᵢ
    ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil (lam list (lam nat recursive-call))
    eager))) ∷Eᵢ (thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) [ recursive-call ]ᵢ eager) +
    pr₁ (list-recᵢ ((0 , return l₂) ∷Eᵢ (thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil
    (lam list (lam nat recursive-call)) eager)) ＝⟨ ap (λ z → succ (z + pr₁
    (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (0 , return l₂) (_∷Eᵢ_ {_} {_} {list}
    (thunk-type (x₂ ∷ l₂)) env)) l₂ nil (lam list (lam nat recursive-call))
    eager))) (recursive-call-list-value-independent ((thunk-type (x₁ ∷ l₁))
    ∷Eᵢ env) (strip-thunk (list-recᵢ ((thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil
    (lam list (lam nat recursive-call)) eager)) (strip-thunk (list-recᵢ
    ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil (lam list (lam nat recursive-call))
    eager)) (recursive-call-length-lemma env x₁ x₂ l₁ l₂ (ap pred' eq)) x₁ x₂)
    ⟩
    succ (pr₁ (((0 , return x₂) ∷Eᵢ (thunk-type {list} (strip-thunk (list-recᵢ
    ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil (lam list (lam nat recursive-call))
    eager))) ∷Eᵢ (thunk-type (x₁ ∷ l₁)) ∷Eᵢ env) [ recursive-call ]ᵢ eager)
    + pr₁ (list-recᵢ ((0 , return l₂) ∷Eᵢ (thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂
    nil (lam list (lam nat recursive-call)) eager)) ＝⟨ ap (λ z → succ ((pr₁ z)
    + pr₁ (list-recᵢ (_∷Eᵢ_ {_} {_} {list} (0 , return l₂) (_∷Eᵢ_ {_} {_} {list}
    (thunk-type (x₂ ∷ l₂)) env)) l₂ nil (lam list (lam nat recursive-call))
    eager))) (recursive-call-same-env ((strip-thunk (list-recᵢ ((thunk-type
    (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil (lam list (lam nat recursive-call)) eager))) x₂)
    ⟩
    succ (pr₁ (((0 , return x₂) ∷Eᵢ (thunk-type {list} (strip-thunk (list-recᵢ
    ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil (lam list (lam nat recursive-call))
    eager))) ∷Eᵢ (thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) [ recursive-call ]ᵢ eager)
    + pr₁ (list-recᵢ ((0 , return l₂) ∷Eᵢ (thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂
    nil (lam list (lam nat recursive-call)) eager))
    ＝⟨ ap (λ z → succ (pr₁ (((0 , return x₂) ∷Eᵢ (thunk-type {list}
    (strip-thunk {list} (list-recᵢ ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil
    (lam list (lam nat recursive-call)) eager))) ∷Eᵢ (thunk-type (x₂ ∷ l₂))
    ∷Eᵢ env) [ recursive-call ]ᵢ eager) + pr₁ z)) (last-list-same-env l₂) ⁻¹ ⟩
    succ (pr₁ (((0 , return x₂) ∷Eᵢ (thunk-type {list} (strip-thunk (list-recᵢ
    ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil (lam list (lam nat recursive-call))
    eager))) ∷Eᵢ (thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) [ recursive-call ]ᵢ eager) +
    pr₁ (list-recᵢ ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil (lam list (lam nat
    recursive-call)) eager))
    ＝⟨ ap succ ((adding-times-lemma-l-n-l (_∷Eᵢ_ {_} {_} {list} (thunk-type
    (x₂ ∷ l₂)) env) recursive-call (list-recᵢ ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env)
    l₂ nil (lam list (lam nat recursive-call)) eager) (0 , return x₂))) ⟩
    succ (pr₁ ((pr₁ ((pr₁ (((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) [ lam list (lam nat
    recursive-call) ]ᵢ eager)) (list-recᵢ ((thunk-type (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil
    (lam list (lam nat recursive-call)) eager))) (0 , return x₂))) ∎



last-list-value-independent : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                            → time-independent-of-list-values env
                              (inl refl) eager last
last-list-value-independent env l₁ l₂ eq
 = pr₁ ((thunk-type l₁ ∷Eᵢ env) [ head ∙ last-list ]ᵢ eager) ＝⟨ refl ⟩
    (pr₁ ((pr₁ ((thunk-type l₁ ∷Eᵢ env) [ head ]ᵢ eager))
    ((thunk-type l₁ ∷Eᵢ env) [ last-list ]ᵢ eager)))
    ＝⟨ adding-times-lemma (inr refl) (inl refl) (thunk-type l₁ ∷Eᵢ env)
    head-comp (((thunk-type l₁ ∷Eᵢ env) [ last-list ]ᵢ eager)) ⁻¹ ⟩
    (pr₁ (((thunk-type (strip-thunk {list} (((thunk-type l₁) ∷Eᵢ env)
    [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type l₁) ∷Eᵢ env) [ head-comp ]ᵢ eager)
    + pr₁ (((thunk-type l₁) ∷Eᵢ env) [ last-list ]ᵢ eager))
    ＝⟨ ap (λ z → pr₁ (((thunk-type z) ∷Eᵢ (thunk-type l₁) ∷Eᵢ env)
    [ head-comp ]ᵢ eager) + pr₁ (((thunk-type l₁) ∷Eᵢ env) [ last-list ]ᵢ eager)
    ) (equivalent-semantics (thunk-type l₁ ∷Eᵢ env) last-list eager) ⟩
    pr₁ (((thunk-type ((l₁ ∷E (strip-thunk-env env)) [ last-list ]ₑ)) ∷Eᵢ
    (0 , return l₁) ∷Eᵢ env) [ head-comp ]ᵢ eager) + pr₁ (((thunk-type l₁) ∷Eᵢ
    env) [ last-list ]ᵢ eager) ＝⟨ refl ⟩
    pr₁ ((pr₁ (((0 , return l₁) ∷Eᵢ env) [ head ]ᵢ eager)) (thunk-type ((l₁
    ∷E (strip-thunk-env env)) [ last-list ]ₑ))) + pr₁ (((thunk-type l₁) ∷Eᵢ
    env) [ last-list ]ᵢ eager) ＝⟨ ap (λ z → pr₁ z + pr₁ (((thunk-type l₁)
    ∷Eᵢ env) [ last-list ]ᵢ eager)) (head-time-value-env-independent-eager
    ((thunk-type ((l₁ ∷E (strip-thunk-env env)) [ last-list ]ₑ)))) ⟩
    pr₁ ((((thunk-type ((l₁ ∷E (strip-thunk-env env)) [ last-list ]ₑ))) ∷Eᵢ
    (_∷Eᵢ_ {_} {_} {list} (thunk-type l₂) env)) [ head-comp ]ᵢ eager) + pr₁
    (((thunk-type l₁) ∷Eᵢ env) [ last-list ]ᵢ eager) ＝⟨ ap (_+ pr₁
    (((thunk-type l₁) ∷Eᵢ env) [ last-list ]ᵢ eager))
    (head-list-value-independent-eager ((thunk-type l₂) ∷Eᵢ env)
    ((l₁ ∷E (strip-thunk-env env)) [ last-list ]ₑ) ((l₂
    ∷E (strip-thunk-env env)) [ last-list ]ₑ) (last-comp-length-lemma l₁
    l₂ eq)) ⟩
    pr₁ ((((thunk-type ((l₂ ∷E (strip-thunk-env env)) [ last-list ]ₑ)))
    ∷Eᵢ (thunk-type l₂) ∷Eᵢ env) [ head-comp ]ᵢ eager) + pr₁ (((thunk-type l₁)
    ∷Eᵢ env) [ last-list ]ᵢ eager) ＝⟨ ap (pr₁ ((((thunk-type ((l₂ ∷E(
    strip-thunk-env env)) [ last-list ]ₑ))) ∷Eᵢ (_∷Eᵢ_ {_} {_} {list}
    (thunk-type l₂) env)) [ head-comp ]ᵢ eager) +_)
    (last-list-list-value-independent env l₁ l₂ eq) ⟩
    pr₁ ((((thunk-type ((l₂ ∷E (strip-thunk-env env)) [ last-list ]ₑ)))
    ∷Eᵢ (thunk-type l₂) ∷Eᵢ env) [ head-comp ]ᵢ eager) + pr₁ (((thunk-type l₂)
    ∷Eᵢ env) [ last-list ]ᵢ eager) ＝⟨ ap (λ z → pr₁ z + pr₁ (((thunk-type l₂)
    ∷Eᵢ env) [ last-list ]ᵢ eager)) (head-time-value-env-independent-eager
    ((thunk-type ((l₂ ∷E (strip-thunk-env env)) [ last-list ]ₑ)))) ⁻¹ ⟩
    pr₁ ((pr₁ (((0 , return l₂) ∷Eᵢ env) [ head ]ᵢ eager)) (thunk-type ((l₂
    ∷E (strip-thunk-env env)) [ last-list ]ₑ))) + pr₁ (((thunk-type l₂) ∷Eᵢ env)
    [ last-list ]ᵢ eager) ＝⟨ ap (λ z → pr₁ (((thunk-type z) ∷Eᵢ (thunk-type l₂)
    ∷Eᵢ env) [ head-comp ]ᵢ eager) + pr₁ (((thunk-type l₂) ∷Eᵢ env)
    [ last-list ]ᵢ eager)) (equivalent-semantics (thunk-type l₂ ∷Eᵢ env)
    last-list eager) ⁻¹ ⟩
    (pr₁ (((thunk-type (strip-thunk {list} (((thunk-type l₂) ∷Eᵢ env)
    [ last-list ]ᵢ eager))) ∷Eᵢ (thunk-type l₂) ∷Eᵢ env) [ head-comp ]ᵢ eager)
    + pr₁ (((thunk-type l₂) ∷Eᵢ env) [ last-list ]ᵢ eager))
    ＝⟨ adding-times-lemma (inr refl) (inl refl) (thunk-type l₂ ∷Eᵢ env)
    head-comp (((thunk-type l₂ ∷Eᵢ env) [ last-list ]ᵢ eager)) ⟩
    pr₁ ((thunk-type l₂ ∷Eᵢ env) [ head ∙ last-list ]ᵢ eager) ∎

\end{code}
