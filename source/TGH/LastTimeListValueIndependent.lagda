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
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec) hiding (head)
open import MLTT.Fin
open import MLTT.List
open import UF.Base
open import TGH.Thunk
open import TGH.Language fe
open import TGH.HeadExample fe
open import TGH.LastCorrectness fe
open import TGH.ComplexityDefinitionsResults fe

head-comp : {n : ℕ} {Γ : Ctx n} → Term (list ∷ Γ) nat
head-comp = lrec (var 𝟎) zero (lam nat (lam nat (var 𝟎)))

thunk-if-lemma' : {τ : LType}
                → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                → (x@(t , _) : Σ t ꞉ ℕ , Thunk t ℕ)
                → (y : ⟦ τ ⟧ᵢ)
                → (z : ⟦ τ ⟧ᵢ)
                → get-time nat-or-list (thunk-if x y z)
                ＝ succ ((if' (strip-thunk x) then' get-time nat-or-list y
                   else' get-time nat-or-list z) + t)
thunk-if-lemma' (inl refl) (zero , return zero) y z = refl
thunk-if-lemma' (inl refl) (zero , return (succ x)) y z = refl
thunk-if-lemma' (inl refl) (succ pr₃ , (√ x)) y z
 = ap succ (thunk-if-lemma' (inl refl) (pr₃ , x) y z)
thunk-if-lemma' (inr refl) (zero , return zero) y z = refl
thunk-if-lemma' (inr refl) (zero , return (succ x)) y z = refl
thunk-if-lemma' (inr refl) (succ pr₃ , (√ x)) y z
 = ap succ (thunk-if-lemma' (inr refl) (pr₃ , x) y z)

head-time-value-env-independent-eager
 : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
   {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
 → pr₁ (env₁ [ head ]ᵢ eager)
 ∼ pr₁ (env₂ [ head ]ᵢ eager)
head-time-value-env-independent-eager (zero , return x)
 = ap inc-nat (eager-head-env-lemma-II x)
head-time-value-env-independent-eager (succ pr₃ , (√ x))
 = ap inc-nat (head-time-value-env-independent-eager (pr₃ , x))

last-list-length-lemma : (xs ys : List ℕ)
                       → (length xs ＝ length ys)
                       → length (last-list' xs) ＝ length (last-list' ys)
last-list-length-lemma [] [] eql = refl
last-list-length-lemma [] (y ∷ ys) ()
last-list-length-lemma (x ∷ []) [] ()
last-list-length-lemma (x ∷ []) (y ∷ []) eql = refl
last-list-length-lemma (x ∷ []) (y ∷ x₂ ∷ ys) ()
last-list-length-lemma (x ∷ x₁ ∷ xs) [] ()
last-list-length-lemma (x ∷ x₁ ∷ xs) (y ∷ []) ()
last-list-length-lemma (x ∷ x₁ ∷ xs) (y ∷ x₂ ∷ ys) eql
 = last-list-length-lemma (x₁ ∷ xs) (x₂ ∷ ys) (ap pred' eql)

last-comp-length-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                         {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                       → (l₁ l₂ : List ℕ)
                       → (length l₁) ＝ (length l₂)
                       → length ((l₁ ∷E env₁) [ last-list ]ₑ)
                       ＝ length ((l₂ ∷E env₂) [ last-list ]ₑ)
last-comp-length-lemma xs ys eq
 = length ((xs ∷E _) [ last-list ]ₑ)
 ＝⟨ ap length (last-list-correctness-any-env xs) ⟩
   length (last-list' xs)
 ＝⟨ last-list-length-lemma xs ys eq ⟩
   length (last-list' ys)
 ＝⟨ ap length (last-list-correctness-any-env ys) ⁻¹ ⟩
   length ((ys ∷E _) [ last-list ]ₑ)
 ∎

recursive-call : {n : ℕ} {Γ : Ctx n} → Term (nat ∷ list ∷ Γ) list
recursive-call = if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)

\end{code}

The following definitions name terms that occur many times in the proofs
below.

* `length'-step-applied env l y` is the result of applying the step
  function of `length'` to the result `l` of the recursive call, and the
  list element `y`, under the eager strategy.
* `last-step-applied env l x` is the same for the step function of
  `last-list`.
* `cons-branch x` and `else-branch l` are the two branches of the
  conditional in `recursive-call`, as thunks.
* `cond-time b` is the time taken by the conditional once its condition
  `b` has been evaluated.
* `length-call-env l x env` is the environment in which `length'` is
  called inside `recursive-call`.
* `recursive-call-time env r x` is the time taken by `recursive-call`, when
  `r` is the result of the recursive call and `x` is the list element.
* `head-comp-time env L` is the time taken by `head-comp` on the list `L`.

\begin{code}

length'-step-applied : {n : ℕ} {Γ : Ctx n}
                     → Envᵢ Γ
                     → Σ t ꞉ ℕ , Thunk t ℕ
                     → ℕ
                     → Σ t ꞉ ℕ , Thunk t ℕ
length'-step-applied env l y
 = pr₁ (eager-function-nat-helper env (lam nat (suc (var 𝟏))) l) (0 , return y)

last-step-applied : {n : ℕ} {Γ : Ctx n}
                  → Envᵢ Γ
                  → Σ t ꞉ ℕ , Thunk t (List ℕ)
                  → ℕ
                  → Σ t ꞉ ℕ , Thunk t (List ℕ)
last-step-applied env l x
 = pr₁ (eager-function-list-helper env (lam nat recursive-call) l)
    (0 , return x)

cons-branch : ℕ → Σ t ꞉ ℕ , Thunk t (List ℕ)
cons-branch x = 3 , (√ (√ (√ return (x ∷ []))))

else-branch : List ℕ → Σ t ꞉ ℕ , Thunk t (List ℕ)
else-branch l = 1 , (√ return l)

cond-time : ℕ → ℕ
cond-time b = if' b then' 3 else' 1

length-call-env : {n : ℕ} {Γ : Ctx n}
                → List ℕ
                → ℕ
                → Envᵢ Γ
                → Envᵢ (list ∷ nat ∷ list ∷ Γ)
length-call-env l x env
 = (0 , return l) ∷Eᵢ (0 , return x) ∷Eᵢ (0 , return l) ∷Eᵢ env

recursive-call-time : {n : ℕ} {Γ : Ctx n}
                    → Envᵢ Γ
                    → Σ t ꞉ ℕ , Thunk t (List ℕ)
                    → ℕ
                    → ℕ
recursive-call-time env r x
 = pr₁ (((0 , return x) ∷Eᵢ thunk-type {list} (strip-thunk {list} r) ∷Eᵢ env)
    [ recursive-call ]ᵢ eager)

head-comp-time : {n : ℕ} {Γ : Ctx n} → Envᵢ Γ → List ℕ → ℕ
head-comp-time env L = pr₁ ((thunk-type {list} L ∷Eᵢ env) [ head-comp ]ᵢ eager)

nat-helper-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                       {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                     → (l : Σ t ꞉ ℕ , Thunk t ℕ)
                     → (n : ℕ)
                     → length'-step-applied env₁ l n
                     ＝ length'-step-applied env₂ l n
nat-helper-env-lemma (zero , return x) n = refl
nat-helper-env-lemma (succ pr₃ , (√ x)) n
 = ap inc-nat (nat-helper-env-lemma (pr₃ , x) n)

length'-comp-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                        {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                      → (l : List ℕ)
                      → list-recᵢ env₁ l zero length'-step eager
                      ＝ list-recᵢ env₂ l zero length'-step eager
length'-comp-same-env [] = refl
length'-comp-same-env {_} {_} {_} {_} {env₁} {env₂} (x ∷ l)
 = length'-step-applied env₁ (list-recᵢ env₁ l zero length'-step eager) x
 ＝⟨ ap (λ z → length'-step-applied env₁ z x) (length'-comp-same-env l) ⟩
   length'-step-applied env₁ (list-recᵢ env₂ l zero length'-step eager) x
 ＝⟨ nat-helper-env-lemma (list-recᵢ env₂ l zero length'-step eager) x ⟩
   length'-step-applied env₂ (list-recᵢ env₂ l zero length'-step eager) x
 ∎

length'-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                 → (l : Σ t ꞉ ℕ , Thunk t (List ℕ))
                 → pr₁ (pr₁ (env₁ [ length' ]ᵢ eager) l)
                 ＝ pr₁ (pr₁ (env₂ [ length' ]ᵢ eager) l)
length'-same-env (zero , return l) = ap (succ ∘ pr₁) (length'-comp-same-env l)
length'-same-env (succ pr₃ , (√ x)) = ap succ (length'-same-env (pr₃ , x))

recursive-call-comp-same-env
 : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
   {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
 → (l : List ℕ)
 → (x : ℕ)
 → thunk-if {list} (pr₁ (env₁ [ length' ]ᵢ eager) (thunk-type l))
    (cons-branch x) (else-branch l)
 ＝ thunk-if {list} (pr₁ (env₂ [ length' ]ᵢ eager) (thunk-type l))
    (cons-branch x) (else-branch l)
recursive-call-comp-same-env l x
 = ap (λ z → inc-list (thunk-if {list} z (cons-branch x) (else-branch l)))
    (length'-comp-same-env l)

recursive-call-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                          {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                        → (l : List ℕ)
                        → (n : ℕ)
                        → pr₁ (pr₁ (env₁ [ lam list (lam nat recursive-call) ]ᵢ
                           eager) (thunk-type l)) (thunk-type n)
                        ＝ pr₁ (pr₁ (env₂ [ lam list (lam nat recursive-call) ]ᵢ
                           eager) (thunk-type l)) (thunk-type n)
recursive-call-same-env l n = ap inc-list (recursive-call-comp-same-env l n)

eager-function-list-helper-env-lemma
 : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
   {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
 → (l : Σ t ꞉ ℕ , Thunk t (List ℕ))
 → (n : ℕ)
 → last-step-applied env₁ l n ＝ last-step-applied env₂ l n
eager-function-list-helper-env-lemma (zero , return l) n
 = recursive-call-same-env l n
eager-function-list-helper-env-lemma (succ pr₃ , (√ x)) n
 = ap inc-list (eager-function-list-helper-env-lemma (pr₃ , x) n)

last-list-same-env : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                     {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                   → (l : List ℕ)
                   → list-recᵢ env₁ l nil last-step eager
                   ＝ list-recᵢ env₂ l nil last-step eager
last-list-same-env [] = refl
last-list-same-env {_} {_} {_} {_} {env₁} {env₂} (x ∷ xs)
 = last-step-applied env₁ (list-recᵢ env₁ xs nil last-step eager) x
 ＝⟨ ap (λ z → last-step-applied env₁ z x) (last-list-same-env xs) ⟩
   last-step-applied env₁ (list-recᵢ env₂ xs nil last-step eager) x
 ＝⟨ eager-function-list-helper-env-lemma
      (list-recᵢ env₂ xs nil last-step eager) x ⟩
   last-step-applied env₂ (list-recᵢ env₂ xs nil last-step eager) x
 ∎

length'-comp-lemma' : {n : ℕ} {Γ : Ctx n}
                    → (env : Envᵢ Γ)
                    → (y : Σ t ꞉ ℕ , Thunk t ℕ)
                    → (x₁ x₂ : ℕ)
                    → length'-step-applied env y x₁
                    ＝ length'-step-applied env y x₂
length'-comp-lemma' env (zero , return x) x₁ x₂ = refl
length'-comp-lemma' env (succ pr₃ , (√ x)) x₁ x₂
 = ap inc-nat (length'-comp-lemma' env (pr₃ , x) x₁ x₂)

length'-comp-lemma : {n : ℕ} {Γ : Ctx n}
                   → (env : Envᵢ Γ)
                   → (l₁ l₂ : List ℕ)
                   → (x₁ x₂ : ℕ)
                   → (length l₁ ＝ length l₂)
                   → length'-step-applied env
                      (list-recᵢ env l₁ zero length'-step eager) x₁
                   ＝ length'-step-applied env
                      (list-recᵢ env l₂ zero length'-step eager) x₂
length'-comp-lemma env [] [] x₁ x₂ eq = refl
length'-comp-lemma env [] (y₂ ∷ l₂) x₁ x₂ ()
length'-comp-lemma env (y₁ ∷ l₁) [] x₁ x₂ ()
length'-comp-lemma env (y₁ ∷ l₁) (y₂ ∷ l₂) x₁ x₂ eq
 = length'-step-applied env (length'-step-applied env r₁ y₁) x₁
 ＝⟨ ap (λ z → length'-step-applied env z x₁)
      (length'-comp-lemma env l₁ l₂ y₁ y₂ (ap pred' eq)) ⟩
   length'-step-applied env (length'-step-applied env r₂ y₂) x₁
 ＝⟨ length'-comp-lemma' env (length'-step-applied env r₂ y₂) x₁ x₂ ⟩
   length'-step-applied env (length'-step-applied env r₂ y₂) x₂
 ∎
 where
  r₁ = list-recᵢ env l₁ zero length'-step eager
  r₂ = list-recᵢ env l₂ zero length'-step eager

length'-list-value-independent : {n : ℕ} {Γ : Ctx n}
                               → (env : Envᵢ Γ)
                               → time-independent-of-list-values env
                                  (inl refl) eager length'
length'-list-value-independent env [] [] eq = refl
length'-list-value-independent env [] (x₂ ∷ l₂) ()
length'-list-value-independent env (x₁ ∷ l₁) [] ()
length'-list-value-independent env (x₁ ∷ l₁) (x₂ ∷ l₂) eq
 = succ (pr₁ (length'-step-applied env₁ (list-recᵢ env₁ l₁ zero length'-step
                                         eager) x₁))
 ＝⟨ ap (succ ∘ pr₁) (length'-comp-same-env (x₁ ∷ l₁)) ⟩
   succ (pr₁ (length'-step-applied env
              (list-recᵢ env l₁ zero length'-step eager) x₁))
 ＝⟨ ap (succ ∘ pr₁) (length'-comp-lemma env l₁ l₂ x₁ x₂ (ap pred' eq)) ⟩
   succ (pr₁ (length'-step-applied env
              (list-recᵢ env l₂ zero length'-step eager) x₂))
 ＝⟨ ap (succ ∘ pr₁) (length'-comp-same-env (x₂ ∷ l₂)) ⁻¹ ⟩
   succ (pr₁ (length'-step-applied env₂
              (list-recᵢ env₂ l₂ zero length'-step eager) x₂))
 ∎
 where
  env₁ = (0 , return (x₁ ∷ l₁)) ∷Eᵢ env
  env₂ = (0 , return (x₂ ∷ l₂)) ∷Eᵢ env

list-rec-length-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                        {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                      → (l₁ l₂ : List ℕ)
                      → (length l₁ ＝ length l₂)
                      → list-rec env₁ l₁ zero length'-step
                      ＝ list-rec env₂ l₂ zero length'-step
list-rec-length-lemma [] [] eq = refl
list-rec-length-lemma [] (x₁ ∷ l₂) ()
list-rec-length-lemma (x ∷ l₁) [] ()
list-rec-length-lemma (x ∷ l₁) (x₁ ∷ l₂) eq
 = ap succ (list-rec-length-lemma l₁ l₂ (ap pred' eq))

if-condition-lemma : {n : ℕ} {Γ : Ctx n}
                   → (env : Envᵢ Γ)
                   → (l₁ l₂ : List ℕ)
                   → (n₁ n₂ : ℕ)
                   → (length l₁ ＝ length l₂)
                   → cond-time (strip-thunk
                      (list-recᵢ (length-call-env l₁ n₁ env) l₁ zero
                       length'-step eager))
                   ＝ cond-time (strip-thunk
                      (list-recᵢ (length-call-env l₂ n₂ env) l₂ zero
                       length'-step eager))
if-condition-lemma env l₁ l₂ n₁ n₂ eq
 = cond-time (strip-thunk
    (list-recᵢ (length-call-env l₁ n₁ env) l₁ zero length'-step eager))
 ＝⟨ ap cond-time (equivalent-lrec-lemma _ l₁ zero _ eager) ⟩
   cond-time (list-rec (l₁ ∷E n₁ ∷E l₁ ∷E (strip-thunk-env env))
              l₁ zero length'-step)
 ＝⟨ ap cond-time (list-rec-length-lemma l₁ l₂ eq) ⟩
   cond-time (list-rec (l₂ ∷E n₂ ∷E l₂ ∷E (strip-thunk-env env))
              l₂ zero length'-step)
 ＝⟨ ap cond-time (equivalent-lrec-lemma _ l₂ zero _ eager) ⁻¹ ⟩
   cond-time (strip-thunk
    (list-recᵢ (length-call-env l₂ n₂ env) l₂ zero length'-step eager))
 ∎

recursive-call-list-value-independent
 : {n : ℕ} {Γ : Ctx n}
 → (env : Envᵢ Γ)
 → time-independent-of-list-values-n env (inr refl) eager
    (lam list (lam nat recursive-call))
recursive-call-list-value-independent {n} {Γ} env l₁ l₂ eq n₁ n₂
 = succ (succ (pr₁ (thunk-if {list} r₁ (cons-branch n₁) (else-branch l₁))))
 ＝⟨ ap (succ ∘ succ)
      (thunk-if-lemma' (inr refl) r₁ (cons-branch n₁) (else-branch l₁)) ⟩
   succ (succ (succ (cond-time (strip-thunk r₁) + pr₁ r₁)))
 ＝⟨ ap (λ z → succ (succ (succ (cond-time (strip-thunk r₁) + z))))
      (ap pred' (length'-list-value-independent env' l₁ l₂ eq)) ⟩
   succ (succ (succ (cond-time (strip-thunk r₁) + pr₁ r₂')))
 ＝⟨ ap (λ z → succ (succ (succ (cond-time (strip-thunk r₁) + z))))
      (ap pr₁ (length'-comp-same-env l₂)) ⟩
   succ (succ (succ (cond-time (strip-thunk r₁) + pr₁ r₂)))
 ＝⟨ ap (λ z → succ (succ (succ (z + pr₁ r₂))))
      (if-condition-lemma env l₁ l₂ n₁ n₂ eq) ⟩
   succ (succ (succ (cond-time (strip-thunk r₂) + pr₁ r₂)))
 ＝⟨ ap (succ ∘ succ)
      (thunk-if-lemma' (inr refl) r₂ (cons-branch n₂) (else-branch l₂)) ⁻¹ ⟩
   succ (succ (pr₁ (thunk-if {list} r₂ (cons-branch n₂) (else-branch l₂))))
 ∎
 where
  r₁ = list-recᵢ (length-call-env l₁ n₁ env) l₁ zero length'-step eager
  r₂ = list-recᵢ (length-call-env l₂ n₂ env) l₂ zero length'-step eager

  env' : Envᵢ (nat ∷ list ∷ Γ)
  env' = (0 , return n₁) ∷Eᵢ (0 , return l₁) ∷Eᵢ env

  env'' : Envᵢ (list ∷ nat ∷ list ∷ Γ)
  env'' = (0 , return l₂) ∷Eᵢ env'

  r₂' = list-recᵢ env'' l₂ zero length'-step eager

recursive-call-length-lemma
 : {n : ℕ} {Γ : Ctx n}
 → (env : Envᵢ Γ)
 → (x₁ x₂ : ℕ)
 → (l₁ l₂ : List ℕ)
 → (length l₁ ＝ length l₂)
 → length (force (pr₂ (list-recᵢ (thunk-type {list} (x₁ ∷ l₁) ∷Eᵢ env)
    l₁ nil last-step eager)))
 ＝ length (force (pr₂ (list-recᵢ (thunk-type {list} (x₂ ∷ l₂) ∷Eᵢ env)
    l₂ nil last-step eager)))
recursive-call-length-lemma env x₁ x₂ l₁ l₂ eq
 = length (force (pr₂ (list-recᵢ (thunk-type (x₁ ∷ l₁) ∷Eᵢ env)
    l₁ nil last-step eager)))
 ＝⟨ ap length (equivalent-lrec-lemma
      ((0 , return (x₁ ∷ l₁)) ∷Eᵢ env) l₁ nil _ eager) ⟩
   length (list-rec ((x₁ ∷ l₁) ∷E (strip-thunk-env env)) l₁ nil last-step)
 ＝⟨ ap length (last-list-correctness-any-env l₁) ⟩
   length (last-list' l₁)
 ＝⟨ last-list-length-lemma l₁ l₂ eq ⟩
   length (last-list' l₂)
 ＝⟨ ap length (last-list-correctness-any-env l₂) ⁻¹ ⟩
   length (list-rec ((x₂ ∷ l₂) ∷E (strip-thunk-env env)) l₂ nil last-step)
 ＝⟨ ap length (equivalent-lrec-lemma
      ((0 , return (x₂ ∷ l₂)) ∷Eᵢ env) l₂ nil _ eager) ⁻¹ ⟩
   length (force (pr₂ (list-recᵢ (thunk-type (x₂ ∷ l₂) ∷Eᵢ env)
    l₂ nil last-step eager)))
 ∎

last-list-list-value-independent : {n : ℕ} {Γ : Ctx n}
                                 → (env : Envᵢ Γ)
                                 → time-independent-of-list-values env
                                    (inr refl) eager (lam list last-list)
last-list-list-value-independent env [] [] eq = refl
last-list-list-value-independent env [] (x₂ ∷ l₂) ()
last-list-list-value-independent env (x₁ ∷ l₁) [] ()
last-list-list-value-independent {n} {Γ} env (x₁ ∷ l₁) (x₂ ∷ l₂) eq
 = succ (pr₁ (last-step-applied env₁ r₁ x₁))
 ＝⟨ ap succ
      (adding-times-lemma-l-n-l env₁ recursive-call r₁ (0 , return x₁)) ⁻¹ ⟩
   succ (recursive-call-time env₁ r₁ x₁ + pr₁ r₁)
 ＝⟨ ap (λ z → succ (recursive-call-time env₁ r₁ x₁ + pr₁ z))
      (last-list-same-env l₁) ⟩
   succ (recursive-call-time env₁ r₁ x₁ + pr₁ r₁')
 ＝⟨ ap (λ z → succ (recursive-call-time env₁ r₁ x₁ + z))
      (ap pred' (last-list-list-value-independent env₂ l₁ l₂ (ap pred' eq))) ⟩
   succ (recursive-call-time env₁ r₁ x₁ + pr₁ r₂')
 ＝⟨ ap (λ z → succ (z + pr₁ r₂'))
      (recursive-call-list-value-independent env₁
        (strip-thunk r₁) (strip-thunk r₂)
        (recursive-call-length-lemma env x₁ x₂ l₁ l₂ (ap pred' eq)) x₁ x₂) ⟩
   succ (recursive-call-time env₁ r₂ x₂ + pr₁ r₂')
 ＝⟨ ap (λ z → succ (pr₁ z + pr₁ r₂'))
      (recursive-call-same-env (strip-thunk r₂) x₂) ⟩
   succ (recursive-call-time env₂ r₂ x₂ + pr₁ r₂')
 ＝⟨ ap (λ z → succ (recursive-call-time env₂ r₂ x₂ + pr₁ z))
      (last-list-same-env l₂) ⁻¹ ⟩
   succ (recursive-call-time env₂ r₂ x₂ + pr₁ r₂)
 ＝⟨ ap succ (adding-times-lemma-l-n-l env₂ recursive-call r₂ (0 , return x₂)) ⟩
   succ (pr₁ (last-step-applied env₂ r₂ x₂))
 ∎
 where
  env₁ : Envᵢ (list ∷ Γ)
  env₁ = thunk-type (x₁ ∷ l₁) ∷Eᵢ env

  env₂ : Envᵢ (list ∷ Γ)
  env₂ = thunk-type (x₂ ∷ l₂) ∷Eᵢ env

  r₁ = list-recᵢ env₁ l₁ nil last-step eager
  r₂ = list-recᵢ env₂ l₂ nil last-step eager

  r₁' = list-recᵢ ((0 , return l₁) ∷Eᵢ env₂) l₁ nil last-step eager
  r₂' = list-recᵢ ((0 , return l₂) ∷Eᵢ env₂) l₂ nil last-step eager

last-list-value-independent : {n : ℕ} {Γ : Ctx n}
                            → (env : Envᵢ Γ)
                            → time-independent-of-list-values env
                               (inl refl) eager last
last-list-value-independent {n} {Γ} env l₁ l₂ eq
 = pr₁ (E₁ [ head ∙ last-list ]ᵢ eager)
 ＝⟨ refl ⟩
   pr₁ ((pr₁ (E₁ [ head ]ᵢ eager)) (E₁ [ last-list ]ᵢ eager))
 ＝⟨ adding-times-lemma (inr refl) (inl refl) E₁ head-comp
      (E₁ [ last-list ]ᵢ eager) ⁻¹ ⟩
   head-comp-time E₁ (strip-thunk {list} (E₁ [ last-list ]ᵢ eager))
   + pr₁ (E₁ [ last-list ]ᵢ eager)
 ＝⟨ ap (λ z → head-comp-time E₁ z + pr₁ (E₁ [ last-list ]ᵢ eager))
      (equivalent-semantics E₁ last-list eager) ⟩
   head-comp-time E₁ (semantics l₁) + pr₁ (E₁ [ last-list ]ᵢ eager)
 ＝⟨ ap (λ z → pr₁ z + pr₁ (E₁ [ last-list ]ᵢ eager))
      (head-time-value-env-independent-eager (thunk-type (semantics l₁))) ⟩
   head-comp-time E₂ (semantics l₁) + pr₁ (E₁ [ last-list ]ᵢ eager)
 ＝⟨ ap (_+ pr₁ (E₁ [ last-list ]ᵢ eager))
      (head-list-value-independent-eager E₂
        (semantics l₁) (semantics l₂) (last-comp-length-lemma l₁ l₂ eq)) ⟩
   head-comp-time E₂ (semantics l₂) + pr₁ (E₁ [ last-list ]ᵢ eager)
 ＝⟨ ap (head-comp-time E₂ (semantics l₂) +_)
      (last-list-list-value-independent env l₁ l₂ eq) ⟩
   head-comp-time E₂ (semantics l₂) + pr₁ (E₂ [ last-list ]ᵢ eager)
 ＝⟨ ap (λ z → head-comp-time E₂ z + pr₁ (E₂ [ last-list ]ᵢ eager))
      (equivalent-semantics E₂ last-list eager) ⁻¹ ⟩
   head-comp-time E₂ (strip-thunk {list} (E₂ [ last-list ]ᵢ eager))
   + pr₁ (E₂ [ last-list ]ᵢ eager)
 ＝⟨ adding-times-lemma (inr refl) (inl refl) E₂ head-comp
      (E₂ [ last-list ]ᵢ eager) ⟩
   pr₁ (E₂ [ head ∙ last-list ]ᵢ eager)
 ∎
 where
  E₁ : Envᵢ (list ∷ Γ)
  E₁ = thunk-type l₁ ∷Eᵢ env

  E₂ : Envᵢ (list ∷ Γ)
  E₂ = thunk-type l₂ ∷Eᵢ env

  semantics : List ℕ → List ℕ
  semantics l = (l ∷E (strip-thunk-env env)) [ last-list ]ₑ

\end{code}
