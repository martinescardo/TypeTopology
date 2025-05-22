Theo Hepburn, started February 2025

Provides useful functions and lemmas for reasoning
about the running time of functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.ComplexityDefinitionsResults (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin
open import MLTT.List
open import UF.Base
open import TGH.Thunk
open import TGH.BigO
open import TGH.NatOrder
open import TGH.Language fe

is-polytime : (k C N₀ x y : ℕ) → 𝓤₀ ̇
is-polytime k C N₀ x y = N₀ ≤ x → y ≤ C * (x ^ k)

get-time : {τ : LType} → ((τ ＝ nat) ∔ (τ ＝ list)) → ⟦ τ ⟧ᵢ → ℕ
get-time (inl refl) x = pr₁ x
get-time (inr refl) x = pr₁ x

gen-naive-list : (n : ℕ) → List ℕ
gen-naive-list zero = []
gen-naive-list (succ n) = 0 ∷ gen-naive-list n

call-intermediate-l : {σ : LType} {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                    → Term Γ (list ⇒ σ) → (strategy : Strategy)
                    → List ℕ → ⟦ σ ⟧ᵢ
call-intermediate-l env t s l = (pr₁ (env [ t ]ᵢ s)) (thunk-type l)

time-independent-of-list-values : {τ : LType} {n : ℕ} {Γ : Ctx n}
                                → (env : Envᵢ Γ)
                                → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                                → (strategy : Strategy)
                                → (Term Γ (list ⇒ τ))
                                → Type
time-independent-of-list-values env (inl refl) strategy program
 = (l₁ l₂ : List ℕ) → (length l₁ ＝ length l₂)
   → pr₁ (call-intermediate-l env program strategy l₁)
   ＝ pr₁ (call-intermediate-l env program strategy l₂)
time-independent-of-list-values env (inr refl) strategy program
 = (l₁ l₂ : List ℕ) → (length l₁ ＝ length l₂)
   → pr₁ (call-intermediate-l env program strategy l₁)
   ＝ pr₁ (call-intermediate-l env program strategy l₂)

time-independent-of-list-values-n : {τ : LType} {n : ℕ} {Γ : Ctx n}
                                  → (env : Envᵢ Γ)
                                  → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                                  → (strategy : Strategy)
                                  → (program : Term Γ (list ⇒ nat ⇒ τ))
                                  → 𝓤₀ ̇
time-independent-of-list-values-n env (inl refl) strategy program
 = (l₁ l₂ : List ℕ) → (length l₁ ＝ length l₂) → (n₁ n₂ : ℕ)
  → pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₁)) (thunk-type n₁))
  ＝ pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₂)) (thunk-type n₂))
time-independent-of-list-values-n env (inr refl) strategy program
 = (l₁ l₂ : List ℕ) → (length l₁ ＝ length l₂) → (n₁ n₂ : ℕ)
  → pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₁)) (thunk-type n₁))
  ＝ pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₂)) (thunk-type n₂))

list-time-function-naive : {τ : LType} {n : ℕ} {Γ : Ctx n}
                         → (env : Envᵢ Γ)
                         → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                         → (program : Term Γ (list ⇒ τ))
                         → (strategy : Strategy)
                         → ℕ → ℕ
list-time-function-naive env (inl refl) program strategy n
 = pr₁ (call-intermediate-l env program strategy (gen-naive-list n))
list-time-function-naive env (inr refl) program strategy n
 = pr₁ (call-intermediate-l env program strategy (gen-naive-list n))

naive-list-length-lemma : (n : ℕ) → n ＝ length (gen-naive-list n)
naive-list-length-lemma zero = refl
naive-list-length-lemma (succ n) = ap succ (naive-list-length-lemma n)

is-linear-time : {τ : LType} {n : ℕ} {Γ : Ctx n}
               → (program : Term Γ (list ⇒ τ))
               → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
               → 𝓤₀ ̇
is-linear-time {τ} {n} {Γ} program nat-or-list
 = Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ ,
   is-polytime 1 C N₀ (length l)
   (get-time nat-or-list (pr₁ (env [ program ]ᵢ eager) (thunk-type l)))

is-linear-time-n : {τ : LType} {n : ℕ} {Γ : Ctx n}
                 → (program : Term Γ (list ⇒ nat ⇒ τ))
                 → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                 → Type
is-linear-time-n {τ} {n} {Γ} program nat-or-list
 = Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π x ꞉ ℕ , Π env ꞉ Envᵢ Γ ,
   is-polytime 1 C N₀ (length l) (get-time nat-or-list
   (pr₁ (pr₁ (env [ program ]ᵢ eager) (thunk-type l)) (thunk-type x)))

is-polytime-to-polybigO : {τ : LType} {n : ℕ} {Γ : Ctx n}
                        → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                        → (program : Term (list ∷ Γ) τ)
                        → (k : ℕ)
                        → (Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ ,
                          is-polytime k C N₀ (length l)
                          (get-time nat-or-list (pr₁ (env [ lam list program ]ᵢ
                          eager) (thunk-type l))))
                        → Π env ꞉ Envᵢ Γ ,
                          ((list-time-function-naive env nat-or-list
                          (lam list program) eager) ∈O[ (λ n → n ^ k) ])
is-polytime-to-polybigO (inl refl) program k (C , N₀ , f) env
 = bigO (C , (N₀ , λ n le → transport (λ z → pr₁
   (pr₁ (eager-function-list env program)
   (0 , return (gen-naive-list n))) ≤ (C * z ^ k))
   (naive-list-length-lemma n ⁻¹) (f (gen-naive-list n) env (transport (N₀ ≤_)
   (naive-list-length-lemma n) le))))
is-polytime-to-polybigO (inr refl) program k (C , N₀ , f) env
 = bigO (C , (N₀ , λ n le → transport (λ z → pr₁
   (pr₁ (eager-function-list env program)
   (0 , return (gen-naive-list n))) ≤ (C * z ^ k))
   (naive-list-length-lemma n ⁻¹) (f (gen-naive-list n) env (transport (N₀ ≤_)
   (naive-list-length-lemma n) le))))

thunk-if-lemma : {τ : LType} → (eq : (τ ＝ nat) ∔ (τ ＝ list))
               → (x : Σ t ꞉ ℕ , Thunk t ℕ)
               → (y : ⟦ τ ⟧ᵢ)
               → (z : ⟦ τ ⟧ᵢ)
               → get-time eq (thunk-if x y z) ≤ succ (max (get-time eq y)
                 (get-time eq z) + pr₁ x)
thunk-if-lemma (inl refl) (zero , return zero) y z
 = max-≤-upper-bound (pr₁ y) (pr₁ z)
thunk-if-lemma (inr refl) (zero , return zero) y z
 = max-≤-upper-bound (pr₁ y) (pr₁ z)
thunk-if-lemma (inl refl) (zero , return (succ _)) y z
 = max-≤-upper-bound' (pr₁ z) (pr₁ y)
thunk-if-lemma (inr refl) (zero , return (succ _)) y z
 = max-≤-upper-bound' (pr₁ z) (pr₁ y)
thunk-if-lemma (inl refl) (succ n , (√ x)) y z
 = thunk-if-lemma (inl refl) (n , x) y z
thunk-if-lemma (inr refl) (succ n , (√ x)) y z
 = thunk-if-lemma (inr refl) (n , x) y z

adding-times-lemma : {σ τ : LType} {n : ℕ} {Γ : Ctx n}
                   → (eq₁ : (σ ＝ nat) ∔ (σ ＝ list))
                   → (eq₂ : (τ ＝ nat) ∔ (τ ＝ list))
                   → (env : Envᵢ Γ) → (program : Term (σ ∷ Γ) τ)
                   → (x : ⟦ σ ⟧ᵢ)
                   → (get-time eq₂ (((thunk-type (strip-thunk x)) ∷Eᵢ env)
                     [ program ]ᵢ eager)) + (get-time eq₁ x)
                     ＝ get-time eq₂ ((pr₁ (env [ lam σ program ]ᵢ eager)) x)
adding-times-lemma (inl refl) (inl refl) env program x = γ x
 where
   γ : (x : Σ t ꞉ ℕ , Thunk t ℕ) → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env)
       [ program ]ᵢ eager) + (pr₁ x) ＝ pr₁ (eager-function-nat-helper env
       program x)
   γ (zero , return x) = refl
   γ (succ n , (√ x)) = ap succ (γ (n , x))
adding-times-lemma (inl refl) (inr refl) env program x = γ x
 where
   γ : (x : Σ t ꞉ ℕ , Thunk t ℕ) → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env)
       [ program ]ᵢ eager) + (pr₁ x) ＝ pr₁ (eager-function-nat-helper env
       program x)
   γ (zero , return x) = refl
   γ (succ n , (√ x)) = ap succ (γ (n , x))
adding-times-lemma (inr refl) (inl refl) env program x = γ x
 where
  γ : (x : Σ t ꞉ ℕ , Thunk t (List ℕ))
    → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env) [ program ]ᵢ eager) + (pr₁ x)
    ＝ pr₁ (eager-function-list-helper env program x)
  γ (zero , return x) = refl
  γ (succ n , (√ x)) = ap succ (γ (n , x))
adding-times-lemma (inr refl) (inr refl) env program x = γ x
 where
  γ : (x : Σ t ꞉ ℕ , Thunk t (List ℕ))
    → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env) [ program ]ᵢ eager)
    + (pr₁ x) ＝ pr₁ (eager-function-list-helper env program x)
  γ (zero , return x) = refl
  γ (succ n , (√ x)) = ap succ (γ (n , x))

adding-times-lemma-l-n-l : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                         → (program : Term (nat ∷ list ∷ Γ) list)
                         → (l : Σ t ꞉ ℕ , Thunk t (List ℕ))
                         → (x : Σ t ꞉ ℕ , Thunk t ℕ)
                         → (pr₁ (((thunk-type {nat} (strip-thunk x))
                         ∷Eᵢ (thunk-type {list} (strip-thunk l)) ∷Eᵢ env)
                         [ program ]ᵢ eager)) + pr₁ l + pr₁ x ＝ pr₁ (pr₁
                         ((pr₁ (env [ lam list (lam nat program) ]ᵢ eager))
                         l) x)
adding-times-lemma-l-n-l env program (zero , return x) (zero , return x₁) = refl
adding-times-lemma-l-n-l env program (zero , return x) (succ pr₃ , (√ x₁))
 = ap succ (adding-times-lemma-l-n-l env program (0 , return x) (pr₃ , x₁))
adding-times-lemma-l-n-l env program (succ pr₃ , (√ x)) (pr₅ , x₁)
 = succ
      (pr₁
       (((0 , return (force x₁)) ∷Eᵢ (0 , return (force x)) ∷Eᵢ env) [
        program ]ᵢ eager)
       + pr₃)
      + pr₅ ＝⟨ succ-left (pr₁
               (((0 , return (force x₁)) ∷Eᵢ (0 , return (force x)) ∷Eᵢ env) [
                 program ]ᵢ eager)
               + pr₃) pr₅ ⟩
       succ
      ((pr₁
       (((0 , return (force x₁)) ∷Eᵢ (0 , return (force x)) ∷Eᵢ env) [
        program ]ᵢ eager)
       + pr₃)
      + pr₅)
      ＝⟨ ap succ (adding-times-lemma-l-n-l env program (pr₃ , x) (pr₅ , x₁)) ⟩
       succ
        (pr₁
         (pr₁ (pr₁ (env [ lam list (lam nat program) ]ᵢ eager) (pr₃ , x))
          (pr₅ , x₁))) ∎

\end{code}
