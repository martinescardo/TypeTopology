Theo Hepburn, started February 2025

Provides useful functions and lemmas for reasoning about the running time
of programs in our language.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.ComplexityDefinitionsResults (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin
open import MLTT.List
open import UF.Base
open import TGH.Thunk
open import TGH.BigO
open import TGH.Language fe

\end{code}

`call-intermediate-l` evaluates the program as a function using the intermediate
semantics and the given evaluation strategy, then applies the function to the
Thunked version of the list supplied by the user.

\begin{code}

call-intermediate-l : {σ : LType} {n : ℕ} {Γ : Ctx n}
                    → (env : Envᵢ Γ)
                    → Term Γ (list ⇒ σ)
                    → (strategy : Strategy)
                    → List ℕ → ⟦ σ ⟧ᵢ
call-intermediate-l env t s l = (pr₁ (env [ t ]ᵢ s)) (thunk-type l)


\end{code}

`time-independent-of-list-values` is true if the running time of a program whose
only input is a list and whose output is a `nat` or `list` depends only on the
length of the input list.

ie. the running time is always the same for any two lists of the same length

\begin{code}

time-independent-of-list-values : {τ : LType} {n : ℕ} {Γ : Ctx n}
                                → (env : Envᵢ Γ)
                                → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                                → (strategy : Strategy)
                                → (Term Γ (list ⇒ τ))
                                → 𝓤₀ ̇
time-independent-of-list-values env (inl refl) strategy program
 = (l₁ l₂ : List ℕ)
  → (length l₁ ＝ length l₂)
  → pr₁ (call-intermediate-l env program strategy l₁)
  ＝ pr₁ (call-intermediate-l env program strategy l₂)
time-independent-of-list-values env (inr refl) strategy program
 = (l₁ l₂ : List ℕ)
  → (length l₁ ＝ length l₂)
  → pr₁ (call-intermediate-l env program strategy l₁)
  ＝ pr₁ (call-intermediate-l env program strategy l₂)

\end{code}

For the sake of simplicity, the lists that we generate to compute running
times of functions that satisfy `time-independent-of-list-values` will contain
only zeros.

\begin{code}


gen-naive-list : (n : ℕ) → List ℕ
gen-naive-list zero = []
gen-naive-list (succ n) = 0 ∷ gen-naive-list n

\end{code}

We define a function `list-time-function-naive` that computes a naive time
function for a program ie. one that uses a “naive” list full of zeros
of the given length. Accepts programs with a list argument that return
a `nat` or a `list`.

To ensure that this will only ever generate a valid time function, we should
first prove that the program satisfies time-independent-of-list-values
before we use this to generate a time function.

\begin{code}

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

\end{code}

Variation of the above for programs that accept an additional `nat` argument.

\begin{code}

time-independent-of-list-values-n : {τ : LType} {n : ℕ} {Γ : Ctx n}
                                  → (env : Envᵢ Γ)
                                  → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                                  → (strategy : Strategy)
                                  → (program : Term Γ (list ⇒ nat ⇒ τ))
                                  → 𝓤₀ ̇
time-independent-of-list-values-n env (inl refl) strategy program
 = (l₁ l₂ : List ℕ)
  → (length l₁ ＝ length l₂)
  → (n₁ n₂ : ℕ)
  → pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₁)) (thunk-type n₁))
  ＝ pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₂)) (thunk-type n₂))
time-independent-of-list-values-n env (inr refl) strategy program
 = (l₁ l₂ : List ℕ)
  → (length l₁ ＝ length l₂)
  → (n₁ n₂ : ℕ)
  → pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₁)) (thunk-type n₁))
  ＝ pr₁ (pr₁ (pr₁ (env [ program ]ᵢ strategy) (thunk-type l₂)) (thunk-type n₂))

naive-list-length-lemma : (n : ℕ) → n ＝ length (gen-naive-list n)
naive-list-length-lemma zero = refl
naive-list-length-lemma (succ n) = ap succ (naive-list-length-lemma n)

\end{code}

Alternative definition of polynomial time that doesn't use time functions,
for programs that take a `list` as input and return a `nat` or `list`.

We provide the size of the input `x` and the running time `y` as arguments
to `is-polytime`.

Allows us to prove properties about the running time for arbitrary lists,
rather than just generated naive lists, allowing us to prove results that
are more general.

\begin{code}

is-polytime : (k C N₀ x y : ℕ) → 𝓤₀ ̇
is-polytime k C N₀ x y = N₀ ≤ x → y ≤ C * (x ^ k)

get-time : {τ : LType} → ((τ ＝ nat) ∔ (τ ＝ list)) → ⟦ τ ⟧ᵢ → ℕ
get-time (inl refl) x = pr₁ x
get-time (inr refl) x = pr₁ x

is-program-k-poly-time : {τ : LType} {n : ℕ} {Γ : Ctx n}
                     → (program : Term Γ (list ⇒ τ))
                     → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                     → (k : ℕ)
                     → 𝓤₀ ̇
is-program-k-poly-time {τ} {n} {Γ} program nat-or-list k =
 Σ C ꞉ ℕ
 , Σ N₀ ꞉ ℕ 
   , Π l ꞉ List ℕ
     , Π env ꞉ Envᵢ Γ
      , is-polytime k C N₀ (length l)
         (get-time nat-or-list
          (pr₁ (env [ program ]ᵢ eager) (thunk-type l))
         )

\end{code}

We use `is-program-k-poly-time` to create a definition of
linear time.

\begin{code}

is-program-linear-time : {τ : LType} {n : ℕ} {Γ : Ctx n}
               → (program : Term Γ (list ⇒ τ))
               → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
               → 𝓤₀ ̇
is-program-linear-time program nat-or-list
 = is-program-k-poly-time program nat-or-list 1

\end{code}

Variation of the above for programs that take an additional
`nat` argument.

\begin{code}

is-program-linear-time-n : {τ : LType} {n : ℕ} {Γ : Ctx n}
                         → (program : Term Γ (list ⇒ nat ⇒ τ))
                         → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                         → 𝓤₀ ̇
is-program-linear-time-n {τ} {n} {Γ} program nat-or-list =
 Σ C ꞉ ℕ
  , Σ N₀ ꞉ ℕ
   , Π l ꞉ List ℕ
    , Π x ꞉ ℕ
     , Π env ꞉ Envᵢ Γ
      , is-polytime 1 C N₀ (length l)
         (get-time nat-or-list
          (pr₁ (pr₁ (env [ program ]ᵢ eager) (thunk-type l)) (thunk-type x))
         )
      
\end{code}

We show that if a program satisfies `is-program-k-poly-time` for some
`k` it is O(nᵏ).

\begin{code}

is-polytime-to-polybig-o : {τ : LType} {n : ℕ} {Γ : Ctx n}
                         → (nat-or-list : (τ ＝ nat) ∔ (τ ＝ list))
                         → (program : Term (list ∷ Γ) τ)
                         → (k : ℕ)
                         → is-program-k-poly-time
                            (lam list program) nat-or-list k
                         → Π env ꞉ Envᵢ Γ ,
                           (
                            (list-time-function-naive env nat-or-list
                             (lam list program) eager)
                              ∈O[ (λ n → n ^ k) ]
                           )
is-polytime-to-polybig-o
 (inl refl)
  program
   k
    (C , N₀ , f)
     env
 = big-o
    (C
     , (N₀
      , λ n le
       → transport
          (
           λ z
            → pr₁
             (
              pr₁
               (eager-function-list env program)
                (0 , return (gen-naive-list n))
             )
            ≤ (C * z ^ k)
          )
           (naive-list-length-lemma n ⁻¹)
            (
             f
              (gen-naive-list n)
               env
                (transport (N₀ ≤_) (naive-list-length-lemma n) le)
            )
       )
    )
is-polytime-to-polybig-o
 (inr refl)
  program
   k
    (C , N₀ , f)
     env
 = big-o
    (
     C
      , (N₀
       , λ n le
       → transport
        (λ z → pr₁
         (pr₁ (eager-function-list env program) (0 , return (gen-naive-list n)))
          ≤ (C * z ^ k)
        )
         (naive-list-length-lemma n ⁻¹)
          (f (gen-naive-list n) env
           (transport (N₀ ≤_) (naive-list-length-lemma n) le)
          )
        )
    )

\end{code}

We show that the running time of an if..then..else.. condition is less than or
equal to the running time of the branch with the longer running time, plus the
time taken to compute the condition, plus one.

\begin{code}

thunk-if-lemma : {τ : LType}
               → (eq : (τ ＝ nat) ∔ (τ ＝ list))
               → (x@(t , _) : Σ t ꞉ ℕ , Thunk t ℕ)
               → (y : ⟦ τ ⟧ᵢ)
               → (z : ⟦ τ ⟧ᵢ)
               → get-time eq (thunk-if x y z)
               ≤ succ (max (get-time eq y)
                  (get-time eq z) + t)
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

 \end{code}

We show that, when the eager evaluation strategy is used, a program `f` that
takes an input `x` that is a `nat` or a `list` and returns an output that is
a `nat` or a `list` takes a total number of steps to run that is equal to the
number of steps to construct `x` plus the number of steps to run `f` with the
value component of `x`, but associated with zero steps of computation, as an
input.

 \begin{code}

adding-times-lemma : {σ τ : LType} {n : ℕ} {Γ : Ctx n}
                   → (eq₁ : (σ ＝ nat) ∔ (σ ＝ list))
                   → (eq₂ : (τ ＝ nat) ∔ (τ ＝ list))
                   → (env : Envᵢ Γ)
                   → (program : Term (σ ∷ Γ) τ)
                   → (x : ⟦ σ ⟧ᵢ)
                   → (get-time eq₂ (((thunk-type (strip-thunk x)) ∷Eᵢ env)
                     [ program ]ᵢ eager)) + (get-time eq₁ x)
                   ＝ get-time eq₂ ((pr₁ (env [ lam σ program ]ᵢ eager)) x)
adding-times-lemma (inl refl) (inl refl) env program x = γ x
 where
  γ : (x@(t , _) : Σ t ꞉ ℕ , Thunk t ℕ)
    → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env) [ program ]ᵢ eager) + t
    ＝ pr₁ (eager-function-nat-helper env program x)
  γ (zero , return x) = refl
  γ (succ n , (√ x)) = ap succ (γ (n , x))
adding-times-lemma (inl refl) (inr refl) env program x = γ x
 where
  γ : (x@(t , _) : Σ t ꞉ ℕ , Thunk t ℕ)
    → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env) [ program ]ᵢ eager) + t
    ＝ pr₁ (eager-function-nat-helper env program x)
  γ (zero , return x) = refl
  γ (succ n , (√ x)) = ap succ (γ (n , x))
adding-times-lemma (inr refl) (inl refl) env program x = γ x
 where
  γ : (x@(t , _) : Σ t ꞉ ℕ , Thunk t (List ℕ))
    → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env) [ program ]ᵢ eager) + t
    ＝ pr₁ (eager-function-list-helper env program x)
  γ (zero , return x) = refl
  γ (succ n , (√ x)) = ap succ (γ (n , x))
adding-times-lemma (inr refl) (inr refl) env program x = γ x
 where
  γ : (x@(t , _) : Σ t ꞉ ℕ , Thunk t (List ℕ))
    → pr₁ (((0 , return (strip-thunk x)) ∷Eᵢ env) [ program ]ᵢ eager)
    + t ＝ pr₁ (eager-function-list-helper env program x)
  γ (zero , return x) = refl
  γ (succ n , (√ x)) = ap succ (γ (n , x))

\end{code}

Similar proof for programs that take one `list` argument and one `nat` argument,
and return a list.

\begin{code}

adding-times-lemma-l-n-l : {n : ℕ} {Γ : Ctx n}
                         → (env : Envᵢ Γ)
                         → (program : Term (nat ∷ list ∷ Γ) list)
                         → (l@(tₗ , _) : Σ t ꞉ ℕ , Thunk t (List ℕ))
                         → (x@(tₓ , _) : Σ t ꞉ ℕ , Thunk t ℕ)
                         → (pr₁ (((thunk-type {nat} (strip-thunk x))
                            ∷Eᵢ (thunk-type {list} (strip-thunk l)) ∷Eᵢ env)
                             [ program ]ᵢ eager)) + tₗ + tₓ
                         ＝ pr₁ (pr₁
                             (
                              (pr₁ (env [ lam list (lam nat program) ]ᵢ eager))
                              l
                             ) x
                            )
adding-times-lemma-l-n-l env program (zero , return x) (zero , return x₁)
 = refl
adding-times-lemma-l-n-l env program (zero , return x) (succ pr₃ , (√ x₁))
 = ap succ (adding-times-lemma-l-n-l env program (0 , return x) (pr₃ , x₁))
adding-times-lemma-l-n-l env program (succ pr₃ , (√ x)) (pr₅ , x₁)
 = succ
    (
     pr₁
      (
       ((0 , return (force x₁)) ∷Eᵢ (0 , return (force x)) ∷Eᵢ env)
     [ program ]ᵢ eager)
     + pr₃)
    + pr₅
   ＝⟨ succ-left (pr₁
        (((0 , return (force x₁)) ∷Eᵢ (0 , return (force x)) ∷Eᵢ env)
         [ program ]ᵢ eager)
        + pr₃)
       pr₅
     ⟩
   succ
    ((pr₁
     (((0 , return (force x₁)) ∷Eᵢ (0 , return (force x)) ∷Eᵢ env)
      [ program ]ᵢ eager)
      + pr₃)
     + pr₅)
    ＝⟨ ap succ
         (adding-times-lemma-l-n-l env program (pr₃ , x) (pr₅ , x₁)
        )
      ⟩
    succ
     (pr₁
      (pr₁ (pr₁ (env [ lam list (lam nat program) ]ᵢ eager) (pr₃ , x))
       (pr₅ , x₁)
      )
     )
    ∎

\end{code}
