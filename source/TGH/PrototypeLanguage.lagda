Theo Hepburn, started 22/05/2025.

A prototype language that features natural numbers as the only basic type.
We also have examples of simple functions in this language.
We use function extensionality as we must prove the equality of functions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_∙_)
open import UF.FunExt

module TGH.PrototypeLanguage (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import Naturals.Double renaming (double to double')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.List
open import MLTT.Bool hiding (if_then_else_)
open import MLTT.Fin
open import TGH.BigO
open import TGH.Thunk

\end{code}

Our prototype language features natural numbers as the only basic type,
with it being possible to construct functions on top of this type.
List types are not yet featured.

\begin{code}

infixr 30 _⇒_
data LType : 𝓤₀ ̇  where
 nat : LType
 _⇒_ : LType → LType → LType

 \end{code}

The syntax of terms in our language is defined as follows using an
inductive family of datatypes.

`zero` and `suc` are the constructors for natural numbers.

`var` is a variable lookup. `Ctx` is a vector of the types of variables.
The type of the variable with de Bruijn index `i` is stored at position `i` of
the context.

`if_then_else_` allows for conditional branching. Here both branches
must return natural numbers.

`_∙_` is the application operator, allowing a function to be applied to an
argument.

`nrec` allows for recursion on natural numbers.

 \begin{code}

Ctx : ℕ → 𝓤₀ ̇
Ctx = Vec LType

data Term {n : ℕ} (Γ : Ctx n) : LType → 𝓤₀ ̇  where
 zero : Term Γ nat
 suc : Term Γ nat → Term Γ nat
 var : (v : Fin n) → Term Γ (Γ !! v)
 if_then_else_ : Term Γ nat → Term Γ nat → Term Γ nat → Term Γ nat
 _∙_ : {σ τ : LType} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
 lam : (σ : LType) {τ : LType} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
 nrec : Term Γ nat → Term Γ nat → Term Γ (nat ⇒ nat) → Term Γ nat

Closed : LType → 𝓤₀ ̇
Closed = Term []

\end{code}

We define a translation from LTypes to Agda Types.

\begin{code}

⟦_⟧ : LType → 𝓤₀ ̇
⟦ nat ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

\end{code}

We define the concept of the environment, which is the vector of values
for variables currently in scope.

We look up the value of a variable using its de Bruijn index.

\begin{code}

infixr 5 _∷E_
data Env : {n : ℕ} → Ctx n → 𝓤₀ ̇  where
 [] : Env []
 _∷E_ : {n : ℕ} {Γ : Ctx n } {τ : LType} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookup-env : {n : ℕ} {Γ : Ctx n} → (m : Fin n) → Env Γ → ⟦ Γ !! m ⟧
lookup-env 𝟎 (x ∷E _) = x
lookup-env (suc m) (x ∷E env) = lookup-env m env

\end{code}

if..then..else.. defined using a natural number, rather than a boolean,
as the condition.

\begin{code}

if'_then'_else'_ : {X : 𝓤₀ ̇} → ℕ → X → X → X
if' zero then' x else' y = x
if' succ _ then' x else' y = y

\end{code}

Natural number recursion.

\begin{code}

nat-rec : {n : ℕ} {Γ : Ctx n}
        → Env Γ
        → (m : ℕ)
        → (base : Term Γ nat)
        → (f : Term Γ (nat ⇒ nat))
        → ℕ

\end{code}

Semantics of the prototype language.

\begin{code}

_[_]ₑ : {n : ℕ} {Γ : Ctx n} {τ : LType} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v ]ₑ = lookup-env v env
env [ zero ]ₑ = zero
env [ suc t ]ₑ = succ (env [ t ]ₑ)
env [ if t then u else v ]ₑ
 = if' (env [ t ]ₑ) then' (env [ u ]ₑ) else' (env [ v ]ₑ)
env [ t ∙ u ]ₑ = (env [ t ]ₑ) (env [ u ]ₑ)
env [ lam _ t ]ₑ = λ x → (x ∷E env) [ t ]ₑ
env [ nrec t u v ]ₑ = nat-rec env (env [ t ]ₑ) u v

nat-rec env zero base f = env [ base ]ₑ
nat-rec env (succ m) base f = (env [ f ]ₑ) (nat-rec env m base f)

\end{code}

Program to double a natural number.

\begin{code}

double-step : {n : ℕ} {Γ : Ctx n} → Term Γ (nat ⇒ nat)
double-step = lam nat (suc (suc (var 𝟎)))

double : Closed (nat ⇒ nat)
double = lam nat (nrec (var 𝟎) zero double-step)

\end{code}

Correctness of the `double` program.

\begin{code}

double-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                 → (m : ℕ)
                 → nat-rec env₁ m zero double-step
                 ＝ nat-rec env₂ m zero double-step
double-env-lemma zero = refl
double-env-lemma (succ m) = ap (succ ∘ succ) (double-env-lemma m)

double-correctness : (n : ℕ) → ([] [ double ]ₑ) n ＝ double' n
double-correctness zero = refl
double-correctness (succ n)
 = succ (succ (nat-rec (succ n ∷E []) n zero double-step))
 ＝⟨ ap (succ ∘ succ) (double-env-lemma n) ⟩
   succ (succ (nat-rec [] n zero double-step))
 ＝⟨ ap (succ ∘ succ) γ ⟩
   succ (succ (double' n))
 ∎
 where
  γ : nat-rec [] n zero double-step ＝ double' n
  γ = nat-rec [] n zero double-step
    ＝⟨ (double-env-lemma n)⁻¹ ⟩
      nat-rec (n ∷E []) n zero double-step
    ＝⟨ double-correctness n ⟩
      double' n
    ∎

\end{code}

Intermediate semantics. Uses the `Thunk` monad to keep track of the computed
value along with the number of steps to compute it.

\begin{code}

NatThunk : 𝓤₀ ̇
NatThunk = Σ t ꞉ ℕ , Thunk t ℕ

\end{code}

In the intermediate semantics we have a different corresponding Agda type for
each `LType`, so we define a new type translation.

\begin{code}

⟦_⟧ᵢ : LType → 𝓤₀ ̇

thunk-type : {σ : LType} → ⟦ σ ⟧ → ⟦ σ ⟧ᵢ

strip-thunk : {σ : LType} → ⟦ σ ⟧ᵢ → ⟦ σ ⟧

\end{code}

`value-time-independent` enforces that the value within the `Thunk` monad
returned by the function `f` depends only on the value within the thunk
arugment `x`, rather than the number of steps contained by `x`.

This is crucial for proving that the normal and intermediate semantics are
equivalent with regards to values, which we do later.

\begin{code}

value-time-independent : {σ τ : LType} → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → 𝓤₀ ̇
value-time-independent {σ} f
 = (x y : ⟦ σ ⟧ᵢ)
 → strip-thunk x ＝ strip-thunk y
 → strip-thunk (f x) ＝ strip-thunk (f y)

⟦ nat ⟧ᵢ = NatThunk
⟦ σ ⇒ τ ⟧ᵢ = Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f

get-time : NatThunk → ℕ
get-time = pr₁

get-thunk : ((t , _) : NatThunk) → Thunk t ℕ
get-thunk = pr₂

get-function : {σ τ : LType} → ⟦ σ ⇒ τ ⟧ᵢ → (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
get-function = pr₁

get-value-time-independent : {σ τ : LType}
                           → ((f , _) : ⟦ σ ⇒ τ ⟧ᵢ)
                           → value-time-independent f
get-value-time-independent = pr₂

thunk-type {nat} x = 0 , return x
thunk-type {σ ⇒ σ₁} f = (λ x → thunk-type (f (strip-thunk x))) , γ f
 where
  γ : {σ σ₁ : LType}
    → (f : ⟦ σ ⟧ → ⟦ σ₁ ⟧)
    → (x y : ⟦ σ ⟧ᵢ)
    → strip-thunk x ＝ strip-thunk y
    → strip-thunk (thunk-type (f (strip-thunk x)))
    ＝ strip-thunk (thunk-type (f (strip-thunk y)))
  γ {_} {_} f x y eq = ap (strip-thunk ∘ thunk-type ∘ f) eq

strip-thunk {nat} (_ , s) = force s
strip-thunk {σ ⇒ σ₁} (f , _) = λ x → strip-thunk (f (thunk-type x))

strip-thunk-is-inverse-of-thunk-type : {σ : LType}
                                     → (x : ⟦ σ ⟧)
                                     → strip-thunk (thunk-type x) ＝ x

strip-thunk-is-inverse-of-thunk-lemma : {σ τ : LType}
                                      → (f : ⟦ σ ⟧ → ⟦ τ ⟧)
                                      → (x : ⟦ σ ⟧)
                                      → strip-thunk (thunk-type f) x ＝ f x
strip-thunk-is-inverse-of-thunk-lemma f x
 = strip-thunk (thunk-type (f (strip-thunk (thunk-type x))))
 ＝⟨ ap (strip-thunk ∘ thunk-type ∘ f)
      (strip-thunk-is-inverse-of-thunk-type x) ⟩
   strip-thunk (thunk-type (f x))
 ＝⟨ strip-thunk-is-inverse-of-thunk-type (f x) ⟩
   f x
 ∎

strip-thunk-is-inverse-of-thunk-type {nat} x = refl
strip-thunk-is-inverse-of-thunk-type {σ ⇒ τ} f
 = fe (strip-thunk-is-inverse-of-thunk-lemma f)

\end{code}

We need a new type of environment for the intermediate semantics to contain
the type translations for the intermediate rather than the normal semantics.

We also need new functions for looking up variables within that environment.

\begin{code}

infixr 5 _∷Eᵢ_
data Envᵢ : {n : ℕ} → Ctx n → 𝓤₀ ̇ where
 [] : Envᵢ []
 _∷Eᵢ_ : {n : ℕ} {Γ : Ctx n } {τ : LType}
       → ⟦ τ ⟧ᵢ
       → Envᵢ Γ
       → Envᵢ (τ ∷ Γ)

strip-thunk-env : {n : ℕ} {Γ : Ctx n } → Envᵢ Γ → Env Γ
strip-thunk-env [] = []
strip-thunk-env (x ∷Eᵢ xs) = strip-thunk x ∷E (strip-thunk-env xs)

lookup-envᵢ : {n : ℕ} {Γ : Ctx n} → (m : Fin n) → Envᵢ Γ → ⟦ Γ !! m ⟧ᵢ
lookup-envᵢ 𝟎 (x ∷Eᵢ _) = x
lookup-envᵢ (suc m) (x ∷Eᵢ env) = lookup-envᵢ m env

\end{code}

Semantics for `if_then_else_` using NatThunk. Moves time steps for the condition
to the output and adds 1 additional time step.

\begin{code}

thunk-if : NatThunk → NatThunk → NatThunk → NatThunk
thunk-if (zero , return zero) (n₂ , u) (n₃ , v) = succ n₂ , (√ u)
thunk-if (zero , return (succ _)) (n₂ , u) (n₃ , v) = succ n₃ , (√ v)
thunk-if (succ n₁ , (√ t)) u v
 = succ (get-time (thunk-if (n₁ , t) u v))
 , (√ (get-thunk (thunk-if (n₁ , t) u v)))

\end{code}

Natural number recursion for `NatThunk`.

\begin{code}

nat-recᵢ : {n : ℕ} {Γ : Ctx n}
         → Envᵢ Γ
         → (m : ℕ)
         → (base : Term Γ nat)
         → (f : Term Γ (nat ⇒ nat))
         → NatThunk

rec-builder : {n : ℕ} {Γ : Ctx n}
            → Envᵢ Γ
            → NatThunk
            → (base : Term Γ nat)
            → (f : Term Γ (nat ⇒ nat))
            → NatThunk

strip-thunk-thunk-type-rearrange : {τ σ : LType}
                                 → (f : ⟦ τ ⇒ σ ⟧ᵢ)
                                 → (z : ⟦ τ ⟧)
                                 → strip-thunk ((get-function f) (thunk-type z))
                                 ＝ (strip-thunk f) z
strip-thunk-thunk-type-rearrange f z = refl

\end{code}

Helper functions for adding steps to functions and values.

\begin{code}

inc-function : {σ τ : LType} → (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ

inc-eq : {σ τ : LType}
       → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
       → value-time-independent f
       → (x y : ⟦ σ ⟧ᵢ)
       → strip-thunk x ＝ strip-thunk y
       → strip-thunk (inc-function f x) ＝ strip-thunk (inc-function f y)

inc-function {_} {nat} f x = γ (f x)
 where
  γ : NatThunk → NatThunk
  γ (n , x) = succ n , (√ x)
inc-function {σ₁} {σ ⇒ τ} f x
 = inc-function (get-function (f x))
 , inc-eq (get-function (f x)) (get-value-time-independent (f x))

change-function : {σ τ : LType}
                → (f@(f' , _) : ⟦ σ ⇒ τ ⟧ᵢ)
                → (g@(g' , _) : ⟦ σ ⇒ τ ⟧ᵢ)
                → strip-thunk {σ ⇒ τ} f ＝ strip-thunk {σ ⇒ τ} g
                → (λ x → strip-thunk (inc-function f' (thunk-type x)))
                ＝ (λ x → strip-thunk (inc-function g' (thunk-type x)))
change-function {σ} {nat} _ _ eq = eq
change-function {σ} {τ ⇒ τ₁} f g eq
 = fe λ x
 → change-function (get-function f (thunk-type x))
    (get-function g (thunk-type x)) (ap (λ w → w x) eq)

inc-eq {_} {nat} f value-time-ind = value-time-ind
inc-eq {σ₁} {σ ⇒ τ} f value-time-ind x y eq
 = change-function (f x) (f y) (value-time-ind x y eq)

increment : {τ : LType} → ⟦ τ ⟧ᵢ → ⟦ τ ⟧ᵢ
increment {nat} (t , x) = succ t , (√ x)
increment {τ ⇒ σ} (f , eqt) = inc-function f , inc-eq f eqt

increment-equal-semantics : {τ : LType}
                          → (x : ⟦ τ ⟧ᵢ)
                          → strip-thunk x ＝ strip-thunk (increment x)
increment-equal-semantics {nat} x = refl
increment-equal-semantics {σ ⇒ τ} (f , eqt) = fe λ x → γ₂ (thunk-type x)
 where
  γ₁ : {σ τ : LType}
     → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
     → (y : ⟦ σ ⟧ᵢ)
     → strip-thunk (increment (f y)) ＝ strip-thunk (inc-function f y)
  γ₁ {σ} {nat} f y = refl
  γ₁ {σ} {τ ⇒ τ₁} f y = refl

  γ₂ : (y : ⟦ σ ⟧ᵢ) → strip-thunk (f y) ＝ strip-thunk (inc-function f y)
  γ₂ y
   = strip-thunk (f y)
   ＝⟨ increment-equal-semantics (f y) ⟩
     strip-thunk (increment (f y))
   ＝⟨ γ₁ f y ⟩
     strip-thunk (inc-function f y)
   ∎

\end{code}

Intermediate semantics.

Loading variables and constants (only `zero` for now) is defined as taking one
step.

Calling the `suc` primitive takes 1 step.

An `if_then_else_` statement takes 1 step.

Application of a function and natural number recursion do not add any steps
themselves, but they must use the above features, which add steps.

\begin{code}

_[_]ᵢ : {n : ℕ} {Γ : Ctx n} {τ : LType} → Envᵢ Γ → Term Γ τ → ⟦ τ ⟧ᵢ

equivalent-semantics : {n : ℕ} {σ : LType} {Γ : Ctx n}
                     → (env : Envᵢ Γ)
                     → (term : Term Γ σ)
                     → strip-thunk (env [ term ]ᵢ)
                     ＝ (strip-thunk-env env) [ term ]ₑ

lam-value-time-independent : {n : ℕ} {Γ : Ctx n} {τ : LType}
                           → (σ : LType)
                           → (env : Envᵢ Γ)
                           → (t : Term (σ ∷ Γ) τ)
                           → value-time-independent (λ x → (x ∷Eᵢ env) [ t ]ᵢ)
lam-value-time-independent σ env t
 = λ x y eq
 → strip-thunk ((x ∷Eᵢ env) [ t ]ᵢ)
 ＝⟨ equivalent-semantics (x ∷Eᵢ env) t ⟩
   ((strip-thunk x) ∷E (strip-thunk-env env)) [ t ]ₑ
 ＝⟨ ap (λ z → (z ∷E strip-thunk-env env) [ t ]ₑ) eq ⟩
   (((strip-thunk y) ∷E (strip-thunk-env env)) [ t ]ₑ)
 ＝⟨ (equivalent-semantics (y ∷Eᵢ env) t)⁻¹ ⟩
   strip-thunk ((y ∷Eᵢ env) [ t ]ᵢ)
 ∎

env [ var v ]ᵢ = increment (lookup-envᵢ v env )
env [ zero ]ᵢ = 1 , (√ return zero)
env [ if t then u else v ]ᵢ = thunk-if (env [ t ]ᵢ) (env [ u ]ᵢ) (env [ v ]ᵢ)
env [ suc t ]ᵢ = γ (env [ t ]ᵢ)
 where
  γ : NatThunk → NatThunk
  γ (n , t) = 1 + n , (t >>= λ x → √ return (succ x))
env [ t ∙ u ]ᵢ = (get-function (env [ t ]ᵢ)) (env [ u ]ᵢ)
env [ lam σ t ]ᵢ
 = (λ x → (x ∷Eᵢ env) [ t ]ᵢ) , lam-value-time-independent σ env t
env [ nrec t u v ]ᵢ = rec-builder env (env [ t ]ᵢ) u v

rec-builder env (0 , return x) u v = nat-recᵢ env x u v
rec-builder env ((succ _) , (√ x)) u v
 = succ (get-time (rec-builder env (_ , x) u v))
 , (√ (get-thunk (rec-builder env (_ , x) u v)))

nat-recᵢ env zero base f = env [ base ]ᵢ
nat-recᵢ env (succ n) base f
 = (get-function (env [ f ]ᵢ)) (nat-recᵢ env n base f)

strip-thunk-thunk-type-lemma : {σ τ : LType}
                             → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
                             → (eqt : (x y : ⟦ σ ⟧ᵢ)
                                    → strip-thunk x ＝ strip-thunk y
                                    → strip-thunk (f x) ＝ strip-thunk (f y))
                             → (thunked : ⟦ σ ⟧ᵢ)
                             → (unthunked : ⟦ σ ⟧)
                             → strip-thunk thunked ＝ unthunked
                             → strip-thunk (f thunked)
                             ＝ strip-thunk (f (thunk-type unthunked))
strip-thunk-thunk-type-lemma f eqt thunked unthunked eq
 = eqt thunked (thunk-type unthunked) I
 where
  I : strip-thunk thunked ＝ strip-thunk (thunk-type unthunked)
  I = strip-thunk thunked
    ＝⟨ eq ⟩
      unthunked
    ＝⟨ (strip-thunk-is-inverse-of-thunk-type unthunked)⁻¹ ⟩
      strip-thunk (thunk-type unthunked)
    ∎

\end{code}

Proof that the normal and intermediate semantics are equivalent with respect
to values. This means that the intermediate semantics correctly encapsulate the
normal semantics, and we can therefore use them to reason about the running
times of programs for which we have proved correctness using the normal
semantics.

\begin{code}

if-then-else-equality : {n : ℕ} {Γ : Ctx n}
                      → (env : Envᵢ Γ)
                      → (term₁ : Term Γ nat)
                      → (term₂ : Term Γ nat)
                      → (thunked : NatThunk)
                      → (not-thunked : ℕ)
                      → strip-thunk thunked ＝ not-thunked
                      → strip-thunk
                         (thunk-if thunked (env [ term₁ ]ᵢ) (env [ term₂ ]ᵢ))
                      ＝ if' not-thunked
                         then' ((strip-thunk-env env) [ term₁ ]ₑ)
                         else' ((strip-thunk-env env) [ term₂ ]ₑ)
if-then-else-equality env term₁ term₂ (_ , return zero) (succ _) ()
if-then-else-equality env term₁ term₂ (_ , return (succ _)) zero ()
if-then-else-equality env term₁ term₂ (.0 , return zero) zero refl
 = equivalent-semantics env term₁
if-then-else-equality env term₁ term₂ (.(succ _) , (√ t)) zero x
 = if-then-else-equality env term₁ term₂ (_ , t) zero x
if-then-else-equality env term₁ term₂ (.0 , return (succ _)) (succ _) refl
 = equivalent-semantics env term₂
if-then-else-equality env term₁ term₂ (.(succ _) , (√ t)) (succ not-thunked) x
 = if-then-else-equality env term₁ term₂ (_ , t) _ x

application-equality : {n : ℕ} {Γ : Ctx n} {σ τ : LType}
                     → (env : Envᵢ Γ)
                     → (thunked₁@(f , _) : ⟦ σ ⇒ τ ⟧ᵢ)
                     → (thunked₂ : ⟦ σ ⟧ᵢ)
                     → (unthunked₁ : ⟦ σ ⟧ → ⟦ τ ⟧)
                     → (unthunked₂ : ⟦ σ ⟧)
                     → strip-thunk thunked₁ ＝ unthunked₁
                     → strip-thunk thunked₂ ＝ unthunked₂
                     → strip-thunk (f thunked₂) ＝ unthunked₁ unthunked₂
application-equality env (f₁ , eqt) thunked₂ unthunked₁ unthunked₂ eq₁ eq₂
 = strip-thunk (f₁ thunked₂)
 ＝⟨ strip-thunk-thunk-type-lemma f₁ eqt thunked₂ unthunked₂ eq₂ ⟩
   strip-thunk (f₁ (thunk-type unthunked₂))
 ＝⟨ refl ⟩
   (λ x → strip-thunk (f₁ (thunk-type x))) unthunked₂
 ＝⟨ ap (λ z → z unthunked₂) eq₁ ⟩
   unthunked₁ unthunked₂
 ∎

equivalent-nrec-lemma : {n : ℕ} {Γ : Ctx n}
                      → (env : Envᵢ Γ)
                      → (ctr : ℕ)
                      → (base : Term Γ nat)
                      → (f : Term Γ (nat ⇒ nat))
                      → strip-thunk (nat-recᵢ env ctr base f)
                      ＝ (nat-rec (strip-thunk-env env) ctr base f)
equivalent-nrec-lemma env zero base f = equivalent-semantics env base
equivalent-nrec-lemma env (succ ctr) base f
 = application-equality env (env [ f ]ᵢ) (nat-recᵢ env ctr base f)
    (strip-thunk-env env [ f ]ₑ) (nat-rec (strip-thunk-env env) ctr base f)
    (equivalent-semantics env f) (equivalent-nrec-lemma env ctr base f)

equivalent-nrec : {n : ℕ} {Γ : Ctx n}
                → (env : Envᵢ Γ)
                → (ctrᵢ : NatThunk)
                → (ctr : ℕ)
                → (strip-thunk ctrᵢ ＝ ctr)
                → (base : Term Γ nat)
                → (f : Term Γ (nat ⇒ nat))
                → strip-thunk (rec-builder env ctrᵢ base f)
                ＝ nat-rec (strip-thunk-env env) ctr base f
equivalent-nrec env (.0 , return n) .(strip-thunk (0 , return n)) refl base f
 = equivalent-nrec-lemma env n base f
equivalent-nrec env (.(succ _) , (√ y)) ctr x base f
 = equivalent-nrec env (_ , y) ctr x base f

equivalent-semantics env (var v)
 = strip-thunk (increment (lookup-envᵢ v env))
 ＝⟨ (increment-equal-semantics (lookup-envᵢ v env))⁻¹ ⟩
   strip-thunk (lookup-envᵢ v env)
 ＝⟨ γ env v ⟩
   lookup-env v (strip-thunk-env env)
 ∎
 where
  γ : {n : ℕ} {Γ : Ctx n}
    → (env : Envᵢ Γ)
    → (v : Fin n)
    → strip-thunk (lookup-envᵢ v env) ＝ lookup-env v (strip-thunk-env env)
  γ [] ()
  γ (x ∷Eᵢ _) 𝟎 = refl
  γ (_ ∷Eᵢ env) (suc v) = γ env v
equivalent-semantics env zero = refl
equivalent-semantics env (if term then term₁ else term₂)
 = if-then-else-equality env term₁ term₂ (env [ term ]ᵢ)
    ((strip-thunk-env env) [ term ]ₑ) (equivalent-semantics env term)
equivalent-semantics env (suc term) = γ₁ (equivalent-semantics env term)
 where
  γ₀ : {n : ℕ}
     → (th : Thunk n ℕ)
     → force (th >>= (λ x → √ return (succ x))) ＝ succ (force th)
  γ₀ (return x) = refl
  γ₀ (√ th) = γ₀ th

  γ₁ : strip-thunk (env [ term ]ᵢ) ＝ (strip-thunk-env env) [ term ]ₑ
     → strip-thunk (env [ suc term ]ᵢ) ＝ (strip-thunk-env env) [ suc term ]ₑ
  γ₁ eq
   = force (get-thunk (env [ term ]ᵢ) >>= (λ x → √ return (succ x)))
   ＝⟨ γ₀ (get-thunk (env [ term ]ᵢ)) ⟩
     succ (strip-thunk (env [ term ]ᵢ))
   ＝⟨ ap succ eq ⟩
     succ ((strip-thunk-env env) [ term ]ₑ)
   ∎
equivalent-semantics env (term ∙ term₁)
 = application-equality env (env [ term ]ᵢ) (env [ term₁ ]ᵢ)
    ((strip-thunk-env env) [ term ]ₑ) ((strip-thunk-env env) [ term₁ ]ₑ)
    (equivalent-semantics env term) (equivalent-semantics env term₁)
equivalent-semantics env (lam σ term)
 = fe λ y
 → strip-thunk ((thunk-type y ∷Eᵢ env) [ term ]ᵢ)
 ＝⟨ equivalent-semantics (thunk-type y ∷Eᵢ env) term ⟩
   (strip-thunk-env (thunk-type y ∷Eᵢ env)) [ term ]ₑ
 ＝⟨ ap (λ z → (z ∷E strip-thunk-env env) [ term ]ₑ)
      (strip-thunk-is-inverse-of-thunk-type y) ⟩
   (y ∷E (strip-thunk-env env)) [ term ]ₑ
 ∎
equivalent-semantics env (nrec t u v)
 = equivalent-nrec env (env [ t ]ᵢ) ((strip-thunk-env env) [ t ]ₑ)
    (equivalent-semantics env t) u v

\end{code}

Uses the intermediate semantics to produce a time function for a program
- a function that returns the running time of a program given the size of its
input.

For the sake of simplicity, we consider the size of a natural number to be its
value.

\begin{code}

time-function : (Closed (nat ⇒ nat)) → ℕ → ℕ
time-function term n = get-time ((get-function ([] [ term ]ᵢ)) (0 , return n))

\end{code}

Proof that the `double` program is linear time.

To show this, we prove that the time function for double has a time function
that is O(n).

\begin{code}

double-rec : ℕ → ℕ → NatThunk
double-rec x n
 = nat-recᵢ {1} {nat ∷ []} ((0 , return x) ∷Eᵢ []) n zero double-step

double-natrec-lemma : {m₁ m₂ : ℕ} {Γ₁ : Ctx m₁} {Γ₂ : Ctx m₂}
                      {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                    → (n : ℕ)
                    → nat-recᵢ env₁ n zero double-step
                    ＝ nat-recᵢ env₂ n zero double-step
double-natrec-lemma zero = refl
double-natrec-lemma (succ n)
 = ap (λ y → succ (1 + (1 + get-time y))
           , (√ get-thunk y >>= (λ x → √ return (succ x))
                            >>= (λ x → √ return (succ x))))
    (double-natrec-lemma n)

succ^ : ℕ → ℕ → ℕ → ℕ
succ^ zero y n = n + y
succ^ (succ x) y n = 1 + succ^ x y n

double-time : (time-function double) ∈O[ (λ n → n) ]
double-time = big-o (5 , 1 , γ)
 where
  γ₀ : (x : ℕ)
     → 1 ≤ (succ x)
     → succ (get-time (double-rec (succ x) (succ x))) ≤ (5 + 5 * x)
  γ₀ zero ⋆ = ⋆
  γ₀ (succ n) ⋆ = γ₈
   where
    γ₁ : (n : ℕ) → (succ ^ 3) (1 + (1 + n)) ＝ 5 + n
    γ₁ n
     = (succ ^ 3) (1 + (1 + n))
     ＝⟨ ap (succ ^ 3) (+-assoc 1 1 n)⁻¹ ⟩
       (succ ^ 3) (2 + n)
     ＝⟨ refl ⟩
       (succ ^ 2) (2 + n + 1)
     ＝⟨ refl ⟩
       2 + n + 3
     ＝⟨ ap (_+ 3) (+-comm 2 n) ⟩
       n + 2 + 3
     ＝⟨ refl ⟩
       n + 5
     ＝⟨ +-comm n 5 ⟩
       5 + n
     ∎

    γ₂ : (n : ℕ) → 5 + n ≤ 5 + n
    γ₂ n = ≤-refl (5 + n)

    γ₃ : (n : ℕ) → (succ ^ 3) (1 + (1 + n)) ≤ 5 + n
    γ₃ n = transport (λ y → y ≤ 5 + n) ((γ₁ n)⁻¹) (γ₂ n)

    γ₄ : (n m : ℕ) → n ≤ m → (succ ^ 3) (1 + (1 + n)) ≤ 5 + m
    γ₄ n m le
     = ≤-trans ((succ ^ 3) (1 + (1 + n))) (5 + n) (5 + m)
        (γ₃ n) (≤-n-monotone-left n m 5 le)

    γ₅ : (n : ℕ) → n ≤ ((succ ^ 2) n)
    γ₅ n = ≤-trans n (succ n) ((succ ^ 2) n) (≤-succ n) (≤-succ (succ n))

    γ₆ : 1 + (1 + get-time (double-rec (succ n) n)) ≤ 5 * (succ n)
    γ₆ = ≤-trans
          (1 + (1 + get-time (double-rec (succ n) n)))
          (succ^ 2 2 (get-time (double-rec (succ n) n)))
          (5 + 5 * n)
          (γ₅ (1 + (1 + get-time (double-rec (succ n) n))))
          (γ₀ n ⋆)

    γ₇ : 1 + (1 + get-time (double-rec (succ (succ n)) n))
       ＝ 1 + (1 + get-time (double-rec (succ n) n))
    γ₇ = ap ((1 +_) ∘ (1 +_) ∘ get-time) (double-natrec-lemma n)

    γ₈ : succ^ 4 3 (get-time (double-rec (succ (succ n)) n))
       ≤ 5 + (5 + 5 * n)
    γ₈ = γ₄ (1 + (1 + get-time (double-rec (succ (succ n)) n))) (5 + 5 * n)
          (transport (λ z → z ≤ 5 + 5 * n) ((γ₇)⁻¹) γ₆)

  γ : (x : ℕ)
    → 1 ≤ x
    → succ (get-time (double-rec x x)) ≤ (5 * x)
  γ zero ()
  γ (succ n) le = γ₀ n ⋆


\end{code}

Definition of an `is-even` program, which checks if a natural number
is even. It returns 0 if so and 1 otherwise.

\begin{code}

even-step : {n : ℕ} {Γ : Ctx n} → Term Γ (nat ⇒ nat)
even-step = lam nat (if var 𝟎 then suc zero else zero)

is-even : Closed (nat ⇒ nat)
is-even = lam nat (nrec (var 𝟎) zero even-step)

\end{code}

Proof of correctness for `is-even`.

\begin{code}

my-even : ℕ → ℕ
my-even zero = 0
my-even (succ n) = if' my-even n then' 1 else' 0

is-even-env-lemma : {m₁ m₂ : ℕ} {Γ₁ : Ctx m₁} {Γ₂ : Ctx m₂}
                    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                  → (n : ℕ)
                  → nat-rec env₁ n zero even-step
                  ＝ nat-rec env₂ n zero even-step
is-even-env-lemma zero = refl
is-even-env-lemma (succ n)
 = ap (λ z → if' z then' 1 else' 0) (is-even-env-lemma n)

is-even-correctness : (n : ℕ) → ([] [ is-even ]ₑ) n ＝ my-even n
is-even-correctness zero = refl
is-even-correctness (succ n)
 = if' nat-rec (succ n ∷E []) n zero even-step then' 1 else' 0
 ＝⟨ is-even-env-lemma (succ n) ⟩
   if' nat-rec (n ∷E []) n zero even-step then' 1 else' 0
 ＝⟨ ap (λ z → if' z then' 1 else' 0) (is-even-correctness n) ⟩
   if' my-even n then' 1 else' 0
 ∎

\end{code}

Proof that `is-even` is linear time.

\begin{code}

even-if : NatThunk → NatThunk
even-if r = thunk-if r (2 , (√ (√ return 1))) (1 , (√ return 0))

even-rec : ℕ → ℕ → NatThunk
even-rec x n
 = nat-recᵢ {1} {nat ∷ []} ((0 , return x) ∷Eᵢ []) n zero even-step

is-even-natrec-lemma : {m₁ m₂ : ℕ} {Γ₁ : Ctx m₁} {Γ₂ : Ctx m₂}
                       {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                     → (n : ℕ)
                     → nat-recᵢ env₁ n zero even-step
                     ＝ nat-recᵢ env₂ n zero even-step
is-even-natrec-lemma zero = refl
is-even-natrec-lemma (succ n)
 = ap (λ x → succ (get-time (even-if x)) , (√ get-thunk (even-if x)))
    (is-even-natrec-lemma n)

nat-rec<2 : {m : ℕ} {Γ : Ctx m} {env : Env Γ}
          → (n : ℕ)
          → nat-rec env n zero even-step < 2
nat-rec<2 zero = ⋆
nat-rec<2 (succ n) = γ (nat-rec _ n zero even-step) (nat-rec<2 n)
 where
  γ : (n : ℕ) → (n < 2) → (if' n then' 1 else' 0) < 2
  γ zero le = ⋆
  γ (succ zero) le = ⋆
  γ (succ (succ n)) ()

is-even-time : (time-function is-even) ∈O[ (λ n → n) ]
is-even-time = big-o (6 , 1 , γ)
 where
  γ₀ : (n : ℕ)
     → 1 ≤ (succ n)
     → succ (get-time (even-rec (succ n) (succ n))) ≤ (6 * (succ n))
  γ₀ zero ⋆ = ⋆
  γ₀ (succ n) ⋆ = goal
   where
    IH : (succ ^ 2) (get-time (even-if (even-rec (succ n) n))) ≤ (6 + 6 * n)
    IH = γ₀ n ⋆

    γ₁ : (succ ^ 2) (get-time (even-if (even-rec (succ n) n))) ≤ (6 * n + 6)
    γ₁ = transport (λ y → (succ ^ 2) (get-time (even-if (even-rec (succ n) n)))
                        ≤ y)
          (+-comm 6 (6 * n)) IH

    γ₂ : (n : ℕ)
       → (n < 2)
       → if' if' n then' 1 else' 0 then' 1 else' 0 ＝ n
    γ₂ zero le = refl
    γ₂ (succ zero) le = refl
    γ₂ (succ (succ n)) ()

    γ₃ : (n : ℕ)
       → strip-thunk (even-if (even-rec (succ (succ (succ n))) (succ (succ n))))
       ＝ strip-thunk (even-if (even-rec (succ n) n))
    γ₃ n
     = strip-thunk (even-if (even-rec (succ (succ (succ n))) (succ (succ n))))
     ＝⟨ ap (λ y → strip-thunk (even-if y))
          (is-even-natrec-lemma (succ (succ n))) ⟩
       strip-thunk (even-if (nat-recᵢ [] (succ (succ n)) zero even-step))
     ＝⟨ if-then-else-equality [] (suc zero) zero
          (nat-recᵢ [] (succ (succ n)) zero even-step)
          (nat-rec [] (succ (succ n)) zero even-step)
          (equivalent-nrec-lemma [] (succ (succ n)) zero even-step) ⟩
       if' (nat-rec [] (succ (succ n)) zero even-step) then' 1 else' 0
     ＝⟨ ap (λ y → if' y then' 1 else' 0)
          (γ₂ (nat-rec [] n zero even-step) (nat-rec<2 n)) ⟩
       if' (nat-rec [] n zero even-step) then' 1 else' 0
     ＝⟨ (if-then-else-equality [] (suc zero) zero
           (nat-recᵢ [] n zero even-step)
           (nat-rec [] n zero even-step)
           (equivalent-nrec-lemma [] n zero even-step))⁻¹ ⟩
       strip-thunk (even-if (nat-recᵢ [] n zero even-step))
     ＝⟨ ap (λ y → strip-thunk (even-if y)) (is-even-natrec-lemma n)⁻¹ ⟩
       strip-thunk (even-if (even-rec (succ n) n))
     ∎

    γ₄ : (n : ℕ) → strip-thunk (even-if (even-rec (succ n) n)) < 2
    γ₄ zero = ⋆
    γ₄ (succ zero) = ⋆
    γ₄ (succ (succ n)) = transport (λ z → z < 2) ((γ₃ n)⁻¹) (γ₄ n)

    γ₅ : (x@(x' , t) : NatThunk) → force t < 2 → get-time (even-if x) ≤ x' + 3
    γ₅ (.0 , return zero) le = ⋆
    γ₅ (.0 , return 1) le = ⋆
    γ₅ (.0 , return (succ (succ x₁))) ()
    γ₅ (.(succ _) , (√ x)) le = γ₅ (_ , x) le

    γ₆ : get-time (even-if (even-if (even-rec (succ n) n)))
       ≤ get-time (even-if (even-rec (succ n) n)) + 3
    γ₆ = γ₅ (even-if (even-rec (succ n) n)) (γ₄ n)

    γ₇ : get-time (even-if (even-if (even-rec (succ n) n))) ≤ 6 * n + 7
    γ₇ = ≤-trans
          (get-time (even-if (even-if (even-rec (succ n) n))))
          (get-time (even-if (even-rec (succ n) n)) + 3)
          (6 * n + 7)
          γ₆ γ₁

    γ₈ : 3 + (6 + 6 * n) ＝ 6 * n + 9
    γ₈ = 3 + (6 + 6 * n)
       ＝⟨ (+-assoc 3 6 (6 * n))⁻¹ ⟩
         9 + 6 * n
       ＝⟨ +-comm 9 (6 * n) ⟩
         6 * n + 9
       ∎

    γ₉ : get-time (even-if (even-if (even-rec (succ n) n))) ≤ (3 + (6 + 6 * n))
    γ₉ = ≤-trans
          (get-time (even-if (even-if (even-rec (succ n) n))))
          (6 * n + 7)
          (3 + (6 + 6 * n))
          γ₇
          (transport (λ z → 6 * n + 7 ≤ z) ((γ₈)⁻¹)
           ((≤-n-monotone-left 0 2 (6 * n) ⋆)))

    γ₁₀ : 3 + (6 + 6 * n) + 3 ＝ 6 + (6 + 6 * n)
    γ₁₀ = 3 + (6 + 6 * n) + 3
        ＝⟨ +-comm (3 + (6 + 6 * n)) 3 ⟩
          3 + (3 + (6 + 6 * n))
        ＝⟨ (+-assoc 3 3 (6 + 6 * n))⁻¹ ⟩
          6 + (6 + 6 * n)
        ∎

    γ₁₁ : get-time (even-if (even-if (even-rec (succ n) n))) + 3
        ≤ (6 + (6 + 6 * n))
    γ₁₁ = transport
           (λ z → get-time (even-if (even-if (even-rec (succ n) n))) + 3 ≤ z)
           γ₁₀ γ₉

    goal : (succ ^ 3)
            (get-time (even-if (even-if (even-rec (succ (succ n)) n))))
         ≤ (6 + (6 + 6 * n))
    goal = transport
            (λ y → (succ ^ 3) (get-time (even-if (even-if y)))
                 ≤ 6 + (6 + 6 * n))
            (is-even-natrec-lemma n) γ₁₁

  γ : (n : ℕ)
    → 1 ≤ n
    → succ (get-time (even-rec n n)) ≤ (6 * n)
  γ zero ()
  γ (succ n) ⋆ = γ₀ n ⋆

\end{code}
