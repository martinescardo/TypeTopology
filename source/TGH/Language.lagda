Theo Hepburn, started January 2025.

Contains the full version of our language with natural numbers and lists of
natural numbers as the available basic types.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.Language (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin hiding (pred)
open import MLTT.List
open import UF.Base
open import TGH.Thunk

\end{code}

We extent our type system to add lists as a basic type.
All lists in this language are lists of natural numbers.

\begin{code}


infixr 30 _⇒_
data LType : 𝓤₀ ̇  where
 nat : LType
 list : LType
 _⇒_ : LType → LType → LType

Ctx : ℕ → 𝓤₀ ̇
Ctx = Vec LType

\end{code}

We add additional constructors to the Term type family to allow us to construct
and perform operations on lists.

`nil and cons` are the constructors for lists.

`lrec` provides recursion on lists, allowing the contents of lists to be read.

`pred` is an additional constructor for natural numbers.

\begin{code}

infixl 20 _∙_
data Term {n : ℕ} (Γ : Ctx n) : LType → 𝓤₀ ̇  where
 var : (v : Fin n) → Term Γ (Γ !! v)
 zero : Term Γ nat
 suc : Term Γ nat → Term Γ nat
 pred : Term Γ nat → Term Γ nat
 nil : Term Γ list
 cons : Term Γ nat → Term Γ list → Term Γ list
 if_then_else_ : {σ : LType} → Term Γ nat → Term Γ σ → Term Γ σ → Term Γ σ
 _∙_ : {σ τ : LType} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
 lam : (σ : LType) {τ : LType} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
 nrec : {σ : LType} → Term Γ nat → Term Γ σ → Term Γ (σ ⇒ σ) → Term Γ σ
 lrec : {σ : LType} → Term Γ list → Term Γ σ → Term Γ (σ ⇒ nat ⇒ σ) → Term Γ σ

Closed : LType → 𝓤₀ ̇
Closed = Term []

\end{code}

We expand our translation to include list types.

\begin{code}

⟦_⟧ : LType → 𝓤₀ ̇
⟦ nat ⟧ = ℕ
⟦ list ⟧ = List ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷E_
data Env : {n : ℕ} → Ctx n → 𝓤₀ ̇  where
 [] : Env []
 _∷E_ : {n : ℕ} {Γ : Ctx n } {τ : LType} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookup-env : {n : ℕ} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ Γ !! m ⟧
lookup-env 𝟎 (x ∷E _) = x
lookup-env (suc m) (x ∷E env) = lookup-env m env

if'_then'_else'_ : {X : 𝓤₀ ̇ } → ℕ → X → X → X
if' zero then' x else' y = x
if' succ _ then' x else' y = y

\end{code}

Natural number recursion and list recursion.

\begin{code}

nat-rec : {n : ℕ} {σ : LType} {Γ : Ctx n}
        → Env Γ
        → (m : ℕ)
        → (base : Term Γ σ)
        → (f : Term Γ (σ ⇒ σ))
        → ⟦ σ ⟧

list-rec : {σ : LType} {n : ℕ} {Γ : Ctx n}
         → Env Γ
         → (l : List ℕ)
         → (base : Term Γ σ)
         → (f : Term Γ (σ ⇒ nat ⇒ σ))
         → ⟦ σ ⟧

\end{code}

Normal semantics of the full language.

\begin{code}

_[_]ₑ : {n : ℕ} {Γ : Ctx n} {τ : LType} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v ]ₑ = lookup-env v env
env [ zero ]ₑ = zero
env [ suc t ]ₑ = succ (env [ t ]ₑ)
env [ pred t ]ₑ = pred' (env [ t ]ₑ)
env [ nil ]ₑ = []
env [ cons t l ]ₑ = (env [ t ]ₑ) ∷ (env [ l ]ₑ)
env [ if t then u else v ]ₑ
 = if' (env [ t ]ₑ) then' (env [ u ]ₑ) else' (env [ v ]ₑ)
env [ t ∙ u ]ₑ = (env [ t ]ₑ) (env [ u ]ₑ)
env [ lam _ t ]ₑ = λ x → (x ∷E env) [ t ]ₑ
env [ nrec t u v ]ₑ = nat-rec env (env [ t ]ₑ) u v
env [ lrec t u v ]ₑ = list-rec env (env [ t ]ₑ) u v

nat-rec env zero base f = env [ base ]ₑ
nat-rec env (succ m) base f = (env [ f ]ₑ) (nat-rec env m base f)

list-rec env [] base f = env [ base ]ₑ
list-rec env (x ∷ l) base f = (env [ f ]ₑ) (list-rec env l base f) x

\end{code}

Once again, in the intermediate semantics we have a different corresponding
Agda type for each `LType`, so we define a new type translation, this time
with list types too. Once again we use the `Thunk` monad.

\begin{code}

⟦_⟧ᵢ : LType → 𝓤₀ ̇

thunk-type : {σ : LType} → ⟦ σ ⟧ → ⟦ σ ⟧ᵢ

strip-thunk : {σ : LType} → ⟦ σ ⟧ᵢ → ⟦ σ ⟧

value-time-independent : {σ τ : LType} → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → 𝓤₀ ̇
value-time-independent {σ} f
 = (x y : ⟦ σ ⟧ᵢ)
 → strip-thunk x ＝ strip-thunk y
 → strip-thunk (f x) ＝ strip-thunk (f y)

⟦ nat ⟧ᵢ = Σ t ꞉ ℕ , Thunk t ℕ
⟦ list ⟧ᵢ = Σ t ꞉ ℕ , Thunk t (List ℕ)
⟦ σ ⇒ τ ⟧ᵢ = Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f

thunk-type {nat} x = 0 , return x
thunk-type {list} l = 0 , return l
thunk-type {σ ⇒ σ₁} f = (λ x → thunk-type (f (strip-thunk x))) , γ f
 where
  γ : {σ σ₁ : LType} (f : ⟦ σ ⟧ → ⟦ σ₁ ⟧)
    → (x y : ⟦ σ ⟧ᵢ)
    → strip-thunk x ＝ strip-thunk y
    → strip-thunk (thunk-type (f (strip-thunk x)))
    ＝ strip-thunk (thunk-type (f (strip-thunk y)))
  γ {_} {_} f x y eq = ap (strip-thunk ∘ thunk-type ∘ f) eq

strip-thunk {nat} (_ , n) = force n
strip-thunk {list} (_ , l) = force l
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
strip-thunk-is-inverse-of-thunk-type {list} l = refl
strip-thunk-is-inverse-of-thunk-type {σ ⇒ τ} f
 = fe (strip-thunk-is-inverse-of-thunk-lemma f)

infixr 5 _∷Eᵢ_
data Envᵢ : {n : ℕ} → Ctx n → 𝓤₀ ̇  where
 [] : Envᵢ []
 _∷Eᵢ_ : {n : ℕ} {Γ : Ctx n } {τ : LType} → ⟦ τ ⟧ᵢ → Envᵢ Γ → Envᵢ (τ ∷ Γ)

strip-thunk-env : {n : ℕ} {Γ : Ctx n } → Envᵢ Γ → Env Γ
strip-thunk-env [] = []
strip-thunk-env (x ∷Eᵢ xs) = strip-thunk x ∷E (strip-thunk-env xs)

lookup-envᵢ : {n : ℕ} {Γ : Ctx n} (m : Fin n) → Envᵢ Γ → ⟦ Γ !! m ⟧ᵢ
lookup-envᵢ 𝟎 (x ∷Eᵢ _) = x
lookup-envᵢ (suc m) (x ∷Eᵢ env) = lookup-envᵢ m env

inc-function : {σ τ : LType} → (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ

strip-thunk-thunk-type-rearrange : {τ σ : LType}
                                 → (f : ⟦ τ ⇒ σ ⟧ᵢ)
                                 → (z : ⟦ τ ⟧)
                                 → strip-thunk ((pr₁ f) (thunk-type z))
                                 ＝ (strip-thunk f) z
strip-thunk-thunk-type-rearrange f z = refl

inc-eq : {σ τ : LType}
       → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
       → value-time-independent f
       → (x y : ⟦ σ ⟧ᵢ)
       → strip-thunk x ＝ strip-thunk y
       → strip-thunk (inc-function f x) ＝ strip-thunk (inc-function f y)

inc-nat : Σ t ꞉ ℕ , Thunk t ℕ → Σ t ꞉ ℕ , Thunk t ℕ
inc-nat (n , x) = succ n , (√ x)

inc-list : Σ t ꞉ ℕ , Thunk t (List ℕ) → Σ t ꞉ ℕ , Thunk t (List ℕ)
inc-list (n , x) = succ n , (√ x)

inc-function {_} {nat} f x = inc-nat (f x)
inc-function {_} {list} f l = inc-list (f l)
inc-function {σ₁} {σ ⇒ τ} f x = inc-function (pr₁ (f x))
                              , inc-eq (pr₁ (f x)) (pr₂ (f x))

change-function : {σ τ : LType}
                → (f : (Σ f' ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f'))
                → (g : (Σ g' ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent g'))
                → strip-thunk {σ ⇒ τ} f ＝ strip-thunk {σ ⇒ τ} g
                → (λ x → strip-thunk (inc-function (pr₁ f) (thunk-type x)))
                ＝ (λ x → strip-thunk (inc-function (pr₁ g) (thunk-type x)))
change-function {σ} {nat} _ _ eq = eq
change-function {σ} {list} _ _ eq = eq
change-function {σ} {τ ⇒ τ₁} f g eq
 = fe λ x
 → change-function (pr₁ f (thunk-type x)) (pr₁ g (thunk-type x))
    (ap (λ w → w x) eq)

inc-eq {_} {nat} f value-time-ind = value-time-ind
inc-eq {_} {list} f value-time-ind = value-time-ind
inc-eq {σ₁} {σ ⇒ τ} f value-time-ind x y eq
 = change-function (f x) (f y) (value-time-ind x y eq)

increment : {τ : LType} → ⟦ τ ⟧ᵢ → ⟦ τ ⟧ᵢ
increment {nat} = inc-nat
increment {list} = inc-list
increment {τ ⇒ σ} (f , eqt) = inc-function f , inc-eq f eqt

increment-equal-semantics : {τ : LType} {x : ⟦ τ ⟧ᵢ}
                          → strip-thunk x ＝ strip-thunk (increment x)
increment-equal-semantics {nat} {x} = refl
increment-equal-semantics {list} {l} = refl
increment-equal-semantics {σ ⇒ τ} {f , eqt} = fe λ x → γ₂ (thunk-type x)
 where
  γ₁ : {σ τ : LType}
     → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
     → (y : ⟦ σ ⟧ᵢ)
     → strip-thunk (increment (f y)) ＝ strip-thunk (inc-function f y)
  γ₁ {σ} {nat} f y = refl
  γ₁ {σ} {list} f y = refl
  γ₁ {σ} {τ ⇒ τ₁} f y = refl

  γ₂ : (y : ⟦ σ ⟧ᵢ) → strip-thunk (f y) ＝ strip-thunk (inc-function f y)
  γ₂ y
   = strip-thunk (f y)
   ＝⟨ increment-equal-semantics ⟩
     strip-thunk (increment (f y))
   ＝⟨ γ₁ f y ⟩
     strip-thunk (inc-function f y)
   ∎

thunk-if : {σ : LType}
         → (Σ n₁ ꞉ ℕ , Thunk n₁ ℕ)
         → ⟦ σ ⟧ᵢ → ⟦ σ ⟧ᵢ → ⟦ σ ⟧ᵢ
thunk-if (zero , return zero) l r = increment l
thunk-if (zero , return (succ _)) l r = increment r
thunk-if (succ n₁ , (√ t)) u v = increment (thunk-if (n₁ , t) u v)

\end{code}

Natural number and list recursion with Thunked types.

We also add an option in the semantics. We can evaluate the semantics of
expressions using an eager evaluation strategy or a lazy evaluation strategy,
and this will model the step count for either.

\begin{code}

nat-recᵢ : {σ : LType} {n : ℕ} {Γ : Ctx n}
         → Envᵢ Γ
         → (m : ℕ)
         → (base : Term Γ σ)
         → (f : Term Γ (σ ⇒ σ))
         → (strategy : Strategy)
         → ⟦ σ ⟧ᵢ

nat-rec-builder : {σ : LType} {n : ℕ} {Γ : Ctx n}
                → Envᵢ Γ
                → Σ t ꞉ ℕ , Thunk t ℕ
                → (base : Term Γ σ)
                → (f : Term Γ (σ ⇒ σ))
                → (strategy : Strategy)
                → ⟦ σ ⟧ᵢ

list-recᵢ : {σ : LType} {n : ℕ} {Γ : Ctx n}
          → Envᵢ Γ
          → List ℕ
          → (base : Term Γ σ)
          → (f : Term Γ (σ ⇒ nat ⇒ σ))
          → (strategy : Strategy)
          → ⟦ σ ⟧ᵢ

list-rec-builder : {σ : LType} {n : ℕ} {Γ : Ctx n}
                 → Envᵢ Γ
                 → Σ t ꞉ ℕ , Thunk t (List ℕ)
                 → (base : Term Γ σ)
                 → (f : Term Γ (σ ⇒ nat ⇒ σ))
                 → (strategy : Strategy)
                 → ⟦ σ ⟧ᵢ


\end{code}

Intermediate semantics.

Loading variables and constants (`zero` and `nil`) is defined as taking one
step.

Calling the `suc`, `pred` or `cons` primitive takes 1 step.

An `if_then_else_` statement takes 1 step.

Application of a function, list recursion, and natural number recursion
do not add any steps themselves, but they must use the above features,
which add steps.

\begin{code}

_[_]ᵢ_ : {n : ℕ} {Γ : Ctx n} {τ : LType}
       → Envᵢ Γ → Term Γ τ → Strategy → ⟦ τ ⟧ᵢ

equivalent-semantics : {n : ℕ} {σ : LType} {Γ : Ctx n}
                     → (env : Envᵢ Γ)
                     → (term : Term Γ σ)
                     → (strategy : Strategy)
                     → strip-thunk (env [ term ]ᵢ strategy)
                     ＝ (strip-thunk-env env) [ term ]ₑ

\end{code}

We must use different helper functions to evaluate the intermediate semantics
depending on whether we are modeling an eager or lazy evaluation strategy.

In the lazy evaluation strategy, we evaluate function arguments when they
are used in the function. This means that any steps assocaiated with the
argument will be added on each time the argument is used. If an argument is
used twice in a function, the associated number of steps will be added on twice
to the running time. However, if an argument is not used at all, the number of
steps will not be added on.

In the eager evaluation strategy, we evaluate function arguments when the
function is called. Therefore, the number of steps associated with each
argument will only ever be added on once.

\begin{code}

lazy-function : {σ τ : LType} {n : ℕ} {Γ : Ctx n}
              → Envᵢ Γ
              → Term (σ ∷ Γ) τ
              → (strategy : Strategy)
              → Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f
lazy-function env t s
 = (λ x → (x ∷Eᵢ env) [ t ]ᵢ s)
 , λ x y eq
 → strip-thunk ((x ∷Eᵢ env) [ t ]ᵢ s)
 ＝⟨ equivalent-semantics (x ∷Eᵢ env) t s ⟩
   ((strip-thunk x) ∷E (strip-thunk-env env)) [ t ]ₑ
 ＝⟨ ap (λ z → (z ∷E strip-thunk-env env) [ t ]ₑ) eq ⟩
   (((strip-thunk y) ∷E (strip-thunk-env env)) [ t ]ₑ)
 ＝⟨ (equivalent-semantics (y ∷Eᵢ env) t s)⁻¹ ⟩
   strip-thunk ((y ∷Eᵢ env) [ t ]ᵢ s)
 ∎

eager-function-nat-helper : {τ : LType} {n : ℕ} {Γ : Ctx n}
                          → Envᵢ Γ
                          → Term (nat ∷ Γ) τ
                          → Σ t ꞉ ℕ , Thunk t ℕ
                          → ⟦ τ ⟧ᵢ
eager-function-nat-helper env t x@(zero , return _)
 = (x ∷Eᵢ env) [ t ]ᵢ eager
eager-function-nat-helper env t (succ n , (√ x))
 = increment (eager-function-nat-helper env t (n , x))

eager-function-list-helper : {τ : LType} {n : ℕ} {Γ : Ctx n}
                           → Envᵢ Γ
                           → Term (list ∷ Γ) τ
                           → Σ t ꞉ ℕ , Thunk t (List ℕ)
                           → ⟦ τ ⟧ᵢ
eager-function-list-helper env t x@(zero , return _)
 = (x ∷Eᵢ env) [ t ]ᵢ eager
eager-function-list-helper env t (succ n , (√ x))
 = increment (eager-function-list-helper env t (n , x))

eager-function-nat : {τ : LType} {n : ℕ} {Γ : Ctx n}
                   → Envᵢ Γ
                   → Term (nat ∷ Γ) τ
                   → Σ f ꞉ (Σ t ꞉ ℕ , Thunk t ℕ → ⟦ τ ⟧ᵢ)
                   , value-time-independent f
eager-function-nat env t = (eager-function-nat-helper env t) , γ₀
 where
  γ₀ : (x y : Σ (λ t₁ → Thunk' ℕ t₁))
     → force (pr₂ x) ＝ force (pr₂ y)
     → strip-thunk (eager-function-nat-helper env t x)
     ＝ strip-thunk (eager-function-nat-helper env t y)
  γ₀ (.0 , return .(force (return x))) (zero , return x) refl = refl
  γ₀ (.0 , return .(force x)) (succ n , (√ x)) refl
   = strip-thunk (((0 , return (force x)) ∷Eᵢ env) [ t ]ᵢ eager)
   ＝⟨ γ₀ (0 , return (force x)) (_ , x) refl ⟩
     strip-thunk (eager-function-nat-helper env t (n , x))
   ＝⟨ increment-equal-semantics ⟩
     strip-thunk (increment (eager-function-nat-helper env t (n , x)))
   ∎
  γ₀ (.(succ _) , (√ x)) (zero , return .(force x)) refl
   = strip-thunk (increment (eager-function-nat-helper env t (_ , x)))
   ＝⟨ (increment-equal-semantics)⁻¹ ⟩
     strip-thunk (eager-function-nat-helper env t (_ , x))
   ＝⟨ γ₀ (_ , x) (0 , return (force x)) refl ⟩
     strip-thunk (((0 , return (force x)) ∷Eᵢ env) [ t ]ᵢ eager)
   ∎
  γ₀ (.(succ _) , (√ x)) (succ _ , (√ y)) eq
   = strip-thunk (increment (eager-function-nat-helper env t (_ , x)))
   ＝⟨ (increment-equal-semantics)⁻¹ ⟩
     strip-thunk (eager-function-nat-helper env t (_ , x))
   ＝⟨ γ₀ (_ , x) (_ , y) eq ⟩
     strip-thunk (eager-function-nat-helper env t (_ , y))
   ＝⟨ increment-equal-semantics ⟩
     strip-thunk (increment (eager-function-nat-helper env t (_ , y)))
   ∎

eager-function-list : {τ : LType} {n : ℕ} {Γ : Ctx n}
                    → Envᵢ Γ
                    → Term (list ∷ Γ) τ
                    → Σ f ꞉ (Σ t ꞉ ℕ , Thunk t (List ℕ) → ⟦ τ ⟧ᵢ)
                    , value-time-independent f
eager-function-list env t = (eager-function-list-helper env t) , γ₀
 where
  γ₀ : (l₁ l₂ : Σ t ꞉ ℕ , Thunk t (List ℕ))
     → force (pr₂ l₁) ＝ force (pr₂ l₂)
     → strip-thunk (eager-function-list-helper env t l₁)
     ＝ strip-thunk (eager-function-list-helper env t l₂)
  γ₀ (.0 , return .(force (return x))) (zero , return x) refl = refl
  γ₀ (.0 , return .(force x)) (succ n , (√ x)) refl
   = strip-thunk (((0 , return (force x)) ∷Eᵢ env) [ t ]ᵢ eager)
   ＝⟨ γ₀ (0 , return (force x)) (_ , x) refl ⟩
     strip-thunk (eager-function-list-helper env t (n , x))
   ＝⟨ increment-equal-semantics ⟩
     strip-thunk (increment (eager-function-list-helper env t (n , x)))
   ∎
  γ₀ (.(succ _) , (√ x)) (zero , return .(force x)) refl
   = strip-thunk (increment (eager-function-list-helper env t (_ , x)))
   ＝⟨ (increment-equal-semantics)⁻¹ ⟩
     strip-thunk (eager-function-list-helper env t (_ , x))
   ＝⟨ γ₀ (_ , x) (0 , return (force x)) refl ⟩
     strip-thunk (((0 , return (force x)) ∷Eᵢ env) [ t ]ᵢ eager)
   ∎
  γ₀ (.(succ _) , (√ x)) (succ _ , (√ y)) eq
   = strip-thunk (increment (eager-function-list-helper env t (_ , x)))
   ＝⟨ (increment-equal-semantics)⁻¹ ⟩
     strip-thunk (eager-function-list-helper env t (_ , x))
   ＝⟨ γ₀ (_ , x) (_ , y) eq ⟩
     strip-thunk (eager-function-list-helper env t (_ , y))
   ＝⟨ increment-equal-semantics ⟩
     strip-thunk (increment (eager-function-list-helper env t (_ , y)))
   ∎

thunk-cons : Σ t ꞉ ℕ , Thunk t ℕ
           → Σ t ꞉ ℕ , Thunk t (List ℕ)
           → Σ t ꞉ ℕ , Thunk t (List ℕ)
thunk-cons (zero , return x) (n , thl)
 = 1 + n , (thl >>= λ l → √ return (x ∷ l))
thunk-cons (succ _ , (√ x)) l = inc-list (thunk-cons (_ , x) l)

env [ var v ]ᵢ _ = increment (lookup-envᵢ v env)
env [ zero ]ᵢ _ = 1 , (√ return zero) --0 , return zero --
env [ suc t ]ᵢ s = γ (env [ t ]ᵢ s)
 where
  γ : Σ t ꞉ ℕ , Thunk t ℕ → Σ t ꞉ ℕ , Thunk t ℕ
  γ (n , t) = 1 + n , (t >>= λ x → √ return (succ x))
env [ pred t ]ᵢ s = γ (env [ t ]ᵢ s)
 where
  γ : Σ t ꞉ ℕ , Thunk t ℕ → Σ t ꞉ ℕ , Thunk t ℕ
  γ (n , th) = 1 + n , (th >>= λ x → √ return (pred' x))
env [ nil ]ᵢ _ = (1 , (√ return []))
env [ cons t u ]ᵢ s = thunk-cons (env [ t ]ᵢ s) (env [ u ]ᵢ s)
env [ if t then u else v ]ᵢ s
 = thunk-if (env [ t ]ᵢ s) (env [ u ]ᵢ s) (env [ v ]ᵢ s)
env [ t ∙ u ]ᵢ s = (pr₁ (env [ t ]ᵢ s)) (env [ u ]ᵢ s)
env [ lam σ t ]ᵢ lazy = lazy-function env t lazy
env [ lam nat t ]ᵢ eager = eager-function-nat env t
env [ lam list t ]ᵢ eager = eager-function-list env t
env [ lam (σ ⇒ σ₁) t ]ᵢ eager = lazy-function env t eager
env [ nrec t u v ]ᵢ s = nat-rec-builder env (env [ t ]ᵢ s) u v s
env [ lrec t u v ]ᵢ s = list-rec-builder env (env [ t ]ᵢ s) u v s

nat-rec-builder env (zero , return x) u v s = nat-recᵢ env x u v s
nat-rec-builder env (succ _ , (√ x)) u v s
 = increment (nat-rec-builder env (_ , x) u v s)

nat-recᵢ env zero base f s = env [ base ]ᵢ s
nat-recᵢ env (succ n) base f s
 = (pr₁ (env [ f ]ᵢ s)) (nat-recᵢ env n base f s)

list-rec-builder env (zero , return l) u v s = list-recᵢ env l u v s
list-rec-builder env (succ _ , (√ l)) u v s
 = increment (list-rec-builder env (_ , l) u v s)

list-recᵢ env [] base f s = env [ base ]ᵢ s
list-recᵢ env (x ∷ l) base f s
 = (pr₁ ((pr₁ (env [ f ]ᵢ s)) (list-recᵢ env l base f s))) (0 , return x)

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
 = eqt thunked (thunk-type unthunked)
    (strip-thunk thunked
    ＝⟨ eq ⟩
     unthunked
    ＝⟨ (strip-thunk-is-inverse-of-thunk-type unthunked)⁻¹ ⟩
     strip-thunk (thunk-type unthunked)
    ∎)

\end{code}

Proof that the normal and intermediate semantics are equivalent with respect
to values. This means that the intermediate semantics correctly encapsulate the
normal semantics, and we can therefore use them to reason about the running
times of programs for which we have proved correctness using the normal
semantics.

\begin{code}

if-then-else-equality : {σ : LType} {n : ℕ} {Γ : Ctx n}
                      → (env : Envᵢ Γ)
                      → (term₁ : Term Γ σ)
                      → (term₂ : Term Γ σ)
                      → (thunked : Σ t ꞉ ℕ , Thunk t ℕ)
                      → (not-thunked : ℕ)
                      → (force (pr₂ thunked)) ＝ not-thunked
                      → (strategy : Strategy)
                      → strip-thunk (thunk-if thunked (env [ term₁ ]ᵢ strategy)
                         (env [ term₂ ]ᵢ strategy))
                      ＝ if' not-thunked then' ((strip-thunk-env env) [ term₁ ]ₑ)
                         else' ((strip-thunk-env env) [ term₂ ]ₑ)
if-then-else-equality env term₁ term₂ (_ , return zero) (succ _) () _
if-then-else-equality env term₁ term₂ (_ , return (succ _)) zero () _
if-then-else-equality env term₁ term₂ (.0 , return zero) zero refl s
 = strip-thunk (increment (env [ term₁ ]ᵢ s))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (env [ term₁ ]ᵢ s)
 ＝⟨ equivalent-semantics env term₁ s ⟩
   strip-thunk-env env [ term₁ ]ₑ
 ∎
if-then-else-equality env term₁ term₂ (.(succ _) , (√ t)) zero x s
 = strip-thunk
    (increment (thunk-if (_ , t) (env [ term₁ ]ᵢ s) (env [ term₂ ]ᵢ s)))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (thunk-if (_ , t) (env [ term₁ ]ᵢ s) (env [ term₂ ]ᵢ s))
 ＝⟨ if-then-else-equality env term₁ term₂ (_ , t) zero x s ⟩
   strip-thunk-env env [ term₁ ]ₑ
 ∎
if-then-else-equality env term₁ term₂ (.0 , return (succ _)) (succ _) refl s
 = strip-thunk (increment (env [ term₂ ]ᵢ s))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (env [ term₂ ]ᵢ s)
 ＝⟨ equivalent-semantics env term₂ s ⟩
   strip-thunk-env env [ term₂ ]ₑ
 ∎
if-then-else-equality env term₁ term₂ (.(succ _) , (√ t)) (succ not-thunked) x s
 = strip-thunk
    (increment (thunk-if (_ , t) (env [ term₁ ]ᵢ s) (env [ term₂ ]ᵢ s)))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (thunk-if (_ , t) (env [ term₁ ]ᵢ s) (env [ term₂ ]ᵢ s))
 ＝⟨ if-then-else-equality env term₁ term₂ (_ , t) _ x s ⟩
   strip-thunk-env env [ term₂ ]ₑ
 ∎

application-equality : {n : ℕ} {Γ : Ctx n} {σ τ : LType}
                     → (env : Envᵢ Γ)
                     → (thunked₁ : Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
                                 , value-time-independent f)
                     → (thunked₂ : ⟦ σ ⟧ᵢ)
                     → (unthunked₁ : ⟦ σ ⟧ → ⟦ τ ⟧)
                     → (unthunked₂ : ⟦ σ ⟧)
                     → strip-thunk thunked₁ ＝ unthunked₁
                     → strip-thunk thunked₂ ＝ unthunked₂
                     → strip-thunk ((pr₁ thunked₁) thunked₂)
                     ＝ unthunked₁ unthunked₂
application-equality env (f₁ , eqt) thunked₂ unthunked₁ unthunked₂ eq₁ eq₂
 = strip-thunk (f₁ thunked₂)
 ＝⟨ strip-thunk-thunk-type-lemma f₁ eqt thunked₂ unthunked₂ eq₂ ⟩
   strip-thunk (f₁ (thunk-type unthunked₂))
 ＝⟨ refl ⟩
   (λ x → strip-thunk (f₁ (thunk-type x))) unthunked₂
 ＝⟨ ap (λ z → z unthunked₂) eq₁ ⟩
   unthunked₁ unthunked₂
 ∎

equivalent-nrec-lemma : {σ : LType} {n : ℕ} {Γ : Ctx n}
                      → (env : Envᵢ Γ)
                      → (ctr : ℕ)
                      → (base : Term Γ σ)
                      → (f : Term Γ (σ ⇒ σ))
                      → (strategy : Strategy)
                      → strip-thunk (nat-recᵢ env ctr base f strategy)
                      ＝ nat-rec (strip-thunk-env env) ctr base f
equivalent-nrec-lemma env zero base f s = equivalent-semantics env base s
equivalent-nrec-lemma env (succ ctr) base f s
 = application-equality env (env [ f ]ᵢ s) (nat-recᵢ env ctr base f s)
    (strip-thunk-env env [ f ]ₑ) (nat-rec (strip-thunk-env env) ctr base f)
    (equivalent-semantics env f s) (equivalent-nrec-lemma env ctr base f s)

equivalent-nrec : {σ : LType} {n : ℕ} {Γ : Ctx n}
                → (env : Envᵢ Γ)
                → (ctrᵢ : Σ t ꞉ ℕ , Thunk t ℕ)
                → (ctr : ℕ)
                → (strip-thunk ctrᵢ ＝ ctr)
                → (base : Term Γ σ) (f : Term Γ (σ ⇒ σ))
                → (strategy : Strategy)
                → strip-thunk (nat-rec-builder env ctrᵢ base f strategy)
                ＝ nat-rec (strip-thunk-env env) ctr base f
equivalent-nrec env (.0 , return n) .(strip-thunk (0 , return n)) refl base f s
 = equivalent-nrec-lemma env n base f s
equivalent-nrec env (.(succ _) , (√ y)) ctr x base f s
 = strip-thunk (increment (nat-rec-builder env (_ , y) base f s))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (nat-rec-builder env (_ , y) base f s)
 ＝⟨ equivalent-nrec env (_ , y) ctr x base f s ⟩
   nat-rec (strip-thunk-env env) ctr base f
 ∎

equivalent-thunk-cons : (xᵢ : Σ t ꞉ ℕ , Thunk t ℕ)
                      → (lᵢ : Σ t ꞉ ℕ , Thunk t (List ℕ))
                      → {x : ℕ} {l : List ℕ}
                      → strip-thunk xᵢ ＝ x
                      → strip-thunk lᵢ ＝ l
                      → strip-thunk ((thunk-cons xᵢ lᵢ))
                      ＝ x ∷ l
equivalent-thunk-cons (zero , return _) (zero , return _) eq₁ eq₂
 = ap₂ _∷_ eq₁ eq₂
equivalent-thunk-cons (zero , return z₁) (succ _ , (√ z₂)) eq₁ eq₂
 = equivalent-thunk-cons (0 , return z₁) (_ , z₂) eq₁ eq₂
equivalent-thunk-cons (succ _ , (√ z)) lᵢ eq₁ eq₂
 = equivalent-thunk-cons (_ , z) lᵢ eq₁ eq₂

equivalent-lrec-lemma : {σ : LType} {n : ℕ} {Γ : Ctx n}
                      → (env : Envᵢ Γ)
                      → (l : List ℕ)
                      → (base : Term Γ σ)
                      → (f : Term Γ (σ ⇒ nat ⇒ σ))
                      → (strategy : Strategy)
                      → strip-thunk (list-recᵢ env l base f strategy)
                      ＝ list-rec (strip-thunk-env env) l base f
equivalent-lrec-lemma env [] base f s = equivalent-semantics env base s
equivalent-lrec-lemma env (x ∷ l) base f s
 = application-equality env (pr₁ (env [ f ]ᵢ s) (list-recᵢ env l base f s))
    (thunk-type x)
    ((strip-thunk-env env [ f ]ₑ) (list-rec (strip-thunk-env env) l base f))
    x γ refl
 where
  γ : strip-thunk (pr₁ (env [ f ]ᵢ s) (list-recᵢ env l base f s))
    ＝ (strip-thunk-env env [ f ]ₑ) (list-rec (strip-thunk-env env) l base f)
  γ = application-equality env (env [ f ]ᵢ s) (list-recᵢ env l base f s)
       (strip-thunk-env env [ f ]ₑ) (list-rec (strip-thunk-env env) l base f)
       (equivalent-semantics env f s) (equivalent-lrec-lemma env l base f s)

equivalent-lrec : {σ : LType} {n : ℕ} {Γ : Ctx n}
                → (env : Envᵢ Γ)
                → (lᵢ : Σ t ꞉ ℕ , Thunk t (List ℕ))
                → (l : List ℕ)
                → (strip-thunk lᵢ ＝ l)
                → (base : Term Γ σ) (f : Term Γ (σ ⇒ nat ⇒ σ))
                → (strategy : Strategy)
                → strip-thunk (list-rec-builder env lᵢ base f strategy)
                ＝ list-rec (strip-thunk-env env) l base f
equivalent-lrec env (.0 , return l) .(strip-thunk (0 , return l)) refl base f s
 = equivalent-lrec-lemma env l base f s
equivalent-lrec env (.(succ _) , (√ thl)) l eq base f s
 = strip-thunk (increment (list-rec-builder env (_ , thl) base f s))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (list-rec-builder env (_ , thl) base f s)
 ＝⟨ equivalent-lrec env (_ , thl) l eq base f s ⟩
   list-rec (strip-thunk-env env) l base f
 ∎

equivalent-lam-lemma : {n : ℕ} {Γ : Ctx n} {σ τ : LType}
                     → (env : Envᵢ Γ)
                     → (term : Term (σ ∷ Γ) τ)
                     → (strategy : Strategy)
                     → (y : ⟦ σ ⟧)
                     → strip-thunk ((thunk-type y ∷Eᵢ env) [ term ]ᵢ strategy)
                     ＝ (y ∷E (strip-thunk-env env)) [ term ]ₑ
equivalent-lam-lemma env term s y
 = strip-thunk ((thunk-type y ∷Eᵢ env) [ term ]ᵢ s)
 ＝⟨ equivalent-semantics (thunk-type y ∷Eᵢ env) term s ⟩
   (strip-thunk-env (thunk-type y ∷Eᵢ env)) [ term ]ₑ
 ＝⟨ ap (λ z → (z ∷E strip-thunk-env env) [ term ]ₑ)
      (strip-thunk-is-inverse-of-thunk-type y) ⟩
   (y ∷E (strip-thunk-env env)) [ term ]ₑ
 ∎

equivalent-semantics env (var v) _
 = strip-thunk (increment (lookup-envᵢ v env))
 ＝⟨ (increment-equal-semantics)⁻¹ ⟩
   strip-thunk (lookup-envᵢ v env)
 ＝⟨ γ env v ⟩
   lookup-env v (strip-thunk-env env)
 ∎
 where
  γ : {n : ℕ} {Γ : Ctx n}
    → (env : Envᵢ Γ)
    → (v : Fin n)
    → strip-thunk (lookup-envᵢ v env)
    ＝ lookup-env v (strip-thunk-env env)
  γ [] ()
  γ (x ∷Eᵢ _) 𝟎 = refl
  γ (_ ∷Eᵢ env) (suc v) = γ env v
equivalent-semantics env zero _ = refl
equivalent-semantics env (suc term) s = γ₁ (equivalent-semantics env term s)
 where
  γ₀ : {n : ℕ}
     → (th : Thunk n ℕ)
     → force (th >>= (λ x → √ return (succ x))) ＝ succ (force th)
  γ₀ (return x) = refl
  γ₀ (√ th) = γ₀ th

  γ₁ : strip-thunk (env [ term ]ᵢ s) ＝ (strip-thunk-env env) [ term ]ₑ
     → strip-thunk (env [ suc term ]ᵢ s)
     ＝ (strip-thunk-env env) [ suc term ]ₑ
  γ₁ eq
   = force (pr₂ (env [ term ]ᵢ s) >>= (λ x → √ return (succ x)))
   ＝⟨ γ₀ (pr₂ (env [ term ]ᵢ s)) ⟩
     succ (force (pr₂ (env [ term ]ᵢ s)))
   ＝⟨ ap succ eq ⟩
     succ ((strip-thunk-env env) [ term ]ₑ)
   ∎
equivalent-semantics env (pred term) s = γ₁ (equivalent-semantics env term s)
 where
  γ₀ : {n : ℕ}
     → (th : Thunk n ℕ)
     → force (th >>= (λ x → √ return (pred' x))) ＝ pred' (force th)
  γ₀ (return x) = refl
  γ₀ (√ th) = γ₀ th

  γ₁ : strip-thunk (env [ term ]ᵢ s) ＝ (strip-thunk-env env) [ term ]ₑ
     → strip-thunk (env [ pred term ]ᵢ s)
     ＝ (strip-thunk-env env) [ pred term ]ₑ
  γ₁ eq
   = force (pr₂ (env [ term ]ᵢ s) >>= (λ x → √ return (pred' x)))
   ＝⟨ γ₀ (pr₂ (env [ term ]ᵢ s)) ⟩
     pred' (force (pr₂ (env [ term ]ᵢ s)))
   ＝⟨ ap pred' eq ⟩
     pred' ((strip-thunk-env env) [ term ]ₑ)
   ∎
equivalent-semantics env nil _ = refl
equivalent-semantics env (cons term term₁) s
 = equivalent-thunk-cons (env [ term ]ᵢ s) (env [ term₁ ]ᵢ s)
    (equivalent-semantics env term s) (equivalent-semantics env term₁ s)
equivalent-semantics env (if term then term₁ else term₂) s
 = if-then-else-equality env term₁ term₂ (env [ term ]ᵢ s)
    ((strip-thunk-env env) [ term ]ₑ) (equivalent-semantics env term s) s
equivalent-semantics env (term ∙ term₁) s
 = application-equality env (env [ term ]ᵢ s) (env [ term₁ ]ᵢ s)
    ((strip-thunk-env env) [ term ]ₑ) ((strip-thunk-env env) [ term₁ ]ₑ)
    (equivalent-semantics env term s) (equivalent-semantics env term₁ s)
equivalent-semantics env (lam σ term) lazy
 = fe (equivalent-lam-lemma env term lazy)
equivalent-semantics env (lam nat term) eager
 = fe (equivalent-lam-lemma env term eager)
equivalent-semantics env (lam list term) eager
 = fe (equivalent-lam-lemma env term eager)
equivalent-semantics env (lam (σ ⇒ σ₁) term) eager
 = fe (equivalent-lam-lemma env term eager)
equivalent-semantics env (nrec t u v) s
 = equivalent-nrec env (env [ t ]ᵢ s) ((strip-thunk-env env) [ t ]ₑ)
    (equivalent-semantics env t s) u v s
equivalent-semantics env (lrec term term₁ term₂) s
 = equivalent-lrec env (env [ term ]ᵢ s) (strip-thunk-env env [ term ]ₑ)
    (equivalent-semantics env term s) term₁ term₂ s

\end{code}
