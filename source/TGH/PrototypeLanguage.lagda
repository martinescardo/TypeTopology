Theo Hepburn, started 22/05/2025.

A prototype language that features natural numbers as the only basic type,
with it being possible to construct functions on top of this type.

We also have examples of simple functions in this language.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt

module TGH.PrototypeLanguage (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred' ; double to double')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin
open import TGH.BigO
open import TGH.Thunk

infixr 30 _⇒_
data LType : 𝓤₀ ̇  where
 nat : LType
 _⇒_ : LType → LType → LType

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

⟦_⟧ : LType → 𝓤₀ ̇
⟦ nat ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷E_
data Env : {n : ℕ} → Ctx n → 𝓤₀ ̇  where
 [] : Env []
 _∷E_ : {n : ℕ} {Γ : Ctx n } {τ : LType} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookup-env : {n : ℕ} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ Γ !! m ⟧
lookup-env 𝟎 (x ∷E _) = x
lookup-env (suc m) (x ∷E env) = lookup-env m env

if'_then'_else'_ : {X : 𝓤₀ ̇} → ℕ → X → X → X
if' zero then' x else' y = x
if' succ _ then' x else' y = y

nat-rec : {n : ℕ} {Γ : Ctx n} → Env Γ → (m : ℕ)
       → (base : Term Γ nat) → (f : Term Γ (nat ⇒ nat)) → ℕ

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

double : Closed (nat ⇒ nat)
double = lam nat (nrec (var 𝟎) zero (lam nat (suc (suc (var 𝟎)))))

\end{code}

Correctness of double

\begin{code}

double-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   {env₁ : Env Γ₁} {env₂ : Env Γ₂} → (m : ℕ )
                 → nat-rec env₁ m zero (lam nat (suc (suc (var 𝟎))))
                 ＝ nat-rec env₂ m zero (lam nat (suc (suc (var 𝟎))))
double-env-lemma zero = refl
double-env-lemma (succ m) = ap (succ ∘ succ) (double-env-lemma m)

double-correctness : (n : ℕ) → ([] [ double ]ₑ) n ＝ double' n
double-correctness zero = refl
double-correctness (succ n)
 = succ (succ (nat-rec (succ n ∷E []) n zero (lam nat (suc (suc (var 𝟎))))))
   ＝⟨ γ₀ ⟩
   succ (succ (nat-rec [] n zero (lam nat (suc (suc (var 𝟎))))))
   ＝⟨ ap (succ ∘ succ) γ₁ ⟩
   succ (succ (double' n)) ∎
 where
  γ₀ : succ (succ (nat-rec (succ n ∷E []) n zero (lam nat (suc (suc (var 𝟎))))))
       ＝ succ (succ (nat-rec [] n zero (lam nat (suc (suc (var 𝟎))))))
  γ₀ = ap (succ ∘ succ) (double-env-lemma n)

  γ₁ : nat-rec [] n zero (lam nat (suc (suc (var 𝟎)))) ＝ double' n
  γ₁ = nat-rec [] n zero (lam nat (suc (suc (var 𝟎))))
       ＝⟨ (double-env-lemma n)⁻¹ ⟩
       nat-rec (n ∷E []) n zero (lam nat (suc (suc (var 𝟎))))
       ＝⟨ double-correctness n ⟩
       double' n ∎

\end{code}

Intermediate semantics

\begin{code}

⟦_⟧ᵢ : LType → 𝓤₀ ̇

thunk-type : {σ : LType} → ⟦ σ ⟧ → ⟦ σ ⟧ᵢ

strip-thunk : {σ : LType} → ⟦ σ ⟧ᵢ → ⟦ σ ⟧

value-time-independent : {σ τ : LType} → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → 𝓤₀ ̇
value-time-independent {σ} f = (x y : ⟦ σ ⟧ᵢ) → strip-thunk x ＝ strip-thunk y
                             →  strip-thunk (f x) ＝ strip-thunk (f y)


⟦ nat ⟧ᵢ = Σ t ꞉ ℕ , Thunk t ℕ
⟦ σ ⇒ τ ⟧ᵢ = Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f 

thunk-type {nat} x = 0 , return x
thunk-type {σ ⇒ σ₁} f = (λ x → thunk-type (f (strip-thunk x))) , γ f
 where
  γ : {σ σ₁ : LType} (f : ⟦ σ ⟧ → ⟦ σ₁ ⟧) → (x y : ⟦ σ ⟧ᵢ) →
      strip-thunk x ＝ strip-thunk y →
      strip-thunk (thunk-type (f (strip-thunk x))) ＝
      strip-thunk (thunk-type (f (strip-thunk y)))
  γ {_} {_} f x y eq = ap (strip-thunk ∘ thunk-type ∘ f) eq

strip-thunk {nat} (_ , s) = force s
strip-thunk {σ ⇒ σ₁} (f , _) = λ x → strip-thunk (f (thunk-type x))

strip-thunk-is-inverse-of-thunk-type : {σ : LType} → (x : ⟦ σ ⟧)
                                     → strip-thunk (thunk-type x) ＝ x

strip-thunk-is-inverse-of-thunk-lemma : {σ τ : LType} → (f : ⟦ σ ⟧ → ⟦ τ ⟧)
                                      → (x : ⟦ σ ⟧)
                                      → strip-thunk (thunk-type f) x ＝ f x
strip-thunk-is-inverse-of-thunk-lemma f x
 = strip-thunk (thunk-type (f (strip-thunk (thunk-type x))))
   ＝⟨ ap (strip-thunk ∘ thunk-type ∘ f)
     (strip-thunk-is-inverse-of-thunk-type x) ⟩
     strip-thunk (thunk-type (f x))
   ＝⟨ strip-thunk-is-inverse-of-thunk-type (f x) ⟩
   f x ∎

strip-thunk-is-inverse-of-thunk-type {nat} x = refl
strip-thunk-is-inverse-of-thunk-type {σ ⇒ τ} f
 = fe (strip-thunk-is-inverse-of-thunk-lemma f)                           

infixr 5 _∷Eᵢ_
data Envᵢ : {n : ℕ} → Ctx n → 𝓤₀ ̇ where
 [] : Envᵢ []
 _∷Eᵢ_ : {n : ℕ} {Γ : Ctx n } {τ : LType} → ⟦ τ ⟧ᵢ → Envᵢ Γ → Envᵢ (τ ∷ Γ)

strip-thunk-env : {n : ℕ} {Γ : Ctx n } → Envᵢ Γ → Env Γ
strip-thunk-env [] = []
strip-thunk-env (x ∷Eᵢ xs) = strip-thunk x ∷E (strip-thunk-env xs)

lookup-envᵢ : {n : ℕ} {Γ : Ctx n} (m : Fin n) → Envᵢ Γ → ⟦ Γ !! m ⟧ᵢ
lookup-envᵢ 𝟎 (x ∷Eᵢ _) = x
lookup-envᵢ (suc m) (x ∷Eᵢ env) = lookup-envᵢ m env

thunk-if : (Σ n₁ ꞉ ℕ , Thunk n₁ ℕ) → (Σ n₂ ꞉ ℕ , Thunk n₂ ℕ)
         → (Σ n₃ ꞉ ℕ , Thunk n₃ ℕ) → (Σ m ꞉ ℕ , Thunk m ℕ)
thunk-if (zero , return zero) (n₂ , u) (n₃ , v) = succ n₂ , (√ u)
thunk-if (zero , return (succ _)) (n₂ , u) (n₃ , v) = succ n₃ , (√ v)
thunk-if (succ n₁ , (√ t)) u v
 = succ (pr₁ (thunk-if (n₁ , t) u v)) , (√ (pr₂ (thunk-if (n₁ , t) u v)))

nat-recᵢ : {n : ℕ} → {Γ : Ctx n} → Envᵢ Γ → (m : ℕ) → (base : Term Γ nat)
        → (f : Term Γ (nat ⇒ nat)) → Σ t ꞉ ℕ , Thunk t ℕ

rec-builder : {n : ℕ} → {Γ : Ctx n} → Envᵢ Γ
           → Σ t ꞉ ℕ , Thunk t ℕ → (base : Term Γ nat)
           → (f : Term Γ (nat ⇒ nat)) → Σ t ꞉ ℕ , Thunk t ℕ




strip-thunk-thunk-type-rearrange : {τ σ : LType} → (f : ⟦ τ ⇒ σ ⟧ᵢ)
                                 → (z : ⟦ τ ⟧)
                                 → strip-thunk ((pr₁ f) (thunk-type z))
                                 ＝ (strip-thunk f) z
strip-thunk-thunk-type-rearrange f z = refl

inc-function : {σ τ : LType} → (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ

inc-eq : {σ τ : LType} → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
   → value-time-independent f
   →  (x y : ⟦ σ ⟧ᵢ)
   → strip-thunk x ＝ strip-thunk y
   → strip-thunk (inc-function f x) ＝ strip-thunk (inc-function f y)

inc-function {_} {nat} f x = γ (f x) --(λ x → γ (f x))
 where
  γ : Σ t ꞉ ℕ , Thunk t ℕ → Σ t ꞉ ℕ , Thunk t ℕ
  γ (n , x) = succ n , (√ x)
inc-function {σ₁} {σ ⇒ τ} f x
 = inc-function (pr₁ (f x)) , inc-eq (pr₁ (f x)) (pr₂ (f x))

change-function : {σ τ : LType}
                → (f : (Σ f' ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f'))
                → (g : (Σ g' ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent g'))
                → strip-thunk {σ ⇒ τ} f ＝ strip-thunk {σ ⇒ τ} g
                → (λ x → strip-thunk (inc-function (pr₁ f) (thunk-type x)))
                ＝ (λ x → strip-thunk (inc-function (pr₁ g) (thunk-type x)))
    
change-function {σ} {nat} (pr₃ , pr₄) (pr₅ , pr₆) eq = eq
change-function {σ} {τ ⇒ τ₁} f g eq
 = fe λ x → change-function (pr₁ f (thunk-type x))
   (pr₁ g (thunk-type x)) (ap (λ w → w x) eq)

inc-eq {_} {nat} f value-time-ind = value-time-ind
inc-eq {σ₁} {σ ⇒ τ} f value-time-ind x y eq
 = change-function (f x) (f y) (value-time-ind x y eq)

increment : {τ : LType} → ⟦ τ ⟧ᵢ → ⟦ τ ⟧ᵢ
increment {nat} (t , x) = succ t , (√ x)
increment {τ ⇒ σ} (f , eqt) = inc-function f , inc-eq f eqt

increment-equal-semantics : {τ : LType} → (x : ⟦ τ ⟧ᵢ)
                          → strip-thunk x ＝ strip-thunk (increment x)
increment-equal-semantics {nat} x = refl
increment-equal-semantics {σ ⇒ τ} (f , eqt) = fe λ x → γ₂ (thunk-type x)
 where
  γ₁ : {σ τ : LType} → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) → (y : ⟦ σ ⟧ᵢ)
       → strip-thunk (increment (f y)) ＝ strip-thunk (inc-function f y)
  γ₁ {σ} {nat} f y = refl
  γ₁ {σ} {τ ⇒ τ₁} f y = refl

  γ₂ : (y : ⟦ σ ⟧ᵢ) → strip-thunk (f y) ＝ strip-thunk (inc-function f y)
  γ₂ y = strip-thunk (f y) ＝⟨ increment-equal-semantics (f y) ⟩
         strip-thunk (increment (f y)) ＝⟨ γ₁ f y ⟩
         strip-thunk (inc-function f y) ∎

_[_]ᵢ : {n : ℕ} {Γ : Ctx n} {τ : LType} → Envᵢ Γ → Term Γ τ → ⟦ τ ⟧ᵢ

equivalent-semantics : {n : ℕ} {σ : LType} {Γ : Ctx n} → (env : Envᵢ Γ)
                     → (term : Term Γ σ)
                     → strip-thunk (env [ term ]ᵢ)
                     ＝ (strip-thunk-env env) [ term ]ₑ


lam-value-time-independent : {n : ℕ} {Γ : Ctx n} {τ : LType} → (σ : LType)
                           → (env : Envᵢ Γ) → (t : Term (σ ∷ Γ) τ)
                           → value-time-independent (λ x → (x ∷Eᵢ env) [ t ]ᵢ)
lam-value-time-independent σ env t
 = λ x y eq → strip-thunk ((x ∷Eᵢ env) [ t ]ᵢ)
   ＝⟨ equivalent-semantics (x ∷Eᵢ env) t ⟩
   ((strip-thunk x) ∷E (strip-thunk-env env)) [ t ]ₑ
   ＝⟨ ap (λ z → (z ∷E strip-thunk-env env) [ t ]ₑ) eq ⟩
   (((strip-thunk y) ∷E (strip-thunk-env env)) [ t ]ₑ)
   ＝⟨ (equivalent-semantics (y ∷Eᵢ env) t)⁻¹ ⟩
   strip-thunk ((y ∷Eᵢ env) [ t ]ᵢ) ∎

env [ var v ]ᵢ = increment (lookup-envᵢ v env )
env [ zero ]ᵢ = 1 , (√ return zero)
env [ if t then u else v ]ᵢ = thunk-if (env [ t ]ᵢ) (env [ u ]ᵢ) (env [ v ]ᵢ)
env [ suc t ]ᵢ = γ (env [ t ]ᵢ)
 where
  γ : Σ t ꞉ ℕ , Thunk t ℕ → Σ t ꞉ ℕ , Thunk t ℕ
  γ (n , t) = 1 + n , (t >>= λ x → √ return (succ x))
env [ t ∙ u ]ᵢ = (pr₁ (env [ t ]ᵢ)) (env [ u ]ᵢ)
env [ lam σ t ]ᵢ
 = (λ x → (x ∷Eᵢ env) [ t ]ᵢ) , lam-value-time-independent σ env t
env [ nrec t u v ]ᵢ = rec-builder env (env [ t ]ᵢ) u v

rec-builder env (0 , return x) u v = nat-recᵢ env x u v
rec-builder env ((succ _) , (√ x)) u v
 = succ (pr₁ (rec-builder env (_ , x) u v)) ,
   (√ (pr₂ (rec-builder env (_ , x) u v)))

nat-recᵢ env zero base f = env [ base ]ᵢ
nat-recᵢ env (succ n) base f = (pr₁ (env [ f ]ᵢ)) (nat-recᵢ env n base f)

\end{code}

We use function extensionality as we must prove the equality of functions.

\begin{code}

strip-thunk-thunk-type-lemma : {σ τ : LType} → (f : ⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ)
           → (eqt : (x y : ⟦ σ ⟧ᵢ) →
           strip-thunk x ＝ strip-thunk y →
           strip-thunk (f x) ＝ strip-thunk (f y))
           →  (thunked : ⟦ σ ⟧ᵢ) → (unthunked : ⟦ σ ⟧)
           → strip-thunk thunked ＝ unthunked
           → strip-thunk (f thunked)
           ＝ strip-thunk (f (thunk-type unthunked))
strip-thunk-thunk-type-lemma f eqt thunked unthunked eq
 = eqt thunked (thunk-type unthunked) (strip-thunk thunked ＝⟨ eq ⟩
   unthunked ＝⟨ (strip-thunk-is-inverse-of-thunk-type unthunked)⁻¹ ⟩
   strip-thunk (thunk-type unthunked) ∎)

if-then-else-equality : {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
      → (term₁ : Term Γ nat) → (term₂ : Term Γ nat)
      → (thunked : Σ t ꞉ ℕ , Thunk t ℕ)
      → (not-thunked : ℕ)
      → (force (pr₂ thunked)) ＝ not-thunked
      → force (pr₂ (thunk-if thunked (env [ term₁ ]ᵢ) (env [ term₂ ]ᵢ)))
      ＝ if' not-thunked then' ((strip-thunk-env env) [ term₁ ]ₑ)
         else' ((strip-thunk-env env) [ term₂ ]ₑ)
if-then-else-equality env term₁ term₂ (.0 , return zero) zero refl
 = equivalent-semantics env term₁
if-then-else-equality env term₁ term₂ (.(succ _) , (√ t)) zero x
 = if-then-else-equality env term₁ term₂ (_ , t) zero x 
if-then-else-equality env term₁ term₂ (.0 , return (succ _)) (succ _) refl
 = equivalent-semantics env term₂
if-then-else-equality env term₁ term₂ (.(succ _) , (√ t)) (succ not-thunked) x
 = if-then-else-equality env term₁ term₂ (_ , t) _ x

application-equality : {n : ℕ} {Γ : Ctx n} {σ τ : LType} → (env : Envᵢ Γ)
      → (thunked₁ : Σ f ꞉ (⟦ σ ⟧ᵢ → ⟦ τ ⟧ᵢ) , value-time-independent f)
      → (thunked₂ : ⟦ σ ⟧ᵢ)
      → (unthunked₁ : ⟦ σ ⟧ → ⟦ τ ⟧)
      → (unthunked₂ : ⟦ σ ⟧)
      → strip-thunk thunked₁  ＝ unthunked₁
      → strip-thunk thunked₂ ＝ unthunked₂
      → strip-thunk ((pr₁ thunked₁) thunked₂) ＝ unthunked₁ unthunked₂
application-equality env (f₁ , eqt) thunked₂ unthunked₁ unthunked₂ eq₁ eq₂
 = strip-thunk (f₁ thunked₂)
   ＝⟨ strip-thunk-thunk-type-lemma f₁ eqt thunked₂ unthunked₂ eq₂ ⟩
   strip-thunk (f₁ (thunk-type unthunked₂)) ＝⟨ refl ⟩
   (λ x → strip-thunk (f₁ (thunk-type x))) unthunked₂
   ＝⟨ ap (λ z → z unthunked₂) eq₁ ⟩
   unthunked₁ unthunked₂ ∎

equivalent-nrec-lemma : {n : ℕ} → {Γ : Ctx n} → (env : Envᵢ Γ) → (ctr : ℕ)
                      → (base : Term Γ nat) → (f : Term Γ (nat ⇒ nat))
                      → strip-thunk (nat-recᵢ env ctr base f)
                      ＝ (nat-rec (strip-thunk-env env) ctr base f)
equivalent-nrec-lemma env zero base f = equivalent-semantics env base
equivalent-nrec-lemma env (succ ctr) base f
 = application-equality env (env [ f ]ᵢ) (nat-recᵢ env ctr base f)
   (strip-thunk-env env [ f ]ₑ) (nat-rec (strip-thunk-env env) ctr base f)
   (equivalent-semantics env f) (equivalent-nrec-lemma env ctr base f) 

equivalent-nrec : {n : ℕ} → {Γ : Ctx n} → (env : Envᵢ Γ)
 → (ctrᵢ : Σ t ꞉ ℕ , Thunk t ℕ) → (ctr : ℕ)
 → (strip-thunk ctrᵢ ＝ ctr) → (base : Term Γ nat)
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
   strip-thunk (lookup-envᵢ v env) ＝⟨ γ env v ⟩
   lookup-env v (strip-thunk-env env) ∎
 where
  γ : {n : ℕ} → {Γ : Ctx n} → (env : Envᵢ Γ) → (v : Fin n)
    → strip-thunk (lookup-envᵢ v env) ＝ lookup-env v (strip-thunk-env env)
  γ (x ∷Eᵢ _) 𝟎 = refl
  γ (_ ∷Eᵢ env) (suc v) = γ env v
equivalent-semantics env zero = refl
equivalent-semantics env (if term then term₁ else term₂)
 = if-then-else-equality env term₁ term₂ (env [ term ]ᵢ) ((strip-thunk-env env)
   [ term ]ₑ) (equivalent-semantics env term)
equivalent-semantics env (suc term) = γ₁ (equivalent-semantics env term)
 where
  γ₀ : {n : ℕ} → (th : Thunk n ℕ)
     → force (th >>= (λ x → √ return (succ x))) ＝ succ (force th)
  γ₀ (return x) = refl
  γ₀ (√ th) = γ₀ th

  γ₁ : strip-thunk (env [ term ]ᵢ) ＝ (strip-thunk-env env) [ term ]ₑ
       → strip-thunk (env [ suc term ]ᵢ) ＝ (strip-thunk-env env) [ suc term ]ₑ
  γ₁ eq = force (pr₂ (env [ term ]ᵢ) >>= (λ x → √ return (succ x)))
          ＝⟨ γ₀ (pr₂ (env [ term ]ᵢ)) ⟩
          succ (force (pr₂ (env [ term ]ᵢ))) ＝⟨ ap succ eq ⟩
          succ ((strip-thunk-env env) [ term ]ₑ) ∎
equivalent-semantics env (term ∙ term₁)
 = application-equality env (env [ term ]ᵢ) (env [ term₁ ]ᵢ)
   ((strip-thunk-env env) [ term ]ₑ) ((strip-thunk-env env) [ term₁ ]ₑ)
   (equivalent-semantics env term) (equivalent-semantics env term₁)
equivalent-semantics env (lam σ term)
 = fe λ y → strip-thunk ((thunk-type y ∷Eᵢ env) [ term ]ᵢ)
   ＝⟨ equivalent-semantics (thunk-type y ∷Eᵢ env) term ⟩
   (strip-thunk-env (thunk-type y ∷Eᵢ env)) [ term ]ₑ
   ＝⟨ ap (λ z → (z ∷E strip-thunk-env env) [ term ]ₑ)
   (strip-thunk-is-inverse-of-thunk-type y) ⟩
   (y ∷E (strip-thunk-env env)) [ term ]ₑ ∎
                                                            
equivalent-semantics env (nrec t u v)
 = equivalent-nrec env (env [ t ]ᵢ) ((strip-thunk-env env) [ t ]ₑ)
   (equivalent-semantics env t) u v

time-function : (Closed (nat ⇒ nat)) → ℕ → ℕ
time-function term n = pr₁ ((pr₁ ([] [ term ]ᵢ)) (0 , return n))

double-natrec-lemma : {m₁ m₂ : ℕ} {Γ₁ : Ctx m₁} {Γ₂ : Ctx m₂}
                      {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂}
                    → (n : ℕ)
                    → (nat-recᵢ env₁ n zero (lam nat (suc (suc (var 𝟎)))))
                    ＝ (nat-recᵢ env₂ n zero (lam nat (suc (suc (var 𝟎)))))
double-natrec-lemma zero = refl
double-natrec-lemma (succ n) = ap (λ y → succ
      (1 +
       (1 +
        pr₁ y))
      ,
      (√
       pr₂ y >>=
       (λ x → √ return (succ x))
       >>= (λ x → √ return (succ x)))) (double-natrec-lemma n)

double-time : (time-function double) ∈O[ (λ n → n) ]
double-time = big-o (5 , 1 , γ)
 where
  γ₀ : (x : ℕ) → 1 ≤ (succ x)
     → succ (pr₁ (nat-recᵢ ((0 , return (succ x)) ∷Eᵢ [])
       (succ x) zero (lam nat (suc (suc (var 𝟎)))))) ≤ (5 + 5 * x)
  γ₀ zero ⋆ = ⋆
  γ₀ (succ n) ⋆ = γ₈
   where
    γ₁ : (n : ℕ) → succ (succ (succ (1 + (1 + n)))) ＝ 5 + n
    γ₁ n = succ (succ (succ (1 + (1 + n)))) ＝⟨ ap (succ ∘ succ ∘ succ)
           (+-assoc 1 1 n)⁻¹ ⟩
           succ (succ (succ (2 + n))) ＝⟨ refl ⟩
           succ (succ (2 + n + 1)) ＝⟨ refl ⟩
           2 + n + 3 ＝⟨ ap (_+ 3) (+-comm 2 n) ⟩
           n + 2 + 3 ＝⟨ refl ⟩
           n + 5 ＝⟨ +-comm n 5 ⟩
           5 + n ∎

    γ₂ : (n : ℕ) → 5 + n ≤ 5 + n
    γ₂ n = ≤-refl (5 + n)

    γ₃ : (n : ℕ) → succ (succ (succ (1 + (1 + n)))) ≤ 5 + n
    γ₃ n = transport (λ y → y ≤ 5 + n) ((γ₁ n)⁻¹) (γ₂ n)

    γ₄ : (n m : ℕ) → n ≤ m → succ (succ (succ (1 + (1 + n)))) ≤ 5 + m
    γ₄ n m le
     = ≤-trans (succ (succ (succ (1 + (1 + n)))))
       (5 + n) (5 + m) (γ₃ n) (≤-n-monotone-left n m 5 le)

    γ₇ : (n : ℕ) → n ≤ succ (succ n)
    γ₇ n = ≤-trans n (succ n) (succ (succ n)) (≤-succ n) (≤-succ (succ n))

    γ₅ : 1 + (1 + (pr₁ (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n
         zero (lam nat (suc (suc (var 𝟎)))))))
         ≤ 5 * (succ n)
    γ₅ = ≤-trans (1 + (1 + pr₁ (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n
         zero (lam nat (suc (suc (var 𝟎))))))) (succ (succ (1 + (1 + pr₁
         (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n zero
         (lam nat (suc (suc (var 𝟎))))
         ))))) (5 + 5 * n) (γ₇ (1 + (1 + pr₁ (nat-recᵢ
         ((0 , return (succ n)) ∷Eᵢ []) n zero
         (lam nat (suc (suc (var 𝟎)))))))) (γ₀ n ⋆)

    γ₆ : (n : ℕ) → 1 + (1 + pr₁ (nat-recᵢ ((0 , return (succ (succ n))) ∷Eᵢ [])
         n zero (lam nat (suc (suc (var 𝟎)))))) ＝ 1 + (1 + (pr₁ (nat-recᵢ
         ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat (suc (suc (var 𝟎)))))))
    γ₆ n = 1 + (1 + pr₁ (nat-recᵢ ((0 , return (succ (succ n))) ∷Eᵢ []) n zero
           (lam nat (suc (suc (var 𝟎)))))) ＝⟨ ap ((1 +_) ∘ (1 +_) ∘ pr₁)
           (double-natrec-lemma n) ⟩
           1 + (1 + pr₁ (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n zero
           (lam nat (suc (suc (var 𝟎)))))) ∎


    γ₈ : succ (succ (succ (1 + (1 + (1 + (1 + pr₁ (nat-recᵢ ((0 , return (succ
         (succ n))) ∷Eᵢ []) n zero (lam nat (suc (suc (var 𝟎)))))))))))
         ≤ 5 + (5 + 5 * n)
    γ₈ = γ₄ (1 + (1 + pr₁ (nat-recᵢ ((0 , return (succ (succ n))) ∷Eᵢ []) n zero
         (lam nat (suc (suc (var 𝟎))))))) (5 + 5 * n)
         (transport (λ z → z ≤ 5 + 5 * n) ((γ₆ n)⁻¹) γ₅)

  γ : (x : ℕ) → 1 ≤ x
    → succ (pr₁ (nat-recᵢ ((0 , return x) ∷Eᵢ []) x zero
      (lam nat (suc (suc (var 𝟎))))))
                          ≤ (5 * x)
  γ (succ n) le = γ₀ n ⋆

is-even : Closed (nat ⇒ nat)
is-even = lam nat (nrec (var 𝟎) zero (lam nat
          (if (var 𝟎) then (suc zero) else zero )))

my-even : ℕ → ℕ
my-even zero = 0
my-even (succ n) = if' my-even n then' 1 else' 0

is-even-env-lemma : {m₁ m₂ : ℕ} {Γ₁ : Ctx m₁} {Γ₂ : Ctx m₂}
                    {env₁ : Env Γ₁} {env₂ : Env Γ₂} → (n : ℕ )
                  → nat-rec env₁ n zero
                    (lam nat (if var 𝟎 then suc zero else zero))
                  ＝ nat-rec env₂ n zero (lam nat
                    (if var 𝟎 then suc zero else zero))
is-even-env-lemma zero = refl
is-even-env-lemma (succ n) = ap (λ z → if' z then' 1 else' 0)
                             (is-even-env-lemma n)

is-even-correctness : (n : ℕ) → ([] [ is-even ]ₑ) n ＝ my-even n
is-even-correctness zero = refl
is-even-correctness (succ n) =
 (if' nat-rec (succ n ∷E []) n zero (lam nat (if var 𝟎 then suc zero else zero))
 then' 1 else' 0) ＝⟨ is-even-env-lemma (succ n) ⟩
 (if' nat-rec (n ∷E []) n zero (lam nat (if var 𝟎 then suc zero else zero))
 then' 1 else' 0)
 ＝⟨ ap (λ z → if' z then' 1 else' 0) (is-even-correctness n) ⟩
 if' my-even n then' 1 else' 0 ∎

is-even-natrec-lemma : {m₁ m₂ : ℕ} {Γ₁ : Ctx m₁} {Γ₂ : Ctx m₂}
                       {env₁ : Envᵢ Γ₁} {env₂ : Envᵢ Γ₂} → (n : ℕ)
                       → nat-recᵢ env₁ n zero (lam nat
                       (if var 𝟎 then suc zero else zero))
                       ＝ nat-recᵢ env₂ n zero (lam nat
                       (if var 𝟎 then suc zero else zero))
is-even-natrec-lemma zero = refl
is-even-natrec-lemma (succ n)
 = ap (λ x → (succ (pr₁ (thunk-if x (2 , (√ (√ return 1))) (1 , (√ return 0))))
   , (√ pr₂ (thunk-if x (2 , (√ (√ return 1))) (1 , (√ return 0))))))
   (is-even-natrec-lemma n)

nat-rec<2 : {m : ℕ} {Γ : Ctx m} {env : Env Γ} → (n : ℕ)
         → nat-rec env n zero (lam nat (if var 𝟎 then suc zero else zero)) < 2
nat-rec<2 zero = ⋆
nat-rec<2 (succ n) = γ (nat-rec _ n zero (lam nat (if var 𝟎 then suc zero else
                    zero))) (nat-rec<2 n)
 where
  γ : (n : ℕ) → (n < 2) → (if' n then' 1 else' 0) < 2
  γ zero le = ⋆
  γ (succ zero) le = ⋆

is-even-time : (time-function is-even) ∈O[ (λ n → n) ]
is-even-time = big-o (6 , 1 , γ)
 where
  γ₀ : (n : ℕ) → 1 ≤ (succ n) → succ (pr₁ (nat-recᵢ {1} {nat ∷ []}
       ((0 , return (succ n)) ∷Eᵢ []) (succ n) zero (lam nat
       (if var 𝟎 then suc zero else zero)))) ≤ (6 * (succ n))
  γ₀ zero ⋆ = ⋆
  γ₀ (succ n) ⋆ = goal
   where
    IH : succ (succ (pr₁ (thunk-if (nat-recᵢ {1} {nat ∷ []}
         ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat
         (if var 𝟎 then suc zero else zero))) (2 ,
         (√ (√ return 1))) (1 , (√ return 0)))))
         ≤ (6 + 6 * n)
    IH = γ₀ n ⋆

    γ₁ : succ (succ (pr₁ (thunk-if (nat-recᵢ {1} {nat ∷ []}
         ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat
         (if var 𝟎 then suc zero else zero))) (2 ,
         (√ (√ return 1))) (1 , (√ return 0)))))
         ≤ (6 * n + 6)
    γ₁ = transport (λ y → succ (succ (pr₁ (thunk-if (nat-recᵢ
         {1} {nat ∷ []} ((0 , return (succ n)) ∷Eᵢ []) n zero
         (lam nat (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1)))
         (1 , (√ return 0))))) ≤ y) (+-comm 6 (6 * n)) IH

    γ₂ : (n : ℕ) → (n < 2) → if' if' n then' 1 else' 0 then' 1 else' 0 ＝ n
    γ₂ zero le = refl
    γ₂ (succ zero) le = refl
        
    γ₃ : (n : ℕ) → force (pr₂ (thunk-if (nat-recᵢ {1} {nat ∷ []}
         ((0 , return (succ (succ (succ n)))) ∷Eᵢ []) (succ (succ n)) zero
         (lam nat (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1)))
         (1 , (√ return 0))))
       ＝ force (pr₂ (thunk-if (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n zero
         (lam nat (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1)))
         (1 , (√ return 0))))
    γ₃ n = force (pr₂ (thunk-if (nat-recᵢ ((0 , return (succ (succ (succ n))))
           ∷Eᵢ []) (succ (succ n)) zero (lam nat (if var 𝟎 then suc zero else
           zero))) (2 , (√ (√ return 1))) (1 , (√ return 0)))) ＝⟨ ap (λ y →
           force (pr₂ (thunk-if y (2 , (√ (√ return 1))) (1 , (√ return 0)))))
           (is-even-natrec-lemma (succ (succ n))) ⟩
           force (pr₂ (thunk-if (nat-recᵢ [] (succ (succ n)) zero (lam nat (if
           var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1))) (1 ,
           (√ return 0)))) ＝⟨ if-then-else-equality [] (suc zero) zero
           (nat-recᵢ
           [] (succ (succ n)) zero (lam nat (if var 𝟎 then suc zero else zero)))
           (nat-rec [] (succ (succ n)) zero (lam nat (if var 𝟎 then suc zero
           else
           zero))) (equivalent-nrec-lemma [] (succ (succ n)) zero (lam nat (if
           var 𝟎 then suc zero else zero))) ⟩
           if' (nat-rec [] (succ (succ n)) zero (lam nat (if var 𝟎 then suc zero
           else zero))) then' 1 else' 0 ＝⟨ ap (λ y → if' y then' 1 else' 0)
           (γ₂ (nat-rec [] n zero (lam nat (if var 𝟎 then suc zero else zero)))
           (nat-rec<2 n)) ⟩
           if' (nat-rec [] n zero (lam nat (if var 𝟎 then suc zero else zero)))
           then' 1 else' 0 ＝⟨ (if-then-else-equality [] (suc zero) zero
           (nat-recᵢ [] n zero (lam nat (if var 𝟎 then suc zero else zero)))
           (nat-rec [] n zero (lam nat (if var 𝟎 then suc zero else zero)))
           (equivalent-nrec-lemma [] n zero (lam nat (if var 𝟎 then suc zero
           else zero))))⁻¹ ⟩
           force (pr₂ (thunk-if (nat-recᵢ [] n zero (lam nat (if var 𝟎 then suc
           zero else zero))) (2 , (√ (√ return 1))) (1 , (√ return 0))))
           ＝⟨ ap (λ y → force (pr₂ (thunk-if y (2 , (√ (√ return 1)))
           (1 , (√ return 0))))) (is-even-natrec-lemma n)⁻¹ ⟩
           force (pr₂ (thunk-if (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n zero
           (lam nat (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1)))
           (1 , (√ return 0)))) ∎

    γ₄ : (n : ℕ) → force (pr₂ (thunk-if (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ [])
         n zero (lam nat (if var 𝟎 then suc zero else zero)))
         (2 , (√ (√ return 1))) (1 , (√ return 0)))) < 2
    γ₄ zero = ⋆
    γ₄ (succ zero) = ⋆
    γ₄ (succ (succ n)) = transport (λ z → z < 2) ((γ₃ n)⁻¹) (γ₄ n)

    γ₅ : (x : (Σ t ꞉ ℕ , Thunk t ℕ)) → force (pr₂ x) < 2 → pr₁ (thunk-if x
         (2 , (√ (√ return 1))) (1 , (√ return 0))) ≤ pr₁ x + 3
    γ₅ (.0 , return zero) le = ⋆
    γ₅ (.0 , return 1) le = ⋆
    γ₅ (.(succ _) , (√ x)) le = γ₅ (_ , x) le

    γ₆ : (pr₁ (thunk-if (thunk-if (nat-recᵢ {1} {nat ∷ []}
         ((0 , return (succ n))
         ∷Eᵢ []) n zero (lam nat (if var 𝟎 then suc zero else zero))) (2 ,
         (√ (√ return 1))) (1 , (√ return 0))) (2 , (√ (√ return 1)))
         (1 , (√ return 0)))) ≤ pr₁ (thunk-if (nat-recᵢ {1} {nat ∷ []}
         ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat (if var 𝟎 then suc zero
         else zero))) (2 , (√ (√ return 1))) (1 , (√ return 0))) + 3
    γ₆ = γ₅ (thunk-if (nat-recᵢ {1} {nat ∷ []} ((0 , return (succ n)) ∷Eᵢ []) n
         zero (lam nat (if var 𝟎 then suc zero else zero))) (2 ,
         (√ (√ return 1))) (1 , (√ return 0))) (γ₄ n)

    γ₇ : (pr₁ (thunk-if (thunk-if (nat-recᵢ {1} {nat ∷ []}
         ((0 , return (succ n))
         ∷Eᵢ []) n zero (lam nat (if var 𝟎 then suc zero else zero)))
         (2 , (√ (√ return 1))) (1 , (√ return 0))) (2 , (√ (√ return 1)))
         (1 , (√ return 0)))) ≤ 6 * n + 7
    γ₇ = ≤-trans (pr₁ (thunk-if (thunk-if (nat-recᵢ
         ((0 , return (succ n)) ∷Eᵢ [])
         n zero (lam nat (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return
         1))) (1 , (√ return 0))) (2 , (√ (√ return 1))) (1 , (√ return 0))))
         (pr₁ (thunk-if (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat
         (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1)))
         (1 , (√ return 0))) + 3) (6 * n + 7) γ₆ γ₁

    γ₈ : 3 + (6 + 6 * n) ＝ 6 * n + 9
    γ₈ = 3 + (6 + 6 * n) ＝⟨ (+-assoc 3 6 (6 * n))⁻¹ ⟩
         9 + 6 * n ＝⟨ +-comm 9 (6 * n) ⟩
         6 * n + 9 ∎

    γ₉ : pr₁ (thunk-if (thunk-if (nat-recᵢ ((0 , return (succ n)) ∷Eᵢ []) n
         zero (lam nat (if var 𝟎 then suc zero else zero)))
         (2 , (√ (√ return 1)))
         (1 , (√ return 0))) (2 , (√ (√ return 1))) (1 , (√ return 0)))
         ≤ (3 + (6 + 6 * n))
    γ₉ = ≤-trans (pr₁ (thunk-if (thunk-if (nat-recᵢ ((0 , return (succ n))
         ∷Eᵢ []) n zero (lam nat (if var 𝟎 then suc zero else zero)))
         (2 , (√ (√ return 1))) (1 , (√ return 0))) (2 , (√ (√ return 1)))
         (1 , (√ return 0)))) (6 * n + 7) (3 + (6 + 6 * n)) γ₇
         (transport (λ z → 6 * n + 7 ≤ z) ((γ₈)⁻¹)
         ((≤-n-monotone-left 0 2 (6 * n) ⋆)))

    γ₁₀ : 3 + (6 + 6 * n) + 3 ＝ 6 + (6 + 6 * n)
    γ₁₀ = 3 + (6 + 6 * n) + 3 ＝⟨ +-comm (3 + (6 + 6 * n)) 3 ⟩
          3 + (3 + (6 + 6 * n)) ＝⟨ (+-assoc 3 3 (6 + 6 * n))⁻¹ ⟩
          6 + (6 + 6 * n) ∎

    γ₁₁ : pr₁ (thunk-if (thunk-if (nat-recᵢ {1} {nat ∷ []}
          ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat
          (if var 𝟎 then suc zero else zero))) (2 , (√ (√ return 1)))
          (1 , (√ return 0))) (2 , (√ (√ return 1))) (1 , (√ return 0)))
          + 3 ≤ (6 + (6 + 6 * n))
    γ₁₁ = transport (λ z → pr₁ (thunk-if (thunk-if (nat-recᵢ {1} {nat ∷ []}
          ((0 , return (succ n)) ∷Eᵢ []) n zero (lam nat (if var 𝟎 then suc
          zero else zero))) (2 , (√ (√ return 1))) (1 , (√ return 0))) (2 ,
          (√ (√ return 1))) (1 , (√ return 0))) + 3 ≤ z) γ₁₀ γ₉        

    goal : succ (succ (succ (pr₁ (thunk-if (thunk-if (nat-recᵢ {1} {nat ∷ []}
           ((0 , return (succ (succ n))) ∷Eᵢ []) n zero (lam nat (if var 𝟎
           then suc zero else zero))) (2 , (√ (√ return 1))) (1 , (√ return 0)))
           (2 , (√ (√ return 1))) (1 , (√ return 0)))))) ≤ (6 + (6 + 6 * n))
    goal = transport (λ y → succ (succ (succ (pr₁ (thunk-if (thunk-if y (2 ,
           (√ (√ return 1))) (1 , (√ return 0))) (2 , (√ (√ return 1)))
           (1 , (√ return 0)))))) ≤ 6 + (6 + 6 * n)) (is-even-natrec-lemma n)
           γ₁₁

  γ : (n : ℕ) → 1 ≤ n → succ (pr₁ (nat-recᵢ ((0 , return n) ∷Eᵢ []) n zero
      (lam nat (if var 𝟎 then suc zero else zero)))) ≤ (6 * n)
  γ (succ n) ⋆ = γ₀ n ⋆

\end{code}
