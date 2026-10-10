Theo Hepburn, started in February 2025

A formalisation of the complexity class P,
with proof of closure properties of P.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy

module TGH.P (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition
 renaming (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin
open import MLTT.List
open import MLTT.Bool hiding (if_then_else_)
open import UF.Base
open import TGH.Thunk
open import TGH.Language fe
open import TGH.ComplexityDefinitionsResults fe

all-binary : List ℕ → 𝓤₀ ̇
all-binary [] = 𝟙
all-binary (x ∷ xs) = ((x ＝ 0) ∔ (x ＝ 1)) × (all-binary xs)

is-binary-program : {n : ℕ} {Γ : Ctx n}
                  → (program : Term (list ∷ Γ) list)
                  → 𝓤₀ ̇
is-binary-program {n} {Γ} program
 = (env : Env Γ)
 → (xs : List ℕ)
 → (all-binary xs)
 → all-binary ((env [ lam list program ]ₑ) xs)

Reduction : {n : ℕ} (Γ : Ctx n) → 𝓤₀ ̇
Reduction Γ = Σ program ꞉ Term (list ∷ Γ) list , is-binary-program program

bool-to-nat : Bool → ℕ
bool-to-nat true = 0
bool-to-nat false = 1

nat-to-bool : ℕ → Bool
nat-to-bool zero = true
nat-to-bool (succ _) = false

_inverse-of_ : {X Y : 𝓤₀ ̇} → (f : Y → X) → (g : X → Y) → 𝓤₀ ̇
f inverse-of g = f ∘ g ∼ id

bool-nat-inverse : nat-to-bool inverse-of bool-to-nat
bool-nat-inverse true = refl
bool-nat-inverse false = refl

map-inverse : {X Y : 𝓤₀ ̇} {f : Y → X} {g : X → Y}
            → f inverse-of g
            → (map f) inverse-of (map g)
map-inverse eq [] = refl
map-inverse eq (x ∷ l) = ap₂ _∷_ (eq x) (map-inverse eq l)

map-bool-nat-inverse : (map nat-to-bool) inverse-of (map bool-to-nat)
map-bool-nat-inverse = map-inverse bool-nat-inverse

ite-nat-bool-inverse : {X : 𝓤₀ ̇} {x y : X}
                     → (n : ℕ)
                     → if' n then' x else' y
                     ＝ if' bool-to-nat (nat-to-bool n) then' x else' y
ite-nat-bool-inverse zero = refl
ite-nat-bool-inverse (succ n) = refl

map-nat-bool-binary-list : (xs : List ℕ)
                         → (all-binary xs)
                         → (map bool-to-nat (map nat-to-bool xs)) ＝ xs
map-nat-bool-binary-list [] x = refl
map-nat-bool-binary-list (zero ∷ xs) (_ , all-binary)
 = ap (0 ∷_) (map-nat-bool-binary-list xs all-binary)
map-nat-bool-binary-list (succ zero ∷ xs) (_ , all-binary)
 = ap (1 ∷_) (map-nat-bool-binary-list xs all-binary)
map-nat-bool-binary-list (succ (succ x₁) ∷ xs) (inl () , pr₄)
map-nat-bool-binary-list (succ (succ x₁) ∷ xs) (inr () , pr₄)

all-binary-map-bool-to-nat : (xs : List Bool)
                           → all-binary (map bool-to-nat xs)
all-binary-map-bool-to-nat [] = ⋆
all-binary-map-bool-to-nat (true ∷ xs)
 = (inl refl) , (all-binary-map-bool-to-nat xs)
all-binary-map-bool-to-nat (false ∷ xs)
 = (inr refl) , (all-binary-map-bool-to-nat xs)

map-nat-bool-inverse-reduction : {n : ℕ} {Γ : Ctx n}
                               → (env : Env Γ)
                               → (r : Reduction Γ)
                               → (xs : List ℕ)
                               → (all-binary xs)
                               → (map bool-to-nat (map nat-to-bool
                                  ((xs ∷E env) [ pr₁ r ]ₑ)))
                               ＝ ((xs ∷E env) [ (pr₁ r) ]ₑ)
map-nat-bool-inverse-reduction env r xs all-binary
 = map-nat-bool-binary-list ((xs ∷E env) [ pr₁ r ]ₑ) ((pr₂ r) env xs all-binary)

to-decision-solver : {n : ℕ} {Γ : Ctx n}
                   → (env : Env Γ)
                   → Term (list ∷ Γ) nat
                   → List Bool
                   → Bool
to-decision-solver env program l
 = nat-to-bool ((env [ lam list program ]ₑ) (map bool-to-nat l))

general-list-polytime : {τ : LType} {n : ℕ} {Γ : Ctx n}
                      → ((τ ＝ nat) ∔ (τ ＝ list))
                      → Term (list ∷ Γ) τ
                      → 𝓤₀ ̇
general-list-polytime {_} {n} {Γ} (inl refl) program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
 , is-polytime k C N₀ (length l)
    (pr₁ (pr₁ (env [ lam list program ]ᵢ eager) (thunk-type l)))
general-list-polytime {_} {n} {Γ} (inr refl) program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
 , is-polytime k C N₀ (length l)
    (pr₁ (pr₁ (env [ lam list program ]ᵢ eager) (thunk-type l)))

\end{code}

A solver for a decision problem `decision` in the context `Γ` is a program
which decides it, together with a proof that it runs in polynomial time.

\begin{code}

P-solver : {n : ℕ} → Ctx n → (List Bool → Bool) → 𝓤₀ ̇
P-solver Γ decision
 = Σ program ꞉ Term (list ∷ Γ) nat
 , ((env : Env Γ) → to-decision-solver env program ∼ decision)
 × general-list-polytime (inl refl) program

_∈P : (decision : List Bool → Bool) → 𝓤₀ ̇
_∈P decision = Π n ꞉ ℕ , Π Γ ꞉ Ctx n , P-solver Γ decision

not' : {n : ℕ} → {Γ : Ctx n} → Term Γ (nat ⇒ nat)
not' = lam nat (if (var 𝟎) then suc zero else zero)

not'-not : {n : ℕ} {Γ : Ctx n}
         → (env : Env Γ)
         → nat-to-bool ∘ (env [ not' ]ₑ) ∘ bool-to-nat ∼ not
not'-not env true = refl
not'-not env false = refl

not'-not' : {n : ℕ} {Γ : Ctx n}
          → (env : Env Γ)
          → (env [ not' ]ₑ) ∼ (env [ not' ]ₑ) ∘ bool-to-nat ∘ nat-to-bool
not'-not' env zero = refl
not'-not' env (succ _) = refl

\end{code}

The programs which decide the negation, disjunction and conjunction of
decision problems, given programs for the original problems. They are
evaluated in a context with the input list duplicated, since each
program is applied to the input list.

\begin{code}

not-program : {n : ℕ} {Γ : Ctx n}
            → Term (list ∷ list ∷ Γ) nat
            → Term (list ∷ Γ) nat
not-program program = not' ∙ ((lam list program) ∙ (var 𝟎))

or-program : {n : ℕ} {Γ : Ctx n}
           → Term (list ∷ list ∷ Γ) nat
           → Term (list ∷ list ∷ Γ) nat
           → Term (list ∷ Γ) nat
or-program program₁ program₂
 = if (lam list program₁) ∙ (var 𝟎) then zero
   else ((lam list program₂) ∙ (var 𝟎))

and-program : {n : ℕ} {Γ : Ctx n}
            → Term (list ∷ list ∷ Γ) nat
            → Term (list ∷ list ∷ Γ) nat
            → Term (list ∷ Γ) nat
and-program program₁ program₂
 = if (lam list program₁) ∙ (var 𝟎) then ((lam list program₂) ∙ (var 𝟎))
   else suc zero

\end{code}

Arithmetic lemmas used to combine the polynomial bounds in the proofs
below. Throughout, `L` stands for the length of the input list.

\begin{code}

one-≤-not-zero : (L : ℕ) → 1 ≤ L → L ≠ 0
one-≤-not-zero L h eq = transport (1 ≤_) eq h

one-≤-power : (L m : ℕ) → 1 ≤ L → 1 ≤ L ^ m
one-≤-power L m h
 = transport (_≤ L ^ m) (exponentiation-of-one m)
    (exponentiation-preserves-order-right 1 L m h)

power-≤-left : (L k' k : ℕ) → 1 ≤ L → L ^ k' ≤ L ^ (k' + k)
power-≤-left L k' k h
 = exponentiation-preserves-order-left L k' (k' + k)
    (inl (one-≤-not-zero L h)) (≤-+ k' k)

power-≤-right : (L k' k : ℕ) → 1 ≤ L → L ^ k ≤ L ^ (k' + k)
power-≤-right L k' k h
 = exponentiation-preserves-order-left L k (k' + k)
    (inl (one-≤-not-zero L h)) (≤-+' k' k)

power-sum-bound : (C' C k' k L : ℕ)
                → 1 ≤ L
                → C' * L ^ k' + C * L ^ k ≤ (C' + C) * L ^ (k' + k)
power-sum-bound C' C k' k L h
 = transport (C' * L ^ k' + C * L ^ k ≤_)
    (distributivity-mult-over-addition' C' C (L ^ (k' + k)) ⁻¹)
    (≤-adding (C' * L ^ k') (C' * L ^ (k' + k)) (C * L ^ k) (C * L ^ (k' + k))
     (multiplication-preserves-order-left C' (L ^ k') (L ^ (k' + k))
      (power-≤-left L k' k h))
     (multiplication-preserves-order-left C (L ^ k) (L ^ (k' + k))
      (power-≤-right L k' k h)))

\end{code}

The time taken by the disjunction, and by the conjunction when the second
program takes more than one step, is bounded as follows.

\begin{code}

parallel-bound : (C' C k' k L : ℕ)
               → 1 ≤ L
               → succ (succ (succ (C' * L ^ k') + C * L ^ k))
               ≤ (C' + C + 3) * L ^ (k' + k)
parallel-bound C' C k' k L h
 = transport (_≤ succ (succ (succ (C' + C))) * L ^ (k' + k))
    (ap (succ ∘ succ) (succ-left (C' * L ^ k') (C * L ^ k))⁻¹)
    (≤-trans (succ (succ (succ (C' * L ^ k' + C * L ^ k))))
     (succ (succ (succ ((C' + C) * L ^ (k' + k)))))
     (succ (succ (succ (C' + C))) * L ^ (k' + k))
     (power-sum-bound C' C k' k L h)
     (transport (succ (succ (succ ((C' + C) * L ^ (k' + k)))) ≤_)
      (distributivity-mult-over-addition' (C' + C) 3 (L ^ (k' + k)) ⁻¹)
      (≤-n-monotone-left 3 (3 * L ^ (k' + k)) ((C' + C) * L ^ (k' + k))
       (multiplication-preserves-order-left 3 1 (L ^ (k' + k))
        (one-≤-power L (k' + k) h)))))

shift-bound : (C' C k' k L a : ℕ)
            → a ≤ C' * L ^ k'
            → 1 ≤ L
            → a + 4 ≤ (C' + C + 4) * L ^ (k' + k)
shift-bound C' C k' k L a p h
 = ≤-trans (a + 4) (C' * L ^ k' + 4) ((C' + C + 4) * L ^ (k' + k))
    p
    (≤-trans (C' * L ^ k' + 4) ((C' + C) * L ^ k' + 4)
     ((C' + C + 4) * L ^ (k' + k))
     (multiplication-preserves-order C' (C' + C) (L ^ k') (≤-+ C' C))
     (≤-trans ((C' + C) * L ^ k' + 4) ((C' + C) * L ^ (k' + k) + 4)
      ((C' + C + 4) * L ^ (k' + k))
      (multiplication-preserves-order-left (C' + C) (L ^ k') (L ^ (k' + k))
       (power-≤-left L k' k h))
      (transport ((C' + C) * L ^ (k' + k) + 4 ≤_)
       (distributivity-mult-over-addition' (C' + C) 4 (L ^ (k' + k)) ⁻¹)
       (≤-n-monotone-left 4 (4 * L ^ (k' + k)) ((C' + C) * L ^ (k' + k))
        (multiplication-preserves-order-left 4 1 (L ^ (k' + k))
         (one-≤-power L (k' + k) h))))))

\end{code}

Closure of P under negation.

\begin{code}

P-closure₁ : (decision : List Bool → Bool)
           → decision ∈P
           → (not ∘ decision) ∈P
P-closure₁ decision d∈P n Γ
 = not-program program , correctness' , timing' timing
 where
  open-d : P-solver (list ∷ Γ) decision
  open-d = d∈P (succ n) (list ∷ Γ)

  program : Term (list ∷ list ∷ Γ) nat
  program = pr₁ open-d

  correctness : (env : Env (list ∷ Γ))
              → to-decision-solver env program ∼ decision
  correctness = pr₁ (pr₂ open-d)

  timing : general-list-polytime (inl refl) program
  timing = pr₂ (pr₂ open-d)

  timing' : general-list-polytime (inl refl) program
          → general-list-polytime (inl refl) (not-program program)
  timing' (k , C , N₀ , f) = k , C + 5 , succ N₀ , f'
   where
    f' : Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
       , is-polytime k (C + 5) (succ N₀) (length l)
          (pr₁ (pr₁ (env [ lam list (not-program program) ]ᵢ eager)
           (thunk-type l)))
    f' xs env le
     = transport (λ z → succ z ≤ ((C + 5) * (length xs) ^ k))
        (adding-times-lemma (inl refl) (inl refl) ((0 , return xs) ∷Eᵢ env)
         (if var 𝟎 then suc zero else zero) r)
        (≤-trans (succ (succ (pr₁ c) + pr₁ r))
         (succ (4 + C * (length xs) ^ k)) ((C + 5) * (length xs) ^ k)
         II
         (transport (_≤ (C + 5) * (length xs) ^ k)
          (succ-left 4 (C * (length xs) ^ k))
          (transport (5 + C * (length xs) ^ k ≤_) ((III)⁻¹)
           (≤-n-monotone-right 5 (5 * ((length xs) ^ k))
            (C * ((length xs) ^ k))
            (multiplication-preserves-order-left 5 1 ((length xs) ^ k)
             (one-≤-power (length xs) k length-non-zero))))))
     where
      env' : Envᵢ (list ∷ list ∷ Γ)
      env' = (0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env

      r : Σ t ꞉ ℕ , Thunk t ℕ
      r = env' [ program ]ᵢ eager

      c : Σ t ꞉ ℕ , Thunk t ℕ
      c = thunk-if {nat} (0 , return (force (pr₂ r)))
           (2 , (√ (√ return 1))) (1 , (√ return 0))

      I : pr₁ c ≤ 3
      I = thunk-if-lemma (inl refl) (0 , return (force (pr₂ r)))
           (2 , (√ (√ return 1))) (1 , (√ return 0))

      II : succ (pr₁ c) + pr₁ r ≤ 4 + C * (length xs) ^ k
      II = ≤-adding (succ (pr₁ c)) 4 (pr₁ r) (C * (length xs) ^ k)
            I
            (f xs ((0 , return xs) ∷Eᵢ env)
             (≤-trans N₀ (succ N₀) (length xs) (≤-succ N₀) le))

      III : (C + 5) * ((length xs) ^ k)
          ＝ (5 * ((length xs) ^ k)) + (C * ((length xs) ^ k))
      III
       = (C + 5) * ((length xs) ^ k)
       ＝⟨ ap (_* ((length xs) ^ k)) (+-comm C 5) ⟩
         (5 + C) * ((length xs) ^ k)
       ＝⟨ distributivity-mult-over-addition' 5 C ((length xs) ^ k) ⟩
         5 * length xs ^ k + C * length xs ^ k
       ∎

      length-non-zero : 0 < length xs
      length-non-zero = ≤-trans 1 (succ N₀) (length xs) ⋆ le

  correctness' : (env : Env Γ)
               → to-decision-solver env (not-program program)
               ∼ not ∘ decision
  correctness' env xs
   = nat-to-bool (if' (E [ program ]ₑ) then' 1 else' 0)
   ＝⟨ ap nat-to-bool (ite-nat-bool-inverse (E [ program ]ₑ)) ⟩
     nat-to-bool
      (if' bool-to-nat (nat-to-bool (E [ program ]ₑ)) then' 1 else' 0)
   ＝⟨ ap (λ z → nat-to-bool (if' z then' 1 else' 0))
        (ap bool-to-nat (correctness (map bool-to-nat xs ∷E env) xs)) ⟩
     nat-to-bool (if' bool-to-nat (decision xs) then' 1 else' 0)
   ＝⟨ not'-not env (decision xs) ⟩
     not (decision xs)
   ∎
   where
    E : Env (list ∷ list ∷ Γ)
    E = map bool-to-nat xs ∷E map bool-to-nat xs ∷E env

ite-or : (a b : ℕ)
       → nat-to-bool (if' a then' 0 else' b)
       ＝ (nat-to-bool a) || (nat-to-bool b)
ite-or zero b = refl
ite-or (succ _) b = refl

\end{code}

Closure of P under disjunction.

\begin{code}

P-closure₂ : (d₁ d₂ : List Bool → Bool)
           → (d₁ ∈P)
           → (d₂ ∈P)
           → ((λ l → d₁ l || d₂ l) ∈P)
P-closure₂ d₁ d₂ d₁∈P d₂∈P n Γ
 = or-program program₁ program₂ , (correctness , timing' timing₁ timing₂)
 where
  open-d₁ : P-solver (list ∷ Γ) d₁
  open-d₁ = d₁∈P (succ n) (list ∷ Γ)

  open-d₂ : P-solver (list ∷ Γ) d₂
  open-d₂ = d₂∈P (succ n) (list ∷ Γ)

  program₁ : Term (list ∷ list ∷ Γ) nat
  program₁ = pr₁ open-d₁

  program₂ : Term (list ∷ list ∷ Γ) nat
  program₂ = pr₁ open-d₂

  timing₁ : general-list-polytime (inl refl) program₁
  timing₁ = pr₂ (pr₂ open-d₁)

  timing₂ : general-list-polytime (inl refl) program₂
  timing₂ = pr₂ (pr₂ open-d₂)

  correctness₁ : (env : Env (list ∷ Γ))
               → to-decision-solver env program₁ ∼ d₁
  correctness₁ = pr₁ (pr₂ open-d₁)

  correctness₂ : (env : Env (list ∷ Γ))
               → to-decision-solver env program₂ ∼ d₂
  correctness₂ = pr₁ (pr₂ open-d₂)

  correctness : (env : Env Γ)
              → to-decision-solver env (or-program program₁ program₂)
              ∼ (λ l → d₁ l || d₂ l)
  correctness env x
   = nat-to-bool (if' (E [ program₁ ]ₑ) then' 0 else' (E [ program₂ ]ₑ))
   ＝⟨ ite-or (E [ program₁ ]ₑ) (E [ program₂ ]ₑ) ⟩
     nat-to-bool (E [ program₁ ]ₑ) || nat-to-bool (E [ program₂ ]ₑ)
   ＝⟨ ap₂ _||_ (correctness₁ (map bool-to-nat x ∷E env) x)
        (correctness₂ (map bool-to-nat x ∷E env) x) ⟩
     d₁ x || d₂ x
   ∎
   where
    E : Env (list ∷ list ∷ Γ)
    E = map bool-to-nat x ∷E map bool-to-nat x ∷E env

  timing' : general-list-polytime (inl refl) program₁
          → general-list-polytime (inl refl) program₂
          → general-list-polytime (inl refl) (or-program program₁ program₂)
  timing' (k , C , N₀ , f) (k' , C' , N₀' , f')
   = (k' + k) , ((C' + C) + 3) , succ (N₀' + N₀) , new-f
   where
    new-f : Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
          , is-polytime (k' + k) ((C' + C) + 3) (succ (N₀' + N₀)) (length l)
             (pr₁ (pr₁ (env [ lam list (or-program program₁ program₂) ]ᵢ
              eager) (thunk-type l)))
    new-f xs env le
     = ≤-trans
        (pr₁ (pr₁ (env [ lam list (or-program program₁ program₂) ]ᵢ eager)
         (thunk-type xs)))
        (succ (succ (succ (pr₁ r₂) + pr₁ r₁)))
        (((C' + C) + 3) * (length xs) ^ (k' + k))
        I
        (≤-trans (succ (succ (succ (pr₁ r₂) + pr₁ r₁)))
         (succ (succ (succ (C' * (length xs) ^ k') + C * (length xs) ^ k)))
         (((C' + C) + 3) * (length xs) ^ (k' + k))
         (≤-adding (succ (pr₁ r₂)) (succ (C' * (length xs) ^ k')) (pr₁ r₁)
          (C * (length xs) ^ k)
          (f' xs ((0 , return xs) ∷Eᵢ env) le₂)
          (f xs ((0 , return xs) ∷Eᵢ env) le₁))
         (parallel-bound C' C k' k (length xs) (≤-trans 1 (succ (N₀' + N₀))
          (length xs) ⋆ le)))
     where
      env' : Envᵢ (list ∷ list ∷ Γ)
      env' = (0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env

      r₁ : Σ t ꞉ ℕ , Thunk t ℕ
      r₁ = env' [ program₁ ]ᵢ eager

      r₂ : Σ t ꞉ ℕ , Thunk t ℕ
      r₂ = env' [ program₂ ]ᵢ eager

      le₁ : N₀ ≤ length xs
      le₁ = ≤-trans N₀ (succ (N₀' + N₀)) (length xs)
             (≤-trans N₀ (N₀' + N₀) (succ (N₀' + N₀))
              (≤-+' N₀' N₀) (≤-succ (N₀' + N₀)))
             le

      le₂ : N₀' ≤ length xs
      le₂ = ≤-trans N₀' (succ (N₀' + N₀)) (length xs)
             (≤-trans N₀' (N₀' + N₀) (succ (N₀' + N₀))
              (≤-+ N₀' N₀) (≤-succ (N₀' + N₀)))
             le

      I : get-time (inl refl)
           (thunk-if {nat} r₁ (1 , (√ return 0)) (inc-nat r₂))
        ≤ succ (succ (pr₁ r₂) + pr₁ r₁)
      I = thunk-if-lemma (inl refl) r₁ (1 , (√ return 0)) (inc-nat r₂)

ite-and : (a b : ℕ)
        → nat-to-bool (if' a then' b else' 1)
        ＝ (nat-to-bool a) && (nat-to-bool b)
ite-and zero b = refl
ite-and (succ _) b = refl

\end{code}

Closure of P under conjunction.

\begin{code}

P-closure₃ : (d₁ d₂ : List Bool → Bool)
           → (d₁ ∈P)
           → (d₂ ∈P)
           → ((λ l → d₁ l && d₂ l) ∈P)
P-closure₃ d₁ d₂ d₁∈P d₂∈P n Γ
 = and-program program₁ program₂ , correctness , timing timing₁ timing₂
 where
  open-d₁ : P-solver (list ∷ Γ) d₁
  open-d₁ = d₁∈P (succ n) (list ∷ Γ)

  open-d₂ : P-solver (list ∷ Γ) d₂
  open-d₂ = d₂∈P (succ n) (list ∷ Γ)

  program₁ : Term (list ∷ list ∷ Γ) nat
  program₁ = pr₁ open-d₁

  program₂ : Term (list ∷ list ∷ Γ) nat
  program₂ = pr₁ open-d₂

  correctness₁ : (env : Env (list ∷ Γ))
               → to-decision-solver env program₁ ∼ d₁
  correctness₁ = pr₁ (pr₂ open-d₁)

  correctness₂ : (env : Env (list ∷ Γ))
               → to-decision-solver env program₂ ∼ d₂
  correctness₂ = pr₁ (pr₂ open-d₂)

  correctness : (env : Env Γ)
              → to-decision-solver env (and-program program₁ program₂)
              ∼ (λ l → d₁ l && d₂ l)
  correctness env xs
   = nat-to-bool (if' (E [ program₁ ]ₑ) then' (E [ program₂ ]ₑ) else' 1)
   ＝⟨ ite-and (E [ program₁ ]ₑ) (E [ program₂ ]ₑ) ⟩
     nat-to-bool (E [ program₁ ]ₑ) && nat-to-bool (E [ program₂ ]ₑ)
   ＝⟨ ap₂ _&&_ (correctness₁ (map bool-to-nat xs ∷E env) xs)
        (correctness₂ (map bool-to-nat xs ∷E env) xs) ⟩
     d₁ xs && d₂ xs
   ∎
   where
    E : Env (list ∷ list ∷ Γ)
    E = map bool-to-nat xs ∷E map bool-to-nat xs ∷E env

  timing₁ : general-list-polytime (inl refl) program₁
  timing₁ = pr₂ (pr₂ open-d₁)

  timing₂ : general-list-polytime (inl refl) program₂
  timing₂ = pr₂ (pr₂ open-d₂)

  timing : general-list-polytime (inl refl) program₁
         → general-list-polytime (inl refl) program₂
         → general-list-polytime (inl refl) (and-program program₁ program₂)
  timing (k' , C' , N₀' , f') (k , C , N₀ , f)
   = k' + k , ((C' + C) + 4 , (succ (N₀' + N₀) , new-f))
   where
    new-f : Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ
          , is-polytime (k' + k) (C' + C + 4) (succ (N₀' + N₀)) (length l)
             (pr₁ (pr₁ (env [ lam list (and-program program₁ program₂) ]ᵢ
              eager) (thunk-type l)))
    new-f xs env le
     = ≤-trans
        (pr₁ (pr₁ (env [ lam list (and-program program₁ program₂) ]ᵢ eager)
         (thunk-type xs)))
        (succ (succ (max (succ (pr₁ r₂)) 2 + pr₁ r₁)))
        ((C' + C + 4) * length xs ^ (k' + k))
        I
        (γ (≤-decidable (pr₁ r₂) 1))
     where
      env' : Envᵢ (list ∷ list ∷ Γ)
      env' = (0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env

      r₁ : Σ t ꞉ ℕ , Thunk t ℕ
      r₁ = env' [ program₁ ]ᵢ eager

      r₂ : Σ t ꞉ ℕ , Thunk t ℕ
      r₂ = env' [ program₂ ]ᵢ eager

      le₁ : N₀' ≤ length xs
      le₁ = ≤-trans N₀' (succ (N₀' + N₀)) (length xs)
             (≤-trans N₀' (N₀' + N₀) (succ (N₀' + N₀))
              (≤-+ N₀' N₀) (≤-succ (N₀' + N₀)))
             le

      le₂ : N₀ ≤ length xs
      le₂ = ≤-trans N₀ (succ (N₀' + N₀)) (length xs)
             (≤-trans N₀ (N₀' + N₀) (succ (N₀' + N₀))
              (≤-+' N₀' N₀) (≤-succ (N₀' + N₀)))
             le

      positive : 1 ≤ length xs
      positive = ≤-trans 1 (succ (N₀' + N₀)) (length xs) ⋆ le

      I : get-time (inl refl)
           (thunk-if {nat} r₁ (inc-nat r₂) (2 , (√ (√ return 1))))
        ≤ succ (max (succ (pr₁ r₂)) 2 + pr₁ r₁)
      I = thunk-if-lemma (inl refl) r₁ (inc-nat r₂) (2 , (√ (√ return 1)))

      II : pr₁ r₂ ≤ 1 → max (succ (pr₁ r₂)) 2 ＝ 2
      II le' = ap succ (max-ord→ (pr₁ r₂) 1 le')

      III : ¬ (pr₁ r₂ ≤ 1) → max (succ (pr₁ r₂)) 2 ＝ succ (pr₁ r₂)
      III gt
       = max (succ (pr₁ r₂)) 2
       ＝⟨ max-comm (succ (pr₁ r₂)) 2 ⟩
         max 2 (succ (pr₁ r₂))
       ＝⟨ ap succ (max-ord→ 1 (pr₁ r₂)
            (≤-trans 1 2 (pr₁ r₂) ⋆ (not-less-bigger-or-equal 2 (pr₁ r₂) gt))) ⟩
         succ (pr₁ r₂)
       ∎

      I' : succ (pr₁ r₂) + pr₁ r₁ ＝ succ (pr₁ r₁) + pr₁ r₂
      I'
       = succ (pr₁ r₂) + pr₁ r₁
       ＝⟨ succ-left (pr₁ r₂) (pr₁ r₁) ⟩
         pr₁ r₂ + succ (pr₁ r₁)
       ＝⟨ +-comm (pr₁ r₂) (succ (pr₁ r₁)) ⟩
         succ (pr₁ r₁) + pr₁ r₂
       ∎

      γ : (pr₁ r₂ ≤ 1) ∔ ¬ (pr₁ r₂ ≤ 1)
        → succ (succ (max (succ (pr₁ r₂)) 2 + pr₁ r₁))
        ≤ ((C' + C + 4) * length xs ^ (k' + k))
      γ (inl le')
       = transport (_≤ ((C' + C + 4) * length xs ^ (k' + k)))
          (ap (λ z → succ (succ (z + pr₁ r₁))) (II le' ⁻¹))
          (transport (λ z → succ (succ z) ≤ (C' + C + 4) * length xs ^ (k' + k))
           (+-comm (pr₁ r₁) 2)
           (shift-bound C' C k' k (length xs) (pr₁ r₁)
            (f' xs ((0 , return xs) ∷Eᵢ env) le₁) positive))
      γ (inr nle)
       = ≤-trans (succ (succ (max (succ (pr₁ r₂)) 2 + pr₁ r₁)))
          ((C' + C + 3) * length xs ^ (k' + k))
          ((C' + C + 4) * length xs ^ (k' + k))
          (transport
           (λ z → succ (succ (z + pr₁ r₁))
                ≤ (C' + C + 3) * length xs ^ (k' + k))
           (III nle ⁻¹)
           (≤-trans (succ (succ (succ (pr₁ r₂) + pr₁ r₁)))
            (succ (succ (succ (C' * (length xs) ^ k')
             + C * (length xs) ^ k)))
            ((C' + C + 3) * length xs ^ (k' + k))
            (transport (_≤ succ (C' * (length xs) ^ k') + C * (length xs) ^ k)
             (I' ⁻¹)
             (≤-adding (succ (pr₁ r₁)) (succ (C' * (length xs) ^ k'))
              (pr₁ r₂) (C * (length xs) ^ k)
              (f' xs ((0 , return xs) ∷Eᵢ env) le₁)
              (f xs ((0 , return xs) ∷Eᵢ env) le₂)))
            (parallel-bound C' C k' k (length xs) positive)))
          (multiplication-preserves-order
           (succ (succ (succ (C' + C))))
           (succ (succ (succ (succ (C' + C)))))
           (length xs ^ (k' + k))
           (≤-succ (C' + C)))

\end{code}
