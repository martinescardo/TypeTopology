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
                  → (program : Term (list ∷ Γ) list) → 𝓤₀ ̇
is-binary-program {n} {Γ} program
 = (env : Env Γ) → (xs : List ℕ) → (all-binary xs)
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

map-inverse : {X Y : 𝓤₀ ̇} → {f : Y → X} → {g : X → Y} → f inverse-of g
            → (map f) inverse-of (map g)
map-inverse eq [] = refl
map-inverse eq (x ∷ l) = ap₂ _∷_ (eq x) (map-inverse eq l)

map-bool-nat-inverse : (map nat-to-bool) inverse-of (map bool-to-nat)
map-bool-nat-inverse = map-inverse bool-nat-inverse

ite-nat-bool-inverse : {X : 𝓤₀ ̇} {x y : X} → (n : ℕ)
                     → if' n then' x else' y
                     ＝ if' bool-to-nat (nat-to-bool n) then' x else' y
ite-nat-bool-inverse zero = refl
ite-nat-bool-inverse (succ n) = refl

map-nat-bool-binary-list : (xs : List ℕ) → (all-binary xs)
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
                               → (env : Env Γ) → (r : Reduction Γ)
                               → (xs : List ℕ) → (all-binary xs)
                               → (map bool-to-nat (map nat-to-bool
                                 ((xs ∷E env) [ pr₁ r ]ₑ)))
                               ＝ ((xs ∷E env) [ (pr₁ r) ]ₑ)
map-nat-bool-inverse-reduction env r xs all-binary
 = map-nat-bool-binary-list ((xs ∷E env) [ pr₁ r ]ₑ) ((pr₂ r) env xs all-binary)

to-decision-solver : {n : ℕ} {Γ : Ctx n} → (env : Env Γ)
                   → Term (list ∷ Γ) nat → List Bool → Bool
to-decision-solver env program l
 = nat-to-bool ((env [ lam list program ]ₑ) (map bool-to-nat l))


general-list-polytime : {τ : LType} {n : ℕ} {Γ : Ctx n}
                      → ((τ ＝ nat) ∔ (τ ＝ list)) → Term (list ∷ Γ) τ → 𝓤₀ ̇
general-list-polytime {_} {n} {Γ} (inl refl) program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ ,
   is-polytime k C N₀ (length l) (pr₁ (pr₁ (env [ lam list program ]ᵢ eager)
   (thunk-type l)))
general-list-polytime {_} {n} {Γ} (inr refl) program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Π l ꞉ List ℕ , Π env ꞉ Envᵢ Γ ,
   is-polytime k C N₀ (length l) (pr₁ (pr₁ (env [ lam list program ]ᵢ eager)
   (thunk-type l)))

_∈P : (decision : List Bool → Bool) → 𝓤₀ ̇
_∈P decision = Π n ꞉ ℕ , Π Γ ꞉ Ctx n ,
                Σ program ꞉ Term (list ∷ Γ) nat ,
                ((env : Env Γ)
                → (l : List Bool)
                → (to-decision-solver env program l ＝ decision l))
                × (general-list-polytime (inl refl) program)

not' : {n : ℕ} → {Γ : Ctx n} → Term Γ (nat ⇒ nat)
not' = lam nat (if (var 𝟎) then suc zero else zero)

not'-not : {n : ℕ} {Γ : Ctx n} → (env : Env Γ)
         → nat-to-bool ∘ (env [ not' ]ₑ) ∘ bool-to-nat ∼ not
not'-not env true = refl
not'-not env false = refl

not'-not' : {n : ℕ} {Γ : Ctx n} → (env : Env Γ)
          → (env [ not' ]ₑ) ∼ (env [ not' ]ₑ) ∘ bool-to-nat ∘ nat-to-bool
not'-not' env zero = refl
not'-not' env (succ _) = refl

P-closure₁ : (decision : List Bool → Bool)
           → decision ∈P
           → (not ∘ decision) ∈P
P-closure₁ decision d∈P n Γ
 = not' ∙ ((lam list program) ∙ (var 𝟎)) , correctness' , timing' timing
 where
  open-d : Sigma (Term (list ∷ (list ∷ Γ)) nat)
           (λ program →
              ((env : Env (list ∷ Γ)) →
                to-decision-solver env program ∼ decision)
                × general-list-polytime (inl refl) program)
  open-d = d∈P (succ n) (list ∷ Γ)

  program : Term (list ∷ list ∷ Γ) nat
  program = pr₁ open-d

  correctness : (env : Env (list ∷ Γ)) →
                to-decision-solver env program ∼ decision
  correctness = pr₁ (pr₂ open-d)

  timing : general-list-polytime (inl refl) (pr₁ open-d)
  timing = pr₂ (pr₂ open-d)

  I : (env : Envᵢ Γ) → (xs : List ℕ) → (pr₁
      (thunk-if {nat}
        (0 ,
        return
        (force
          (pr₂
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
            pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
        (2 , (√ (√ return 1))) (1 , (√ return 0)))) ≤ 3
  I env xs
   = thunk-if-lemma (inl refl) ((0 ,
     return
     (force
     (pr₂
     (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
     pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))) (2 , (√ (√ return 1)))
     (1 , (√ return 0))

  timing' : (general-list-polytime (inl refl) program)
          → general-list-polytime (inl refl)
            (not' ∙ (lam list program ∙ var 𝟎))
  timing' (k , C , N₀ , f) = k , C + 5 , succ N₀ , f'
   where
    f' : Pi (List ℕ)
         (λ l →
         Pi (Envᵢ Γ)
         (λ env →
         is-polytime k (C + 5) (succ N₀) (length l)
         (pr₁
         (pr₁
         (env [ lam list (not' ∙ (lam list program ∙ var 𝟎)) ]ᵢ eager)
         (thunk-type l)))))
    f' xs env le
     = transport (λ z → succ z ≤ ((C + 5) * (length xs) ^ k))
       (adding-times-lemma (inl refl) (inl refl) ((0 , return xs) ∷Eᵢ env)
       (if var 𝟎 then suc zero else zero) (((0 , return xs) ∷Eᵢ
       (0 , return xs) ∷Eᵢ env) [
         pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
         (≤-trans (succ
          (succ
         (pr₁
           (thunk-if {nat}
         (0 ,
          return
          (force
           (pr₂
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
           (2 , (√ (√ return 1))) (1 , (√ return 0))))
         +
         pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
         (succ (4 + C * (length xs) ^ k)) ((C + 5) * (length xs) ^ k)
         II (transport (_≤ (C + 5) * (length xs) ^ k)
         (succ-left 4 (C * (length xs) ^ k))
         (transport (5 + C * (length xs) ^ k ≤_) ((III)⁻¹)
         (≤-n-monotone-right 5 (5 * ((length xs) ^ k)) (C * ((length xs) ^ k))
          (multiplication-preserves-order-left 5 1 ((length xs) ^ k)
          (transport (_≤ (length xs) ^ k) (exponentiation-of-one k)
          (exponentiation-preserves-order-right 1 (length xs) k
          length-non-zero)))))))
     where
       II : succ
            (pr₁
            (thunk-if {nat}
            (0 ,
            return
            (force
            (pr₂
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
            pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
            (2 , (√ (√ return 1))) (1 , (√ return 0)))) +  pr₁
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
            pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager) ≤ 4 + C * (length xs) ^ k
       II = ≤-adding (succ (pr₁
            (thunk-if {nat} (0 ,  return
            (force
            (pr₂ (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
            pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
            (2 , (√ (√ return 1))) (1 , (√ return 0))))) 4 (pr₁
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
            pr₁ (d∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) (C * (length xs) ^ k)
            (I env xs) (f xs ((0 , return xs) ∷Eᵢ env) (≤-trans N₀ (succ N₀)
            (length xs) (≤-succ N₀) le))

       III : (C + 5) * ((length xs) ^ k)
           ＝ (5 * ((length xs) ^ k)) + (C * ((length xs) ^ k))
       III = (C + 5) * ((length xs) ^ k)
             ＝⟨ ap (_* ((length xs) ^ k)) (+-comm C 5) ⟩
             (5 + C) * ((length xs) ^ k)
             ＝⟨ distributivity-mult-over-addition' 5 C ((length xs) ^ k) ⟩
             5 * length xs ^ k + C * length xs ^ k ∎

       length-non-zero : 0 < length xs
       length-non-zero = ≤-trans 1 (succ N₀) (length xs) ⋆ le

  correctness' : (env : Env Γ)
               → to-decision-solver env (not' ∙ (lam list program ∙ var 𝟎)) ∼
                 not ∘ decision
  correctness' env xs
   = nat-to-bool (if' (map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [
     pr₁ (d∈P (succ n) (list ∷ Γ)) ]ₑ then' 1 else' 0) ＝⟨ ap nat-to-bool
     (ite-nat-bool-inverse ((map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [
     pr₁ (d∈P (succ n) (list ∷ Γ)) ]ₑ)) ⟩
     nat-to-bool (if' bool-to-nat (nat-to-bool
     ((map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [
     pr₁ (d∈P (succ n) (list ∷ Γ)) ]ₑ)) then' 1 else' 0)
     ＝⟨ ap (λ z → nat-to-bool (if' z then' 1 else' 0))
     (ap bool-to-nat (correctness (map bool-to-nat xs ∷E env) xs)) ⟩
     nat-to-bool (if' bool-to-nat (decision xs) then' 1 else' 0)
     ＝⟨ not'-not env (decision xs) ⟩
     not (decision xs) ∎

ite-or : (a b : ℕ)
       → nat-to-bool (if' a then' 0 else' b)
       ＝ (nat-to-bool a) || (nat-to-bool b)
ite-or zero b = refl
ite-or (succ _) b = refl

P-closure₂ : (d₁ d₂ : List Bool → Bool)
           → (d₁ ∈P) → (d₂ ∈P)
           → ((λ l → d₁ l || d₂ l) ∈P)
P-closure₂ d₁ d₂ d₁∈P d₂∈P n Γ
 = (if (lam list program₁) ∙ (var 𝟎) then zero
   else ((lam list program₂) ∙ (var 𝟎)))
    , (correctness , timing' timing₁ timing₂)
 where
  open-d₁ : Sigma (Term (list ∷ (list ∷ Γ)) nat)
            (λ program →
            ((env : Env (list ∷ Γ)) →
            to-decision-solver env program ∼ d₁)
            × general-list-polytime (inl refl) program)
  open-d₁ = d₁∈P (succ n) (list ∷ Γ)

  open-d₂ : Sigma (Term (list ∷ (list ∷ Γ)) nat)
            (λ program →
               ((env : Env (list ∷ Γ)) →
                 to-decision-solver env program ∼ d₂)
               × general-list-polytime (inl refl) program)
  open-d₂ = d₂∈P (succ n) (list ∷ Γ)

  program₁ : Term (list ∷ (list ∷ Γ)) nat
  program₁ = pr₁ open-d₁

  program₂ : Term (list ∷ (list ∷ Γ)) nat
  program₂ = pr₁ open-d₂

  timing₁ : Σ
            (λ k →
            Sigma ℕ
            (λ C →
            Sigma ℕ
            (λ N₀ →
            Pi (List ℕ)
            (λ l →
            Pi (Envᵢ (list ∷ Γ))
            (λ env →
            is-polytime k C N₀ (length l)
            (pr₁
            (pr₁ (env [ lam list (pr₁ open-d₁) ]ᵢ eager) (thunk-type l))))))))
  timing₁ = pr₂ (pr₂ open-d₁)

  timing₂ : Σ
            (λ k →
            Sigma ℕ
            (λ C →
            Sigma ℕ
            (λ N₀ →
            Pi (List ℕ)
            (λ l →
            Pi (Envᵢ (list ∷ Γ))
            (λ env →
            is-polytime k C N₀ (length l)
            (pr₁
            (pr₁ (env [ lam list (pr₁ open-d₂) ]ᵢ eager) (thunk-type l))))))))
  timing₂ = pr₂ (pr₂ open-d₂)

  correctness₁ : (env : Env (list ∷ Γ))
               → to-decision-solver env (pr₁ open-d₁) ∼ d₁
  correctness₁ = pr₁ (pr₂ open-d₁)

  correctness₂ : (env : Env (list ∷ Γ))
               → to-decision-solver env (pr₁ open-d₂) ∼ d₂
  correctness₂ = pr₁ (pr₂ open-d₂)

  correctness : (env : Env Γ) →
                to-decision-solver env
                (if lam list program₁ ∙ var 𝟎 then zero else
                (lam list program₂ ∙ var 𝟎))
                ∼ (λ l → d₁ l || d₂ l)
  correctness env x
   = nat-to-bool
     (if'
     (map bool-to-nat x ∷E map bool-to-nat x ∷E env) [
     pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ₑ
     then' 0 else'
     ((map bool-to-nat x ∷E map bool-to-nat x ∷E env) [
     pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ₑ)) ＝⟨ ite-or
     ((map bool-to-nat x ∷E map bool-to-nat x ∷E env) [
     pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ₑ) ((map bool-to-nat x
     ∷E map bool-to-nat x ∷E env) [
     pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ₑ) ⟩
     (nat-to-bool ((map bool-to-nat x ∷E map bool-to-nat x ∷E env) [
     pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ₑ))
     || nat-to-bool ((map bool-to-nat x ∷E map bool-to-nat x ∷E env) [
     pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ₑ) ＝⟨ ap₂ _||_ (correctness₁
     (map bool-to-nat x ∷E env) x) (correctness₂ (map bool-to-nat x ∷E env) x) ⟩
     d₁ x || d₂ x ∎

  timing' : Σ
            (λ k →
            Sigma ℕ
            (λ C →
            Sigma ℕ
            (λ N₀ →
            Pi (List ℕ)
            (λ l →
            Pi (Envᵢ (list ∷ Γ))
            (λ env →
            is-polytime k C N₀ (length l)
            (pr₁
            (pr₁ (env [ lam list (pr₁ open-d₁) ]ᵢ eager)
            (thunk-type l))))))))
          → Σ
            (λ k →
            Sigma ℕ
            (λ C →
            Sigma ℕ
            (λ N₀ →
            Pi (List ℕ)
            (λ l →
            Pi (Envᵢ (list ∷ Γ))
            (λ env →
            is-polytime k C N₀ (length l)
            (pr₁
            (pr₁ (env [ lam list (pr₁ open-d₂) ]ᵢ eager) (thunk-type l))))))))
          → general-list-polytime (inl refl)
            (if lam list program₁ ∙ var 𝟎 then zero else
            (lam list program₂ ∙ var 𝟎))
  timing' (k , C , N₀ , f) (k' , C' , N₀' , f')
   = (k' + k) , ((C' + C) + 3) , succ (N₀' + N₀) , new-f
   where
    new-f : Pi (List ℕ)
            (λ l →
            Pi (Envᵢ Γ)
            (λ env →
            is-polytime (k' + k) ((C' + C) + 3) (succ (N₀' + N₀)) (length l)
            (pr₁
            (pr₁
            (env [
            lam list
            (if lam list program₁ ∙ var 𝟎 then zero else
            (lam list program₂ ∙ var 𝟎))
            ]ᵢ eager)
            (thunk-type l)))))
    new-f xs env le
     = ≤-trans (pr₁
       (pr₁
       (env [
       lam list
       (if lam list program₁ ∙ var 𝟎 then zero else
       (lam list program₂ ∙ var 𝟎))
       ]ᵢ eager)
       (thunk-type xs)))
       (succ (succ
       ((succ
       (pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
       pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
       +
       pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
       pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
       (((C' + C) + 3) * (length xs) ^ (k' + k))
       I
       (≤-trans (succ
       (succ
       (succ
       (pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
       pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
       +
       pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
       pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
       (succ (succ (succ (C' * (length xs) ^ k')
       + C * (length xs) ^ k)))
       (((C' + C) + 3) * (length xs) ^ (k' + k))
       (≤-adding (succ (pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
       pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
       (succ (C' * (length xs) ^ k'))
       (pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
       (C * (length xs) ^ k)
       (f' xs ((0 , return xs) ∷Eᵢ env)
       (≤-trans N₀' (succ (N₀' + N₀)) (length xs)
       (≤-trans N₀' (N₀' + N₀) (succ (N₀' + N₀))
       (≤-+ N₀' N₀) (≤-succ (N₀' + N₀))) le))
       (f xs ((0 , return xs) ∷Eᵢ env)
       ((≤-trans N₀ (succ (N₀' + N₀)) (length xs)
       (≤-trans N₀ (N₀' + N₀) (succ (N₀' + N₀))
       (≤-+' N₀' N₀) (≤-succ (N₀' + N₀))) le))))
       (transport (_≤ (succ (succ (succ (C' + C))) * length xs ^ (k' + k)))
       (ap (succ ∘ succ) (succ-left (C' * length xs ^ k')
       (C * length xs ^ k))⁻¹)
       (≤-trans (succ (succ (succ (C' * length xs ^ k' + C * length xs ^ k))))
       (succ (succ (succ ((C' + C) * length xs ^ (k' + k)))))
       (succ (succ (succ (C' + C))) * length xs ^ (k' + k))
       V
       (transport (succ (succ (succ ((C' + C) * rec 1 (_*_ (length xs))
       (k' + k))))
       ≤_)
       (VI ⁻¹) (≤-n-monotone-left 3 (3 * (length xs) ^ (k' + k))
       ((C' + C) * (length xs) ^ (k' + k))
       (multiplication-preserves-order-left 3 1 (length xs ^ (k' + k))
       (transport (_≤ (length xs ^ (k' + k)))
       (exponentiation-of-one (k' + k))
       (exponentiation-preserves-order-right 1 (length xs) (k' + k)
       (≤-trans 1 (succ (N₀' + N₀)) (length xs)
       ⋆ le)))))))))
     where
      I : get-time (inl refl)
          (thunk-if {nat}
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)
          (1 , (√ return 0))
          (inc-nat
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
          ≤
          succ
          ((succ
          (pr₁
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
          +
          pr₁
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
      I = thunk-if-lemma (inl refl) (((0 , return xs)
          ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager) (1 , (√ return 0))
          (inc-nat (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))

      II : length xs ≠ 0
      II eq = transport (succ (N₀' + N₀) ≤_) eq le

      III : (length xs ^ k') ≤
            (length xs ^ (k' + k))
      III = exponentiation-preserves-order-left (length xs) k'
            (k' + k) (inl II)
            (≤-+ k' k)

      IV : (length xs ^ k) ≤
           (length xs ^ (k' + k))
      IV = exponentiation-preserves-order-left (length xs) k
           (k' + k) (inl II)
           (≤-+' k' k)

      V : (C' * length xs ^ k' + C * length xs ^ k) ≤ (C' + C)
          * (length xs ^ (k' + k))
      V = transport ((C' * length xs ^ k' + C * length xs ^ k) ≤_)
          (distributivity-mult-over-addition' C' C
          (length xs ^ (k' + k)) ⁻¹)
          (≤-adding (C' * (length xs) ^ k')
          (C' * (length xs) ^ (k' + k))
          (C * (length xs) ^ k) (C * (length xs) ^ (k' + k))
          (multiplication-preserves-order-left C' ((length xs) ^ k')
          ((length xs) ^ (k' + k)) III)
          ((multiplication-preserves-order-left C ((length xs) ^ k)
          ((length xs) ^ (k' + k)) IV)))

      VI : ((C' + C) + 3) * (length xs) ^ (k' + k)
         ＝ (C' + C) * (length xs) ^ (k' + k)
            + 3 * (length xs) ^ (k' + k)
      VI = distributivity-mult-over-addition' (C' + C) 3
           ((length xs) ^ (k' + k))

ite-and : (a b : ℕ) → nat-to-bool (if' a then' b else' 1)
        ＝ (nat-to-bool a) && (nat-to-bool b)
ite-and zero b = refl
ite-and (succ _) b = refl

P-closure₃ : (d₁ d₂ : List Bool → Bool) → (d₁ ∈P) → (d₂ ∈P)
           → ((λ l → d₁ l && d₂ l) ∈P)
P-closure₃ d₁ d₂ d₁∈P d₂∈P n Γ
 = (if (lam list program₁) ∙ (var 𝟎) then ((lam list program₂)
   ∙ (var 𝟎)) else suc zero) ,
   correctness , timing timing₁ timing₂
 where
  open-d₁ : Sigma (Term (list ∷ (list ∷ Γ)) nat)
            (λ program →
            ((env : Env (list ∷ Γ)) →
            to-decision-solver env program ∼ d₁)
            × general-list-polytime (inl refl) program)
  open-d₁ = d₁∈P (succ n) (list ∷ Γ)

  open-d₂ : Sigma (Term (list ∷ (list ∷ Γ)) nat)
            (λ program →
            ((env : Env (list ∷ Γ)) →
            to-decision-solver env program ∼ d₂)
            × general-list-polytime (inl refl) program)
  open-d₂ = d₂∈P (succ n) (list ∷ Γ)

  program₁ : Term (list ∷ (list ∷ Γ)) nat
  program₁ = pr₁ open-d₁
                 
  program₂ : Term (list ∷ (list ∷ Γ)) nat
  program₂ = pr₁ open-d₂

  correctness₁ : (env : Env (list ∷ Γ))
               → to-decision-solver env (pr₁ open-d₁) ∼ d₁
  correctness₁ = pr₁ (pr₂ open-d₁)

  correctness₂ : (env : Env (list ∷ Γ))
               → to-decision-solver env (pr₁ open-d₂) ∼ d₂
  correctness₂ = pr₁ (pr₂ open-d₂)

  correctness : (env : Env Γ) →
                to-decision-solver env
                (if lam list program₁ ∙ var 𝟎 then
                lam list program₂ ∙ var 𝟎 else suc zero)
                ∼ (λ l → d₁ l && d₂ l)
  correctness env xs
   = nat-to-bool
     (if'
     (map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [ program₁ ]ₑ
     then'
     (map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [ program₂ ]ₑ
     else' 1) ＝⟨ ite-and ((map bool-to-nat xs ∷E map bool-to-nat xs ∷E env)
     [ program₁ ]ₑ)
     ((map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [ program₂ ]ₑ) ⟩
     (nat-to-bool ((map bool-to-nat xs ∷E map bool-to-nat xs ∷E env) [
     program₁ ]ₑ))
     && nat-to-bool ((map bool-to-nat xs ∷E map bool-to-nat xs ∷E env)
     [ program₂ ]ₑ)
     ＝⟨ ap₂ _&&_ (correctness₁ ((map bool-to-nat xs) ∷E env) xs)
     (correctness₂ ((map bool-to-nat xs) ∷E env) xs) ⟩
     d₁ xs && d₂ xs ∎

  timing₁ : Σ
            (λ k →
            Sigma ℕ
            (λ C →
            Sigma ℕ
            (λ N₀ →
            Pi (List ℕ)
            (λ l →
            Pi (Envᵢ (list ∷ Γ))
            (λ env →
            is-polytime k C N₀ (length l)
            (pr₁
            (pr₁ (env [ lam list (pr₁ open-d₁) ]ᵢ eager) (thunk-type l))))))))
  timing₁ = pr₂ (pr₂ open-d₁)

  timing₂ : Σ
            (λ k →
            Sigma ℕ
            (λ C →
            Sigma ℕ
            (λ N₀ →
            Pi (List ℕ)
            (λ l →
            Pi (Envᵢ (list ∷ Γ))
            (λ env →
            is-polytime k C N₀ (length l)
            (pr₁
            (pr₁ (env [ lam list (pr₁ open-d₂) ]ᵢ eager) (thunk-type l))))))))
  timing₂ = pr₂ (pr₂ open-d₂)

  timing : Σ
           (λ k →
           Sigma ℕ
           (λ C →
           Sigma ℕ
           (λ N₀ →
           Pi (List ℕ)
           (λ l →
           Pi (Envᵢ (list ∷ Γ))
           (λ env →
           is-polytime k C N₀ (length l)
           (pr₁
           (pr₁ (env [ lam list (pr₁ open-d₁) ]ᵢ eager) (thunk-type l))))))))
         → Σ
           (λ k →
           Sigma ℕ
           (λ C →
           Sigma ℕ
           (λ N₀ →
           Pi (List ℕ)
           (λ l →
           Pi (Envᵢ (list ∷ Γ))
           (λ env →
           is-polytime k C N₀ (length l)
           (pr₁
           (pr₁ (env [ lam list (pr₁ open-d₂) ]ᵢ eager) (thunk-type l))))))))
         → general-list-polytime (inl refl)
           (if lam list program₁ ∙ var 𝟎 then
           lam list program₂ ∙ var 𝟎 else suc zero)
  timing (k' , C' , N₀' , f') (k , C , N₀ , f)
   = k' + k , ((C' + C) + 4 , (succ (N₀' + N₀) , new-f))
   where
    new-f : Pi (List ℕ)
            (λ l →
            Pi (Envᵢ Γ)
            (λ env →
            is-polytime (k' + k) (C' + C + 4) (succ (N₀' + N₀)) (length l)
            (pr₁
            (pr₁
            (env [
            lam list
            (if lam list program₁ ∙ var 𝟎 then
            lam list program₂ ∙ var 𝟎 else suc zero)
            ]ᵢ eager)
            (thunk-type l)))))
    new-f xs env le
     = ≤-trans (pr₁
       (pr₁
       (env [
       lam list
       (if lam list program₁ ∙ var 𝟎 then
       lam list program₂ ∙ var 𝟎 else suc zero)
       ]ᵢ eager)
       (thunk-type xs)))
       (succ (succ
       (max
       (succ
       (pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
       eager)))
       2
       +
       pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₁ ]ᵢ eager))))
       ((C' + C + 4) * length xs ^ (k' + k))
       I (γ (≤-decidable (pr₁
       (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
       eager)) 1))
     where
      I : get-time (inl refl)
          (thunk-if {nat}
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₁ ]ᵢ eager)
          (inc-nat
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
          eager))
          (2 , (√ (√ return 1))))
          ≤
          succ
          (max
          (succ
          (pr₁
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
          eager)))
          2
          +
          pr₁
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₁ ]ᵢ
          eager))
      I = thunk-if-lemma (inl refl) (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ
          env) [
          program₁ ]ᵢ eager)
          (inc-nat (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
          program₂ ]ᵢ eager))
          (2 , (√ (√ return 1)))

      II : (pr₁
           (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
           eager)) ≤ 1 →
           max
           (succ
           (pr₁
           (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
           eager)))
           2 ＝ 2
      II le = ap succ (max-ord→ (pr₁
              (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
              eager)) 1 le)

      III : ¬ ((pr₁
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
            eager)) ≤ 1) →
            max
            (succ
            (pr₁
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
            eager)))
            2 ＝ (succ
            (pr₁
            (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
            eager)))
      III gt
       = max
         (succ
         (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
         eager)))
         2 ＝⟨ max-comm (succ
         (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
         eager))) 2 ⟩
         max
         2
         (succ
         (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
         eager)))
         ＝⟨ ap succ (max-ord→ 1 (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
         (≤-trans 1 2 (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) ⋆ (not-less-bigger-or-equal 2
         (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) gt))) ⟩
         succ
         (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
         eager)) ∎

      IV : length xs ≠ 0
      IV eq = transport (succ (N₀' + N₀) ≤_) eq le

      V : ((C' + C) + 4) * (length xs) ^ (k' + k)
        ＝ (C' + C) * (length xs) ^ (k' + k)
           + 4 * (length xs) ^ (k' + k)
      V = distributivity-mult-over-addition' (C' + C) 4 ((length xs) ^ (k' + k))

      γ : (pr₁ (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
          eager) ≤ 1) ∔ ¬ (pr₁ (((0 , return xs) ∷Eᵢ
          (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
          eager) ≤ 1) → (succ
          (succ
          (max
          (succ
          (pr₁
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₂ ]ᵢ
          eager)))
          2
          +
          pr₁
          (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₁ ]ᵢ
          eager)))) ≤
          ((C' + C + 4) * length xs ^ (k' + k))
      γ (inl le')
       = transport (_≤ ((C' + C + 4) * length xs ^ (k' + k)))
         (ap (λ z → succ (succ (z + pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [ program₁ ]ᵢ
         eager)))) (II le' ⁻¹))
         (transport (λ z → succ (succ z) ≤ (C' + C + 4) * length xs ^ (k' + k))
         (+-comm (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) 2)
         (≤-trans (
         (pr₁
         (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
         pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) + 4)
         (C' * (length xs) ^ k' + 4)
         ((C' + C + 4) * (length xs) ^ (k' + k))
         (f' xs ((0 , return xs) ∷Eᵢ env)
         (≤-trans N₀' (succ (N₀' + N₀)) (length xs)
         (≤-trans N₀' (N₀' + N₀) (succ (N₀' + N₀))
         (≤-+ N₀' N₀) (≤-succ (N₀' + N₀))) le))
         (≤-trans ((C' * (length xs) ^ k') + 4)
         (((C' + C) * (length xs) ^ k') + 4)
         ((C' + C + 4) * (length xs) ^ (k' + k))
         (multiplication-preserves-order C' (C' + C)
         ((length xs) ^ k') (≤-+ C' C))
         (≤-trans ((C' + C) * (length xs) ^ k' + 4)
         ((C' + C) * (length xs) ^ (k' + k) + 4)
         ((C' + C + 4) * (length xs) ^ (k' + k))
         (multiplication-preserves-order-left (C' + C)
         ((length xs) ^ k') ((length xs) ^ (k' + k))
         (exponentiation-preserves-order-left (length xs)
         k' (k' + k) (inl IV) (≤-+ k' k)))
         ( transport ((((C' + C) * (length xs) ^ (k' + k)) + 4) ≤_)
         (V ⁻¹) (≤-n-monotone-left 4 (4 * (length xs) ^ (k' + k))
         ((C' + C) * (length xs) ^ (k' + k))
         (multiplication-preserves-order-left 4 1 (length xs ^ (k' + k))
         (transport (_≤ (length xs ^ (k' + k)))
         (exponentiation-of-one (k' + k))
         (exponentiation-preserves-order-right 1 (length xs) (k' + k)
         (≤-trans 1 (succ (N₀' + N₀)) (length xs)
         ⋆ le))))))))))
      γ (inr nle) = ≤-trans (succ
                    (succ
                    (succ
                    (max
                    (pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
                    1)
                    +
                    pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
                    ((C' + C + 3) *
                    (length xs) ^ (k' + k))
                    ((C' + C + 4) *
                    (length xs) ^ (k' + k))
                    (transport (λ z → succ (succ (z + pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))) ≤
                    (C' + C + 3) * (length xs) ^ (k' + k))
                    (III nle ⁻¹)
                    (≤-trans (succ
                    (succ
                    (succ
                    (pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
                    +
                    pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))))
                    (succ (succ (succ (C' * (length xs) ^ k')
                    + C * (length xs) ^ k)))
                    (((C' + C) + 3) * (length xs) ^ (k' + k))
                    (transport (_≤ (succ (C' * (length xs) ^ k')
                    + (C * (length xs) ^ k)))
                    (I' ⁻¹)
                    (≤-adding (succ (pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
                    (succ (C' * (length xs) ^ k'))
                    (pr₁
                    (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
                    pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
                    (C * (length xs) ^ k)
                    (f' xs ((0 , return xs) ∷Eᵢ env)
                    ((≤-trans N₀' (succ (N₀' + N₀)) (length xs)
                    (≤-trans N₀' (N₀' + N₀) (succ (N₀' + N₀))
                    (≤-+ N₀' N₀) (≤-succ (N₀' + N₀))) le)))
                    (f xs ((0 , return xs) ∷Eᵢ env)
                    (((≤-trans N₀ (succ (N₀' + N₀)) (length xs)
                    (≤-trans N₀ (N₀' + N₀) (succ (N₀' + N₀))
                    (≤-+' N₀' N₀) (≤-succ (N₀' + N₀))) le))))))
                    ((transport (_≤ (succ (succ (succ (C' + C)))
                    * length xs ^ (k' + k)))
                    (ap (succ ∘ succ) (succ-left (C' * length xs ^ k')
                    (C * length xs ^ k))⁻¹)
                    (≤-trans (succ (succ (succ (C' * length xs ^ k'
                    + C * length xs ^ k))))
                    (succ (succ (succ ((C' + C)
                    * length xs ^ (k' + k)))))
                    (succ (succ (succ (C' + C)))
                    * length xs ^ (k' + k))
                    V'
                    (transport (succ (succ (succ ((C' + C) * rec 1
                    (_*_ (length xs)) (k' + k)))) ≤_)
                    (VI' ⁻¹) (≤-n-monotone-left 3 (3 * (length xs)
                    ^ (k' + k))
                    ((C' + C) * (length xs) ^ (k' + k))
                    (multiplication-preserves-order-left 3 1
                    (length xs ^ (k' + k))
                    (transport (_≤ (length xs ^ (k' + k)))
                    (exponentiation-of-one (k' + k))
                    (exponentiation-preserves-order-right 1
                    (length xs) (k' + k)
                    (≤-trans 1 (succ (N₀' + N₀)) (length xs)
                    ⋆ le)))))))))))
                    (multiplication-preserves-order (succ (succ
                    (succ (C' + C))))
                    (succ (succ (succ (succ (C' + C)))))
                    (length xs ^ (k' + k))
                    (≤-succ (C' + C)))

       where
        I' : (succ
             (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             +
             pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
           ＝ (succ
             (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             +
             pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
        I' = (succ
             (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             +
             pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             ＝⟨ succ-left (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) ⟩
             (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             +
             (succ (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
             ＝⟨ +-comm (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager))
             (succ (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager))) ⟩
             (succ (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₁∈P (succ n) (list ∷ Γ)) ]ᵢ eager)))
             +
             (pr₁
             (((0 , return xs) ∷Eᵢ (0 , return xs) ∷Eᵢ env) [
             pr₁ (d₂∈P (succ n) (list ∷ Γ)) ]ᵢ eager)) ∎

        II' : length xs ≠ 0
        II' eq = transport (succ (N₀' + N₀) ≤_) eq le

        III' : (length xs ^ k') ≤
               (length xs ^ (k' + k))
        III' = exponentiation-preserves-order-left (length xs) k' (k' + k)
               (inl II')
               (≤-+ k' k)

        IV' : (length xs ^ k) ≤
              (length xs ^ (k' + k))
        IV' = exponentiation-preserves-order-left (length xs) k (k' + k)
              (inl II')
              (≤-+' k' k)

        V' : (C' * length xs ^ k' + C * length xs ^ k) ≤ (C' + C)
             * (length xs ^ (k' + k))
        V' = transport ((C' * length xs ^ k' + C * length xs ^ k) ≤_)
             (distributivity-mult-over-addition' C' C (length xs ^ (k' + k)) ⁻¹)
             (≤-adding (C' * (length xs) ^ k') (C' * (length xs) ^ (k' + k))
             (C * (length xs) ^ k) (C * (length xs) ^ (k' + k))
             (multiplication-preserves-order-left C' ((length xs) ^ k')
             ((length xs) ^ (k' + k)) III')
             ((multiplication-preserves-order-left C ((length xs) ^ k)
             ((length xs) ^ (k' + k)) IV')))
                                      
        VI' : ((C' + C) + 3) * (length xs) ^ (k' + k)
            ＝ (C' + C) * (length xs) ^ (k' + k)
              + 3 * (length xs) ^ (k' + k)
        VI' = distributivity-mult-over-addition' (C' + C) 3 ((length xs)
              ^ (k' + k))

\end{code}
