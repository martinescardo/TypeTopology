\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt
open import TGH.Strategy


module TGH.NP (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition
 renaming (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_ ; _<ℕ_ to _<_)
open import Naturals.Properties renaming (pred to pred')
open import MLTT.Vector renaming (Vector to Vec)
open import MLTT.Fin
open import MLTT.List
open import MLTT.Bool hiding (if_then_else_)
open import UF.Base
open import TGH.Thunk
open import TGH.NatOrder
open import TGH.MyExponentiation
open import TGH.Language fe
open import TGH.P fe

is-polytime' : (k C A₀ x y : ℕ) → 𝓤₀ ̇
is-polytime' k C M x y = y ≤ C * (x ^ k) + M

to-decision-verifier : {n : ℕ} {Γ : Ctx n} → (env : Env Γ)
                     → Term (list ∷ list ∷ Γ) nat → List Bool
                     → List Bool → Bool
to-decision-verifier env program c l
 = nat-to-bool ((env [ lam list (lam list program) ]ₑ)
   (map bool-to-nat c) (map bool-to-nat l))

reduce : {n : ℕ} {Γ : Ctx n} → (env : Env Γ)
       → Term (list ∷ Γ) list → List Bool → List Bool
reduce env r l
 = map nat-to-bool ((env [ lam list r ]ₑ) (map bool-to-nat l))

is-polytime₂ : (k C N₀ N₁ x₁ x₂ y : ℕ) → 𝓤₀ ̇
is-polytime₂ k C N₀ N₁ x₀ x₁ y
  = N₀ ≤ x₀ → N₁ ≤ x₁ → y ≤ C * (x₀ + x₁) ^ k 

polynomial-length : (l₁ l₂ : List Bool) → (k C : ℕ) → 𝓤₀ ̇
polynomial-length l₁ l₂ k C
 = (length l₂) ≤ C * (length l₁) ^ k

general-list-polytime' : {τ : LType} {n : ℕ} {Γ : Ctx n}
                       → ((τ ＝ nat) ∔ (τ ＝ list)) → Term (list ∷ Γ) τ → 𝓤₀ ̇
general-list-polytime' {_} {n} {Γ} (inl refl) program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ M ꞉ ℕ , Π l ꞉ List Bool , Π env ꞉ Envᵢ Γ ,
   is-polytime' k C M (length l) (pr₁ (pr₁ (env [ lam list program ]ᵢ eager)
   (thunk-type (map bool-to-nat l))))
general-list-polytime' {_} {n} {Γ} (inr refl) program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ M ꞉ ℕ , Π l ꞉ List Bool , Π env ꞉ Envᵢ Γ ,
   is-polytime' k C M (length l) (pr₁ (pr₁ (env [ lam list program ]ᵢ eager)
   (thunk-type (map bool-to-nat l))))

verifier-polytime : {n : ℕ} {Γ : Ctx n} → Term (list ∷ list ∷ Γ) nat → 𝓤₀ ̇
verifier-polytime {n} {Γ} program
 = Σ k ꞉ ℕ , Σ C ꞉ ℕ , Σ N₀ ꞉ ℕ , Σ N₁ ꞉ ℕ , Π l ꞉ List ℕ , Π c ꞉ List ℕ ,
   Π env ꞉ Envᵢ Γ ,
    is-polytime₂ k C N₀ N₁ (length c) (length l)
    (pr₁ (pr₁ (pr₁ (env [ lam list (lam list program) ]ᵢ eager) (thunk-type c))
    (thunk-type l)))

_∈NP : (decision : List Bool → Bool) → 𝓤₀ ̇
_∈NP decision = Π n ꞉ ℕ , Π Γ ꞉ Ctx n ,
                Σ program ꞉ Term (list ∷ list ∷ Γ) nat , (Σ k ꞉ ℕ , Σ C ꞉ ℕ ,
                Π l ꞉ List Bool , Σ c ꞉ List Bool , polynomial-length l c k C
                × ((env : Env Γ) →
                (to-decision-verifier env program c l ＝ decision l))
                × (verifier-polytime program))

applying-function : {σ τ : LType} {n : ℕ} {Γ : Ctx n} → (env : Envᵢ Γ)
                  → (term : Term (σ ∷ Γ) τ) → (x : ⟦ σ ⟧)
                  → pr₁ (env [ lam σ term ]ᵢ eager) (thunk-type x)
                  ＝ ((thunk-type x) ∷Eᵢ env) [ term ]ᵢ eager
applying-function {nat} env term x = refl
applying-function {list} env term x = refl
applying-function {σ ⇒ σ₁} env term x = refl

P⊆NP : (decision : List Bool → Bool) → decision ∈P → decision ∈NP
P⊆NP decision p n Γ
 = program , 0 , 1 , γ
 where
  P-instance : Sigma (Term (list ∷ (list ∷ Γ)) nat)
               (λ program →
               ((env : Env (list ∷ Γ)) →
               to-decision-solver env program ∼ decision)
               × general-list-polytime (inl refl) program)
  P-instance = p (succ n) (list ∷ Γ)

  program : Term (list ∷ (list ∷ Γ)) nat
  program = pr₁ P-instance

  γ₂ : (xs : List Bool)
     → ((env : Env (list ∷ Γ)) → to-decision-solver env program ∼ decision) ×
       (general-list-polytime (inl refl) program)
     → ((env : Env Γ) → (to-decision-verifier env program [])
       xs ＝ decision xs)
       × (verifier-polytime program)
  γ₂ xs (correctness , k , C , N₀ , f')
   = (λ env → correctness ([] ∷E env) xs) , timing
   where
    timing : verifier-polytime program
    timing = k , (C , 0 , (N₀ , f))
     where        
      I : (l : List ℕ) → (c : List ℕ) → (env : Envᵢ Γ)
        → pr₁ (pr₁ (pr₁ (env [ lam list (lam list program) ]ᵢ eager)
          (0 , return c)) (0 , return l))
        ＝ pr₁ (pr₁ (((0 , return c) ∷Eᵢ env) [ lam list program ]ᵢ eager)
          (0 , return l))
      I l c env
       = ap (λ z → (pr₁ ((pr₁ z) (0 , return l)))) (applying-function env
         (lam list program) c)

      II : (l : List ℕ) → (c : List ℕ) → (env : Envᵢ Γ)
         → N₀ ≤ length l
         → pr₁ (pr₁ (((0 , return c) ∷Eᵢ env) [ lam list program ]ᵢ eager)
           (0 , return l))
           ≤ (C * (length c + length l) ^ k)
      II l c env le
       = ≤-trans (pr₁ (pr₁ (((0 , return c) ∷Eᵢ env) [ lam list program ]ᵢ eager)
         (0 , return l)))
         (C * (length l) ^ k) (C * (length c + length l) ^ k) (f' l
         ((0 , return c)
         ∷Eᵢ env) le)
         (multiplication-preserves-order-left C ((length l) ^ k)
         ((length c + length l) ^ k)
         (exponentiation-preserves-order-right (length l) (length c + length l) k
         (transport (_≤ length c + length l) (zero-left-neutral (length l))
         (≤-n-monotone-right 0 (length c) (length l) ⋆))))

      f : Pi (List ℕ)
          (λ l →
          Pi (List ℕ)
          (λ c →
          Pi (Envᵢ Γ)
          (λ env →
          is-polytime₂ k C 0 N₀ (length c) (length l)
          (pr₁
          (pr₁ (pr₁ (env [ lam list (lam list program) ]ᵢ eager) (0 , return c))
          (0 , return l))))))
      f l c env ⋆ le
       = transport (λ z → z ≤ (C * (length c + length l) ^ k)) (I l c env ⁻¹)
         (II l c env le)
     

  γ : Pi (List Bool)
          (λ l →
          Sigma (List Bool)
          (λ c →
          is-polytime' 0 1 0 (length l) (length c)
          × ((env : Env Γ)
          → to-decision-verifier env program c l ＝ decision l)
          × verifier-polytime program))
  γ xs = [] , ⋆ , γ₂ xs (pr₂ P-instance)
     
\end{code}
