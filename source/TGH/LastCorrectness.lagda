Theo Hepburn, started February 2025

A program that gets the last element of a list,
together with proof of correctness.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_ ; _∙_)
open import UF.FunExt

module TGH.LastCorrectness (fe : naive-funext 𝓤₀ 𝓤₀) where

open import Naturals.Addition
 renaming (addition-commutativity to +-comm ; addition-associativity to +-assoc)
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
open import TGH.BigO
open import TGH.Language fe
open import TGH.HeadExample fe

length' : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ nat)
length' = lam list (lrec (var 𝟎) zero (lam nat (lam nat (suc (var 𝟏)))))

last : {n : ℕ} {Γ : Ctx n} → Term Γ (list ⇒ nat)
last = lam list (head ∙ (lrec (var 𝟎) nil (lam list (lam nat (if length'
       ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))))

last' : List ℕ → ℕ
last' [] = zero
last' (x ∷ []) = x
last' (_ ∷ xs@(_ ∷ _)) = last' xs

last-list' : List ℕ → List ℕ
last-list' [] = []
last-list' (x ∷ []) = [ x ]
last-list' (_ ∷ xs@(_ ∷ _)) = last-list' xs

last-list'-not-empty : (x : ℕ) (xs : List ℕ)
                     → ¬ (length (last-list' (x ∷ xs)) ＝ 0)
last-list'-not-empty x [] ()
last-list'-not-empty x (x₁ ∷ xs) = last-list'-not-empty x₁ xs

length'-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  → {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                  → (l : List ℕ)
                  →
                     list-rec env₁ l zero (lam nat (lam nat (suc (var 𝟏))))
                  ＝ list-rec env₂ l zero (lam nat (lam nat (suc (var 𝟏))))
length'-env-lemma [] = refl
length'-env-lemma (x ∷ l) = ap succ (length'-env-lemma l)

length'-correctness : {n : ℕ} {Γ : Ctx n}
                    → {env : Env Γ}
                    → (l : List ℕ)
                    → (env [ length' ]ₑ) l ＝ length l
length'-correctness [] = refl
length'-correctness {_} {_} {env} (x ∷ l)
 = succ (list-rec ((x ∷ l) ∷E env) l zero (lam nat (lam nat (suc (var 𝟏)))))
   ＝⟨ ap succ (length'-env-lemma l) ⟩
   succ (list-rec (l ∷E env) l zero (lam nat (lam nat (suc (var 𝟏)))))
   ＝⟨ ap succ (length'-correctness l) ⟩
   succ (length l) ∎

last-list : {n : ℕ} {Γ : Ctx n} → Term ((list ∷ Γ)) list
last-list = lrec (var 𝟎) nil (lam list (lam nat (if length' ∙ (var 𝟏)
            then cons (var 𝟎) nil else (var 𝟏))))

last-list-env-lemma : {n₁ n₂ : ℕ} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  → {env₁ : Env Γ₁} {env₂ : Env Γ₂}
                  → (l : List ℕ)
                  → list-rec env₁ l nil (lam list (lam nat
                    (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))
                  ＝ list-rec env₂ l nil (lam list (lam nat (if length'
                    ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))
last-list-env-lemma [] = refl
last-list-env-lemma {_} {_} {_} {_} {env₁} {env₂} (x ∷ l)
 = if' ((x ∷E (list-rec env₁ l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏))))) ∷E env₁) [ length' ]ₑ) (list-rec
   env₁ l nil (lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil
   else (var 𝟏)))))
   then' x ∷ [] else'
   (list-rec env₁ l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏))))) ＝⟨ ap (λ z → if' ((x ∷E (list-rec
   env₁ l nil (lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil
   else (var 𝟏))))) ∷E env₁) [ length' ]ₑ) z then' [ x ] else' z)
   (last-list-env-lemma l) ⟩
   (if' ((x ∷E (list-rec env₁ l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏))))) ∷E env₁) [ length' ]ₑ) (list-rec env₂
   l nil (lam list (lam nat (if length' ∙ (var 𝟏) then
   cons (var 𝟎) nil else (var 𝟏)))))
   then' x ∷ [] else'
   (list-rec env₂ l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏)))))) ＝⟨ ap (λ z
   → if' z (list-rec env₂ l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏))))) then' [ x ] else' list-rec env₂
   l nil (lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil
   else (var 𝟏))))) (fe length'-env-lemma) ⟩
   ((if' ((x ∷E (list-rec env₂ l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏))))) ∷E env₂) [ length' ]ₑ) (list-rec env₂
   l nil (lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil
   else (var 𝟏)))))
   then' x ∷ [] else'
   (list-rec env₂ l nil (lam list (lam nat (if length' ∙ (var 𝟏) then
   cons (var 𝟎) nil else (var 𝟏))))))) ∎

last-list-correctness : {n : ℕ} {Γ : Ctx n}
                            → {env : Env Γ}
                            → (l : List ℕ)
                            → ((l ∷E env) [ last-list ]ₑ) ＝ last-list' l

last-list-correctness-any-env : {n : ℕ} {Γ : Ctx n}
                            → {env : Env Γ}
                            (l : List ℕ)
                            → list-rec env l nil (lam list (lam nat
                              (if length' ∙ (var 𝟏) then cons (var 𝟎)
                              nil else (var 𝟏))))
                              ＝ last-list' l
last-list-correctness-any-env {_} {_} {env} l
 = list-rec env l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏)))) ＝⟨ last-list-env-lemma l ⟩
   list-rec (l ∷E []) l nil (lam list (lam nat (if length' ∙ (var 𝟏)
   then cons (var 𝟎) nil else (var 𝟏)))) ＝⟨ last-list-correctness l ⟩
   last-list' l ∎

last-list-correctness [] = refl
last-list-correctness (x ∷ []) = refl
last-list-correctness {_} {_} {env} (x ∷ l@(x₁ ∷ x₂))
 = ((x ∷ l) ∷E env) [ lrec (var 𝟎) nil (lam list
   (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))  ]ₑ
   ＝⟨ refl ⟩
   list-rec ((x ∷ l) ∷E env) (x ∷ l) nil (lam list (lam nat
   (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)))) ＝⟨ refl ⟩
     (((x ∷ l) ∷E env) [ lam list (lam nat (if length' ∙ (var 𝟏)
     then cons (var 𝟎) nil else (var 𝟏))) ]ₑ) (list-rec ((x ∷ l) ∷E env) l nil
     (lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else
     (var 𝟏))))) x ＝⟨ refl ⟩    
     (λ n → (λ lis → (n ∷E lis ∷E (x ∷ l) ∷E env) [ if length' ∙ (var 𝟏)
     then cons (var 𝟎) nil else (var 𝟏) ]ₑ) (list-rec ((x ∷ l) ∷E env) l nil
     (lam list (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else
     (var 𝟏)))))) x ＝⟨ refl ⟩
     ((x ∷E (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat
     (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)))))
     ∷E (x ∷ l) ∷E env) [ if length' ∙ (var 𝟏) then cons (var 𝟎) nil
     else (var 𝟏) ]ₑ) ＝⟨ refl ⟩
     if' (x ∷E (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat
     (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))) ∷E
     (x ∷ l) ∷E env) [ length' ∙ (var 𝟏) ]ₑ
     then' x ∷ [] else'
     ((x ∷E (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat
     (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))) ∷E
     (x ∷ l) ∷E env) [ var 𝟏 ]ₑ) ＝⟨ refl ⟩
     if' ((x ∷E (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat
     (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))) ∷E (x ∷ l)
     ∷E env) [ length' ]ₑ) (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat
     (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)))))
       then' x ∷ [] else'
        (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat (if length' ∙ (var 𝟏)
        then cons (var 𝟎) nil else (var 𝟏))))) ＝⟨ ap (λ z → if' z (list-rec
        ((x ∷ l) ∷E env) l nil (lam list (lam nat (if length' ∙ (var 𝟏)
        then cons (var 𝟎) nil else (var 𝟏))))) then' x ∷ [] else' (list-rec
        ((x ∷ l) ∷E env) l nil (lam list (lam nat (if length' ∙ (var 𝟏) then
        cons (var 𝟎) nil else (var 𝟏))))) ) (fe length'-correctness) ⟩
        (if' length (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat
        (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)))))
       then' x ∷ [] else'
        (list-rec ((x ∷ l) ∷E env) l nil (lam list (lam nat (if length'
        ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏))))))
        ＝⟨ ap (λ z → if' length z then' [ x ] else' z)
        (last-list-correctness-any-env l) ⟩
        (if' length (last-list' l) then' [ x ] else' last-list' l)
        ＝⟨ γ₁ (length (last-list' l)) γ₀ ⟩
        last-list' l ＝⟨ refl ⟩
        last-list' (x ∷ l) ∎
 where
  γ₀ : ¬ (length (last-list' l) ＝ 0)
  γ₀ = last-list'-not-empty x₁ x₂

  γ₁ : {x y : List ℕ} → (n : ℕ) → n ≠ 0 → if' n then' x else' y ＝ y
  γ₁ zero neq = 𝟘-elim (neq refl)
  γ₁ (succ n) _ = refl


last-correctness : {n : ℕ} {Γ : Ctx n} → {env : Env Γ} → (l : List ℕ)
                 → (env [ last ]ₑ) l ＝ last' l
last-correctness {_} {_} {env} l
 = ((l ∷E env) [ head ]ₑ) (list-rec (l ∷E env) l nil (lam list
   (lam nat (if length' ∙ (var 𝟏) then cons (var 𝟎) nil else (var 𝟏)))))
   ＝⟨ ap (λ z → ((l ∷E env) [ head ]ₑ) z) (last-list-correctness l) ⟩
   ((l ∷E env) [ head ]ₑ) (last-list' l) ＝⟨ head-correctness (last-list' l) ⟩
   list-head (last-list' l) ＝⟨ γ l ⟩
   last' l ∎
 where
  γ : (l : List ℕ) → list-head (last-list' l) ＝ last' l
  γ [] = refl
  γ (x ∷ []) = refl
  γ (x ∷ x₁ ∷ l) = γ (x₁ ∷ l)

\end{code}
