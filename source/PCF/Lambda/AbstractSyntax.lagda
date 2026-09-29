Brendan Hart 2019-2020

We define PCF types and terms, substitution as in PLFA, and the big step semantics.

https://plfa.github.io/

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module PCF.Lambda.AbstractSyntax (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan

data Vec (X : 𝓤₀ ̇ ) : ℕ → 𝓤₀ ̇ where
 ⟨⟩  : Vec X zero
 _’_ : {n : ℕ} → Vec X n → X → Vec X (succ n)

data Fin : (n : ℕ) → 𝓤₀ ̇ where
 zero : ∀ {n} → Fin (succ n)
 succ : ∀ {n} → Fin n → Fin (succ n)

data type : 𝓤₀ ̇ where
 ι : type
 _⇒_ : type → type → type

infixr 1 _⇒_

Context : ℕ → 𝓤₀ ̇
Context = Vec type

data _∋_ : {n : ℕ} → Context n → type → 𝓤₀ ̇ where
 Z : ∀ {n : ℕ} {Γ : Context n} {σ : type} → (Γ ’ σ) ∋ σ
 S : ∀ {n : ℕ} {Γ : Context n} {σ τ : type}
   → Γ ∋ σ
   → (Γ ’ τ) ∋ σ


data PCF : {n : ℕ} (Γ : Context n) (σ : type) → 𝓤₀ ̇ where

 Zero   : {n : ℕ} {Γ : Context n}
        → PCF Γ ι

 Succ   : {n : ℕ} {Γ : Context n}
        → PCF Γ ι
        → PCF Γ ι

 Pred   : {n : ℕ} {Γ : Context n}
        → PCF Γ ι
        → PCF Γ ι

 IfZero : {n : ℕ} {Γ : Context n}
        → PCF Γ ι
        → PCF Γ ι
        → PCF Γ ι
        → PCF Γ ι

 ƛ      : {n : ℕ} {Γ : Context n} {σ τ : type}
        → PCF (Γ ’ σ) τ
        → PCF Γ (σ ⇒ τ)

 _·_    : {n : ℕ} {Γ : Context n} {σ τ : type}
        → PCF Γ (σ ⇒ τ)
        → PCF Γ σ
        → PCF Γ τ

 v      : {n : ℕ} {Γ : Context n} {σ : type}
        → Γ ∋ σ
        → PCF Γ σ

 Fix    : {n : ℕ} {Γ : Context n} {σ : type}
        → PCF Γ (σ ⇒ σ)
        → PCF Γ σ

infixl 1 _·_

Fin-0-is-empty : ¬ Fin 0
Fin-0-is-empty i = f i
 where
  P : ℕ → 𝓤₀ ̇
  P 0        = 𝟘
  P (succ n) = 𝟙

  f : {n : ℕ} → Fin n → P n
  f zero     = ⋆
  f (succ i) = ⋆

lookup : {n : ℕ} → Context n → Fin n → type
lookup ⟨⟩      i        = 𝟘-elim (Fin-0-is-empty i)
lookup (Γ ’ x) zero     = x
lookup (Γ ’ x) (succ n) = lookup Γ n

count : {n : ℕ} {Γ : Context n} → (f : Fin n) → Γ ∋ lookup Γ f
count {0}      {⟨⟩}    i        = 𝟘-elim (Fin-0-is-empty i)
count {succ n} {Γ ’ x} zero     = Z
count {succ n} {Γ ’ x} (succ f) = S (count f)

ext : ∀ {m n} {Γ : Context m} {Δ : Context n}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
    → (∀ {σ A} → (Γ ’ σ) ∋ A → (Δ ’ σ) ∋ A)
ext f Z     = Z
ext f (S t) = S (f t)

rename : ∀ {m n} {Γ : Context m} {Δ : Context n}
       → (∀ {A} → Γ ∋ A → Δ ∋ A)
       → (∀ {A} → PCF Γ A → PCF Δ A)
rename f Zero = Zero
rename f (Succ t)         = Succ (rename f t)
rename f (Pred t)         = Pred (rename f t)
rename f (IfZero t t₁ t₂) = IfZero (rename f t) (rename f t₁) (rename f t₂)
rename f (ƛ t)            = ƛ (rename (ext f) t)
rename f (t · t₁)         = rename f t · rename f t₁
rename f (v x)            = v (f x)
rename f (Fix t)          = Fix (rename f t)

exts : ∀ {m n} {Γ : Context m} {Δ : Context n}
       → (∀ {A} → Γ ∋ A → PCF Δ A)
       → (∀ {σ A} → (Γ ’ σ) ∋ A → PCF (Δ ’ σ) A)
exts f Z     = v Z
exts f (S t) = rename (_∋_.S) (f t)

subst : ∀ {m n} {Γ : Context m} {Δ : Context n}
      → (∀ {A} → Γ ∋ A → PCF Δ A)
      → (∀ {A} → PCF Γ A → PCF Δ A)
subst f Zero = Zero
subst f (Succ t)         = Succ (subst f t)
subst f (Pred t)         = Pred (subst f t)
subst f (IfZero t t₁ t₂) = IfZero (subst f t) (subst f t₁) (subst f t₂)
subst f (ƛ t)            = ƛ (subst (exts f) t)
subst f (t · t₁)         = subst f t · subst f t₁
subst f (v x)            = f x
subst f (Fix t)          = Fix (subst f t)

extend-with : {n : ℕ} {m : ℕ} {Γ : Context n} {Δ : Context m}
              {A : type} (N : PCF Δ A)
            → (∀ {A} → Γ ∋ A → PCF Δ A)
            → (∀ {B} → (Γ ’ A) ∋ B → PCF Δ B)
extend-with N f Z = N
extend-with N f (S x) = f x

replace-first : {n : ℕ} (A : type) (Γ : Context n) (N : PCF Γ A)
              → (∀ {B} → (Γ ’ A) ∋ B → PCF Γ B)
replace-first A Γ N Z     = N
replace-first A Γ N (S t) = v t

_[_] : {n : ℕ} {Γ : Context n} {σ A : type}
         → PCF (Γ ’ A) σ → PCF Γ A → PCF Γ σ
_[_] {n} {Γ} {σ} {A} M N = subst (replace-first A Γ N) M

numeral : ∀ {n} {Γ : Context n} → ℕ → PCF Γ ι
numeral zero     = Zero
numeral (succ n) = Succ (numeral n)

peano-axiom-for-PCF : ∀ {n Γ k} → numeral {n} {Γ} zero ≠ numeral (succ k)
peano-axiom-for-PCF ()

\end{code}
