Brendan Hart 2019-2020

We define big step semantics of PCF.Lambda.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module PCF.Lambda.BigStep (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import Naturals.Properties hiding (pred-succ)
open import PCF.Lambda.AbstractSyntax pt

data _⇓'_ : ∀ {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → PCF Γ σ → 𝓤₀ ̇ where

  var-id    : {n : ℕ} {Γ : Context n} {A : type}
              {i : Γ ∋ A}
            → (v i) ⇓' (v i)

  ƛ-id      : {n : ℕ} {Γ : Context n} {σ τ : type}
              {t : PCF (Γ ’ σ) τ}
            → ƛ t ⇓' ƛ t

  zero-id   : {n : ℕ} {Γ : Context n}
            → numeral {n} {Γ} zero ⇓' numeral {n} {Γ} zero

  pred-zero : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι}
            → M ⇓' numeral {n} {Γ} zero
            → Pred M ⇓' numeral {n} {Γ} zero

  pred-succ : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι}
              {k : ℕ}
            → M ⇓' numeral {n} {Γ} (succ k)
            → Pred M ⇓' numeral {n} {Γ} k

  succ-arg  : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι}
              {k : ℕ}
            → M ⇓' numeral {n} {Γ} k
            → Succ M ⇓' numeral {n} {Γ} (succ k)

  IfZero-zero : {n : ℕ} {Γ : Context n}
                {M : PCF Γ ι} {M₁ : PCF Γ ι} {M₂ : PCF Γ ι}
                {V : PCF Γ ι}
              → M ⇓' numeral {n} {Γ} zero
              → M₁ ⇓' V
              → IfZero M M₁ M₂ ⇓' V

  IfZero-succ : {n : ℕ} {Γ : Context n}
                {M : PCF Γ ι} {M₁ : PCF Γ ι} {M₂ : PCF Γ ι}
                {V : PCF Γ ι}
                {k : ℕ}
              → M ⇓' numeral {n} {Γ} (succ k)
              → M₂ ⇓' V
              → IfZero M M₁ M₂ ⇓' V

  Fix-step  : {n : ℕ} {Γ : Context n} {σ : type} {M : PCF Γ (σ ⇒ σ)} {V : PCF Γ σ}
            → (M · (Fix M)) ⇓' V
            → Fix M ⇓' V

  ·-step    : {n : ℕ} {Γ : Context n} {σ τ : type}
              {M : PCF Γ (σ ⇒ τ)} {E : PCF (Γ ’ σ) τ} {N : PCF Γ σ}
              {V : PCF Γ τ}
            → M ⇓' ƛ E
            → (E [ N ]) ⇓' V
            → (M · N) ⇓' V

_⇓_ : {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → PCF Γ σ → 𝓤₀ ̇
M ⇓ N = ∥ M ⇓' N ∥

data Value : {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → 𝓤₀ ̇ where

  zero-val : {n : ℕ} {Γ : Context n}
           → Value {n} {Γ} Zero

  succ-val : {n : ℕ} {Γ : Context n} {V : PCF Γ ι}
           → Value V
           → Value (Succ V)

  ƛ-val    : {n : ℕ} {Γ : Context n} {σ τ : type} {N : PCF (Γ ’ σ) τ}
           → Value (ƛ N)

  var-val  : {n : ℕ} {Γ : Context n} {σ : type}
           → (i : Γ ∋ σ)
           → Value (v i)

values-dont-reduce-further : {n : ℕ} {Γ : Context n} {σ : type}
                           → (M : PCF Γ σ)
                           → Value M
                           → (N : PCF Γ σ)
                           → M ⇓' N
                           → M ＝ N
values-dont-reduce-further .(v _) x .(v _) var-id = refl
values-dont-reduce-further .(ƛ _) x .(ƛ _) ƛ-id   = refl
values-dont-reduce-further .Zero x .Zero zero-id  = refl
values-dont-reduce-further .(Succ M) (succ-val x)
                           .(Succ (numeral k))
                            (succ-arg {n} {Γ} {M} {k} r) = ap Succ IH
  where
    IH : M ＝ numeral k
    IH = values-dont-reduce-further M x (numeral k) r

⇓-reduces-to-val : {n : ℕ} {Γ : Context n} {σ : type}
                   (M N : PCF Γ σ)
                 → M ⇓' N
                 → Value N
⇓-reduces-to-val (v i)    (v i)  var-id        = var-val i
⇓-reduces-to-val .(ƛ _)   .(ƛ _) ƛ-id          = ƛ-val
⇓-reduces-to-val .Zero    .Zero  zero-id       = zero-val
⇓-reduces-to-val (Pred M) .Zero (pred-zero p)  = ⇓-reduces-to-val M Zero p
⇓-reduces-to-val (Pred M) (N)
                 (pred-succ {_} {_} {_} {k} p) = lemma IH
  where
    IH : Value (Succ (numeral k))
    IH = ⇓-reduces-to-val M (Succ (numeral k)) p

    lemma : ∀ {n} {Γ} {N} → Value {n} {Γ} (Succ N) → Value N
    lemma (succ-val t) = t

⇓-reduces-to-val (Succ M) (Succ N) (succ-arg p)        = succ-val (⇓-reduces-to-val M N p)
⇓-reduces-to-val (IfZero M M₁ M₂) N (IfZero-zero p p₁) = ⇓-reduces-to-val M₁ N p₁
⇓-reduces-to-val (IfZero M M₁ M₂) N (IfZero-succ p p₁) = ⇓-reduces-to-val M₂ N p₁
⇓-reduces-to-val (Fix M) N (Fix-step p) =
 ⇓-reduces-to-val (M · Fix M) N p
⇓-reduces-to-val (L · R) N (·-step {_} {_} {_} {_} {_} {E} p p₁) =
 ⇓-reduces-to-val (E [ R ]) N p₁

⇓-cant-reduce-further : {n : ℕ} {Γ : Context n} {σ : type}
                        (M N L : PCF Γ σ)
                      → M ⇓' N
                      → N ⇓' L
                      → N ＝ L
⇓-cant-reduce-further M N L step₁ step₂ =
 values-dont-reduce-further N (⇓-reduces-to-val M N step₁) L step₂

⇓-deterministic : {n : ℕ} {Γ : Context n} {σ : type}
                  {M N L : PCF Γ σ}
                → M ⇓' N
                → M ⇓' L
                → N ＝ L
⇓-deterministic var-id var-id = refl
⇓-deterministic ƛ-id              ƛ-id              = refl
⇓-deterministic zero-id           zero-id           = refl
⇓-deterministic (pred-zero step₁) (pred-zero step₂) = refl
⇓-deterministic (pred-zero step₁) (pred-succ {_} {_} {_} {k} step₂) =
 𝟘-elim (peano-axiom-for-PCF IH)
 where
   IH : numeral zero ＝ numeral (succ k)
   IH = ⇓-deterministic step₁ step₂

⇓-deterministic (pred-succ {_} {_} {_} {k} step₁) (pred-zero step₂) =
 𝟘-elim (peano-axiom-for-PCF (IH ⁻¹))
 where
  IH : numeral (succ k) ＝ numeral zero
  IH = ⇓-deterministic step₁ step₂

⇓-deterministic (pred-succ step₁) (pred-succ step₂) =
 succ-removal (⇓-deterministic step₁ step₂)
 where
  succ-removal : ∀ {M N} → Succ M ＝ Succ N → M ＝ N
  succ-removal refl = refl

⇓-deterministic (succ-arg step₁) (succ-arg step₂) =
 ap Succ (⇓-deterministic step₁ step₂)

⇓-deterministic (IfZero-zero step₁ step₃) (IfZero-zero step₂ step₄) =
 ⇓-deterministic step₃ step₄

⇓-deterministic (IfZero-zero step₁ step₃)
                (IfZero-succ {_} {_} {_} {_} {_} {_} {k} step₂ step₄) =
 𝟘-elim (peano-axiom-for-PCF IH)
  where
   IH : numeral zero ＝ numeral (succ k)
   IH = ⇓-deterministic step₁ step₂

⇓-deterministic (IfZero-succ {_} {_} {_} {_} {_} {_} {k} step₁ step₃)
                (IfZero-zero step₂ step₄) =
 𝟘-elim (peano-axiom-for-PCF (IH ⁻¹))
 where
   IH : numeral (succ k) ＝ numeral zero
   IH = ⇓-deterministic step₁ step₂

⇓-deterministic (IfZero-succ step₁ step₃) (IfZero-succ step₂ step₄) =
 ⇓-deterministic step₃ step₄

⇓-deterministic (Fix-step step₁) (Fix-step step₂) =
 ⇓-deterministic step₁ step₂

⇓-deterministic (·-step {_} {_} {_} {_} {_} {E} {N} {L} step₁ step₃)
                (·-step {_} {_} {_} {_} {_} {E₁} {N} {L₁} step₂ step₄) = γ
 where
  IH : ƛ E ＝ ƛ E₁
  IH = ⇓-deterministic step₁ step₂

  ƛ-removal-＝ : ∀ {A B} → ƛ A ＝ ƛ B → A ＝ B
  ƛ-removal-＝ refl = refl

  transported-step : (E [ N ]) ⇓' L₁
  transported-step = transport (λ - → (- [ N ]) ⇓' L₁) (ƛ-removal-＝ IH ⁻¹) step₄

  γ : L ＝ L₁
  γ = ⇓-deterministic step₃ transported-step

\end{code}
