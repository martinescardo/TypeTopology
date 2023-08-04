Ayberk Tosun

Based on some previous work by Martín Escardó.

In this module, we prove the correctness of the internal modulus of continuity
operator.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt

module EffectfulForcing.Internal.InternalModCont (fe : Fun-Ext) where

open import MLTT.Spartan hiding (rec; _^_)
open import MLTT.List
open import Naturals.Order using (max)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Dialogue
 using (eloquent; D; dialogue; eloquent-functions-are-continuous; dialogue-continuity)
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; is-continuous₀; continuity-implies-continuity₀;
        _＝⦅_⦆_; _＝⟪_⟫_; modulus-at₀; maximum)
open import EffectfulForcing.Internal.Correctness
 using (⌜dialogue⌝; ⌜dialogue-tree⌝-correct')
open import EffectfulForcing.Internal.External
 using (eloquence-theorem; dialogue-tree)
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type; ι; _⇒_;〖_〗)

\end{code}

First, we define some nicer syntax for inherently typed System T terms.

\begin{code}

_⊢_ : Cxt → type → 𝓤₀  ̇
_⊢_ Γ τ = T Γ τ

infix 4 _⊢_

baire : type
baire = ι ⇒ ι

\end{code}

Some examples

\begin{code}

lam-example₁ : (n : ℕ) → ⟦ ƛ ν₀ ⟧₀ n ＝ n
lam-example₁ n = refl

lam-example₂ : (m n : ℕ) → ⟦ ƛ (ƛ ν₁) ⟧₀ m n ＝ m
lam-example₂ m n = refl

\end{code}

The `ifz` operator in Agda and in System T respectively. We adopt the convention
of using the superscript `ᵀ` to denote internal version of an operator that we
have defined in Agda.

\begin{code}

ifz : ℕ → ℕ → ℕ → ℕ
ifz zero     n₁ n₂ = n₁
ifz (succ _) n₁ n₂ = n₂

ifzᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι ⇒ ι ⇒ ι
ifzᵀ = ƛ (ƛ (ƛ (Rec (ƛ (ƛ ν₂)) ν₁ ν₂)))

ifzᵀ-correct : (m n₁ n₂ : ℕ) → ⟦ ifzᵀ ⟧₀ m n₁ n₂ ＝ ifz m n₁ n₂
ifzᵀ-correct zero     n₁ n₂ = refl
ifzᵀ-correct (succ m) n₁ n₂ = refl

\end{code}

The predecessor operator.

\begin{code}

pred : ℕ → ℕ
pred zero     = zero
pred (succ n) = n

predᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι
predᵀ = Rec' {σ = ι} · (ƛ (ƛ ν₁)) · Zero

predᵀ-correct : (n : ℕ) → ⟦ predᵀ ⟧₀ n ＝ pred n
predᵀ-correct zero     = refl
predᵀ-correct (succ n) = refl

\end{code}

The identity function on the naturals in System T.

\begin{code}

idᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι
idᵀ {Γ} = ƛ ν₀

\end{code}

We now define the System T version of the `max` operator computing the maximum
of two given natural numbers.

\begin{code}

maxᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ (ι ⇒ ι)
maxᵀ =
 ƛ (Rec (ƛ (ƛ (ƛ (ifzᵀ · ν₀ · Succ ν₂ · Succ (ν₁ · (predᵀ · ν₀)))))) idᵀ ν₀)

maxᵀ-correct : (m n : ℕ) → ⟦ maxᵀ ⟧₀ m n ＝ max m n
maxᵀ-correct zero     n        = refl
maxᵀ-correct (succ m) zero     = refl
maxᵀ-correct (succ m) (succ n) =
 ⟦ maxᵀ ⟧₀ (succ m) (succ n)                                            ＝⟨ refl ⟩
 ⟦ ifzᵀ ⟧₀ (succ n) (succ m) (succ (⟦ maxᵀ ⟧₀ m (⟦ predᵀ ⟧₀ (succ n)))) ＝⟨ Ⅰ    ⟩
 ifz (succ n) (succ m) (succ (⟦ maxᵀ ⟧₀ m (⟦ predᵀ ⟧₀ (succ n))))       ＝⟨ refl ⟩
 succ (⟦ maxᵀ ⟧₀ m (⟦ predᵀ ⟧₀ (succ n)))                               ＝⟨ refl ⟩
 succ (⟦ maxᵀ ⟧₀ m (pred (succ n)))                                     ＝⟨ Ⅱ    ⟩
 succ (max m n)                                                         ＝⟨ refl ⟩
 max (succ m) (succ n)                                                  ∎
  where
   Ⅰ = ifzᵀ-correct (succ n) (succ m) (succ (⟦ maxᵀ ⟧₀ m (⟦ predᵀ ⟧₀ (succ n))))
   Ⅱ = ap succ (maxᵀ-correct m n)

\end{code}

We will use the `maxᵀ` operator to define the internal modulus of continuity
operator. To work towards this, we define the external version of the operator
that we call `max-question`.

There will be three different versions of this operator:

  1. `max-question`, that works on the external inductive type encoding of
     dialogue trees in Agda,
  2. `max-question⋆`, that works on the external Church encoding of dialogue
     trees in Agda, and
  3. `max-questionᵀ`, that is a System T function working on the Church encoding
     of dialogue trees in System T.

\begin{code}

max-question : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question (D.η n)   α = 0
max-question (D.β φ n) α = max n (max-question (φ (α n)) α)

max-question₀ : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question₀ d α = maximum (pr₁ (dialogue-continuity d α))

\end{code}

\begin{code}

external-mod-cont : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
external-mod-cont d α = succ (max-question d α)

external-mod-cont′ : (d : D ℕ ℕ ℕ) → (ℕ → ℕ) → ℕ
external-mod-cont′ d α = succ (max-question₀ d α)

max-ext-equal-to-max-ext′ : (d : D ℕ ℕ ℕ) (α : ℕ → ℕ)
                          → max-question d α ＝ max-question₀ d α
max-ext-equal-to-max-ext′ (D.η n)   α = refl
max-ext-equal-to-max-ext′ (D.β φ n) α = ap (max n) (max-ext-equal-to-max-ext′ (φ (α n)) α)

max-question⋆ : D⋆ ℕ ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question⋆ d α = d (λ _ → 0) (λ g x → max x (g (α x)))

max-question-int : {Γ : Cxt} → Γ ⊢ (⌜B⌝ ι ι) ⇒ baire ⇒ ι
max-question-int = ƛ (ƛ (ν₁ · (ƛ Zero) · ƛ (ƛ (maxᵀ · ν₀ · (ν₁ · (ν₂ · ν₀))))))

internal-mod-cont : {Γ : Cxt}
                   → Γ ⊢ baire ⇒ ι
                   → B-context【 Γ 】 ι ⊢ (ι ⇒ ι) ⇒ ι
internal-mod-cont t = comp · Succ' · (max-question-int · ⌜dialogue-tree⌝ t)

-- Use the 3 results:

_ = ⌜dialogue-tree⌝-correct'
_ = eloquence-theorem
_ = continuity-implies-continuity₀

max-question-agreement : (d : D ℕ ℕ ℕ) (α : ℕ → ℕ)
                       → max-question d α ＝ max-question⋆ (church-encode d) α
max-question-agreement (D.η n)   α = refl
max-question-agreement (D.β φ n) α = †
 where
  IH : max-question (φ (α n)) α
     ＝ max-question⋆ (church-encode (φ (α n))) α
  IH = max-question-agreement (φ (α n)) α

  † : max n (max-question (φ (α n)) α)
    ＝ church-encode (D.β φ n) (λ _ → 0) (λ g x → max x (g (α x)))
  † = ap (max n) IH

main-lemma : (d : 〈〉 ⊢ ⌜D⋆⌝ ι ι ι ι) (α : ℕ → ℕ)
           → ⟦ max-question-int · d ⟧₀ α ＝ max-question⋆ ⟦ d ⟧₀ α
main-lemma d α =
 ⟦ max-question-int · d ⟧₀ α         ＝⟨ refl ⟩
 ⟦ d ⟧₀ (λ _ → 0) (⟦ ƛ (ƛ (maxᵀ · ν₀ · (ν₁ · (ν₂ · ν₀)))) ⟧ ((⟨⟩ ‚ ⟦ d ⟧₀) ‚ α))   ＝⟨  refl ⟩
 ⟦ d ⟧₀ (λ _ → 0) (λ g x → ⟦ maxᵀ ⟧₀ x (g (α x)))                                  ＝⟨ †    ⟩
 ⟦ d ⟧₀ (λ _ → 0) (λ g x → max x (g (α x)))                                        ＝⟨ refl ⟩
 max-question⋆ ⟦ d ⟧₀ α    ∎
  where
   † = ap
        (⟦ d ⟧₀ (λ _ → 0))
        (dfunext fe λ g → dfunext fe λ x → maxᵀ-correct x (g (α x)))

internal-mod-cont-correct : (t : 〈〉 ⊢ (baire ⇒ ι)) (α β : 〈〉 ⊢ baire)
                          → ⟦ α ⟧₀ ＝⦅ ⟦ internal-mod-cont t · α ⟧₀ ⦆ ⟦ β ⟧₀
                          → ⟦ t · α ⟧₀ ＝ ⟦ t ·  β ⟧₀
internal-mod-cont-correct t α β p = †
 where
  ⌜m⌝ : B-context【 〈〉 】 (baire ⇒ ι) ⊢ ι
  ⌜m⌝ = internal-mod-cont t · α

  m : ℕ
  m = ⟦ ⌜m⌝ ⟧₀

  ε : eloquent ⟦ t ⟧₀
  ε = eloquence-theorem ⟦ t ⟧₀ (t , refl)

  dₜ : D ℕ ℕ ℕ
  dₜ = pr₁ ε

  foo : dialogue-tree t ＝ dₜ
  foo = refl

  φ : dialogue dₜ ∼ ⟦ t ⟧₀
  φ = pr₂ ε

  γ : ⟦ t ⟧₀ ⟦ α ⟧₀ ＝ dialogue dₜ ⟦ α ⟧₀
  γ = φ ⟦ α ⟧₀ ⁻¹

  p′ : ⟦ α ⟧₀ ＝⦅ m ⦆ ⟦ β ⟧₀
  p′ = p

  c : is-continuous ⟦ t ⟧₀
  c = eloquent-functions-are-continuous ⟦ t ⟧₀ ε

  c₀ : is-continuous₀ ⟦ t ⟧₀
  c₀ = continuity-implies-continuity₀ ⟦ t ⟧₀ c

  m₀ : ℕ
  m₀ = pr₁ (c₀ ⟦ α ⟧₀)

  lemma : ⟦ ⌜dialogue-tree⌝ t ⟧₀ ＝ church-encode (dialogue-tree t)
  lemma = dfunext fe {!!}

  q : ⟦ internal-mod-cont t · α ⟧₀ ＝ m₀
  q = ⟦ internal-mod-cont t · α ⟧₀                                  ＝⟨ refl ⟩
      succ (⟦ max-question-int · (⌜dialogue-tree⌝ t) ⟧₀ ⟦ α ⟧₀)     ＝⟨ ap succ (main-lemma (⌜dialogue-tree⌝ t) ⟦ α ⟧₀) ⟩
      succ (max-question⋆ ⟦ ⌜dialogue-tree⌝ t  ⟧₀ ⟦ α ⟧₀) ＝⟨ ♣ ⟩
      succ (max-question⋆ (church-encode dₜ) ⟦ α ⟧₀)      ＝⟨ ap succ (max-question-agreement dₜ ⟦ α ⟧₀ ⁻¹) ⟩
      succ (max-question dₜ ⟦ α ⟧₀)                             ＝⟨ ap succ (max-ext-equal-to-max-ext′ dₜ ⟦ α ⟧₀) ⟩
      succ (max-question₀ dₜ ⟦ α ⟧₀)                                ＝⟨ refl ⟩
      modulus-at₀ ⟦ t ⟧₀ c₀ ⟦ α ⟧₀                                  ∎
       where
        ♣ : succ (max-question⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀ ⟦ α ⟧₀)
          ＝ succ (max-question⋆ (church-encode dₜ) ⟦ α ⟧₀)
        ♣ = ap succ (ap (λ - → (max-question⋆ - ⟦ α ⟧₀)) lemma)

  ‡ : ⟦ α ⟧₀ ＝⦅ m₀ ⦆ ⟦ β ⟧₀
  ‡ = transport (λ - → ⟦ α ⟧₀ ＝⦅ - ⦆ ⟦ β ⟧₀) q p

  † : ⟦ t ⟧₀ ⟦ α ⟧₀ ＝ ⟦ t ⟧₀ ⟦ β ⟧₀
  † = pr₂ (c₀ ⟦ α ⟧₀) ⟦ β ⟧₀ ‡

\end{code}
