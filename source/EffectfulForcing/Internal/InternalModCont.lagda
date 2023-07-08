\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.InternalModCont where

open import MLTT.Spartan hiding (rec; _^_)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.Internal.Correctness using (⌜dialogue-tree⌝-correct')
open import EffectfulForcing.Internal.External using (eloquence-theorem)
open import EffectfulForcing.MFPSAndVariations.SystemT using (type; ι; _⇒_)

\end{code}

The following is copied from Martín Escardó's work in the
`MFPSAndVariations.Internal` module

\begin{code}

_⊢_ : Cxt → type → 𝓤₀  ̇
_⊢_ Γ τ = T Γ τ

infix 4 _⊢_

κ : type
κ = ι ⇒ ι

lam-example₁ : (n : ℕ) → ⟦ ƛ ν₀ ⟧₀ n ＝ n
lam-example₁ n = refl

lam-example₂ : (m n : ℕ) → ⟦ ƛ (ƛ ν₁) ⟧₀ m n ＝ m
lam-example₂ m n = refl

natrec : {A : 𝓤₀  ̇} → A → (ℕ → A → A) → ℕ → A
natrec z s zero     = z
natrec z s (succ n) = s n (natrec z s n)

ifz : ℕ → ℕ → ℕ → ℕ
ifz zero     n₁ n₂ = n₁
ifz (succ _) n₁ n₂ = n₂

max₀ : ℕ → ℕ → ℕ
max₀ zero     = λ n → n
max₀ (succ m) = λ n → ifz n (succ m) (succ (max₀ m n))

idᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι
idᵀ {Γ} = ƛ ν₀

ifzᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι ⇒ ι ⇒ ι
ifzᵀ = ƛ (ƛ (ƛ (Rec (ƛ (ƛ ν₃)) ν₂ ν₀)))

ifzᵀ-correct : (m n₁ n₂ : ℕ) → ⟦ ifzᵀ ⟧₀ n₁ n₂ m ＝ ifz m n₁ n₂
ifzᵀ-correct zero     n₁ n₂ = refl
ifzᵀ-correct (succ m) n₁ n₂ = refl

maxᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι ⇒ ι
maxᵀ = ƛ (Rec (ƛ (ƛ (ƛ (ifzᵀ · (Succ ν₀) · Succ (ν₁ · ν₂) · ν₃)))) idᵀ ν₀)

maxᵀ-correct : (m n : ℕ) → ⟦ maxᵀ ⟧₀ m n ＝ max₀ m n
maxᵀ-correct zero     n = refl
maxᵀ-correct (succ m) n =
 ⟦ maxᵀ ⟧₀ (succ m) n                    ＝⟨ refl ⟩
 rec (⟦ {!!} ⟧₀ (succ (⟦ maxᵀ ⟧₀ m n))) n (succ m)                     ＝⟨ {!!} ⟩
 ⟦ ifzᵀ ⟧₀ (succ m) (succ (max₀ m n)) n ＝⟨ ifzᵀ-correct n (succ m) (succ (max₀ m n)) ⟩
 ifz n (succ m) (succ (max₀ m n))       ＝⟨ refl ⟩
 max₀ (succ m) n                        ∎

max-question-in-path : {Γ : Cxt}
                     → B-context【 Γ 】(κ ⇒ ι) ⊢ (⌜B⌝ ι (κ ⇒ ι)) ⇒ κ ⇒ ι
max-question-in-path = {!!}

internal-mod-cont : {Γ : Cxt} → Γ ⊢ (κ ⇒ ι) → B-context【 Γ 】 (κ ⇒ ι) ⊢ (κ ⇒ ι)
internal-mod-cont = {!!}

-- Use the 3 results:

_ = ⌜dialogue-tree⌝-correct'
_ = eloquence-theorem
_ = continuity-implies-continuity₀

internal-mod-cont-correct : (t : 〈〉 ⊢ (κ ⇒ ι)) (α : 〈〉 ⊢ κ) (β : 〈〉 ⊢ κ)
                          → ⟦ α ⟧₀ ＝⦅ ⟦ internal-mod-cont t · α ⟧₀ ⦆ ⟦ β ⟧₀
                          → ⟦ t · α ⟧₀ ＝ ⟦ t ·  β ⟧₀
internal-mod-cont-correct = {!!}

\end{code}
