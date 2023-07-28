\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.InternalModCont where

open import MLTT.Spartan hiding (rec; _^_)
open import MLTT.List
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Dialogue using (eloquent; D; dialogue; eloquent-functions-are-continuous)
open import EffectfulForcing.MFPSAndVariations.Continuity using (is-continuous; is-continuous₀; continuity-implies-continuity₀; _＝⦅_⦆_; _＝⟪_⟫_)
open import EffectfulForcing.Internal.Correctness using (⌜dialogue⌝; ⌜dialogue-tree⌝-correct')
open import EffectfulForcing.Internal.External using (eloquence-theorem; dialogue-tree)
open import EffectfulForcing.MFPSAndVariations.SystemT using (type; ι; _⇒_;〖_〗)

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

ifz : ℕ → ℕ → ℕ → ℕ
ifz zero     n₁ n₂ = n₁
ifz (succ _) n₁ n₂ = n₂

max₀ : ℕ → ℕ → ℕ
max₀ zero     = λ n → n
max₀ (succ m) = λ n → ifz n (succ m) (succ (max₀ m n))

max₁ : ℕ → ℕ → ℕ
max₁ = rec {X = ℕ → ℕ} (λ m₀ f → λ n → ifz n (succ m₀) (succ (f n))) id

max₀-eq-max₁ : (m n : ℕ) → max₀ m n ＝ max₁ m n
max₀-eq-max₁ zero     n        = refl
max₀-eq-max₁ (succ m) zero     = refl
max₀-eq-max₁ (succ m) (succ n) =
 max₀ (succ m) (succ n)  ＝⟨ refl                              ⟩
 succ (max₀ m (succ n))  ＝⟨ ap succ (max₀-eq-max₁ m (succ n)) ⟩
 succ (max₁ m (succ n))  ＝⟨ refl                              ⟩
 max₁ (succ m) (succ n)  ∎

idᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι
idᵀ {Γ} = ƛ ν₀

ifzᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ ι ⇒ ι ⇒ ι
ifzᵀ = ƛ (ƛ (ƛ (Rec (ƛ (ƛ ν₂)) ν₁ ν₂)))

ifzᵀ-correct : (m n₁ n₂ : ℕ) → ⟦ ifzᵀ ⟧₀ m n₁ n₂ ＝ ifz m n₁ n₂
ifzᵀ-correct zero     n₁ n₂ = refl
ifzᵀ-correct (succ m) n₁ n₂ = refl

maxᵀ : {Γ : Cxt} → Γ ⊢ ι ⇒ (ι ⇒ ι)
maxᵀ =
 ƛ (Rec {σ = ι ⇒ ι} (ƛ (ƛ (ƛ (ifzᵀ · ν₀ · Succ ν₂ · Succ (ν₁ · ν₀))))) idᵀ ν₀)

maxᵀ-correct : (m n : ℕ) → ⟦ maxᵀ ⟧₀ m n ＝ max₀ m n
maxᵀ-correct zero     n        = refl
maxᵀ-correct (succ m) zero     = refl
maxᵀ-correct (succ m) (succ n) =
 ⟦ maxᵀ ⟧₀ (succ m) (succ n)                                         ＝⟨ Ⅰ    ⟩
 ifz (succ n) m (succ (⟦ maxᵀ ⟧₀ m (succ n)))                        ＝⟨ Ⅱ    ⟩
 ifz (succ n) m (succ (max₀ m (succ n)))                             ＝⟨ Ⅲ    ⟩
 ifz (succ n) m (succ (max₁ m (succ n)))                             ＝⟨ refl ⟩
 rec (λ m₀ f n → ifz n (succ m₀) (succ (f n))) id (succ m) (succ n)  ＝⟨ refl ⟩
 max₁ (succ m) (succ n)                                              ＝⟨ Ⅳ    ⟩
 max₀ (succ m) (succ n)                                              ∎
  where
   Ⅰ = ifzᵀ-correct
        (succ n)
        m
        (rec (λ m₀ f n → ⟦ ifzᵀ ⟧₀ n (succ m₀) (succ (f n))) id (succ m) (succ n))
   Ⅱ = ap (λ - → ifz (succ n) m (succ -)) (maxᵀ-correct m (succ n))
   Ⅲ = ap (λ - → ifz (succ n) m (succ -)) (max₀-eq-max₁ m (succ n))
   Ⅳ = max₀-eq-max₁ (succ m) (succ n) ⁻¹


max-question-ext : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question-ext (D.η n)   α = 0
max-question-ext (D.β φ n) α = max₀ n (max-question-ext (φ (α n)) α)

max-question-ext-church : D⋆ ℕ ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question-ext-church d α = d (λ _ → 0) (λ g x → max₀ x (g (α x)))

max-question-int : {Γ : Cxt}
                     → B-context【 Γ 】 ι ⊢ (⌜B⌝ ι ι) ⇒ κ ⇒ ι
max-question-int =
 ƛ (ƛ (ν₁ · (ƛ Zero) · ƛ (ƛ (maxᵀ · ν₀ · (ν₁ · (ν₂ · ν₀))))))

internal-mod-cont : {Γ : Cxt}
                  → Γ ⊢ (κ ⇒ ι)
                  → B-context【 Γ 】 ι ⊢ ((ι ⇒ ι) ⇒ ι)
internal-mod-cont t = max-question-int · (⌜dialogue-tree⌝ t)

-- Use the 3 results:

_ = ⌜dialogue-tree⌝-correct'
_ = eloquence-theorem
_ = continuity-implies-continuity₀

max-question-agreement : (d : D ℕ ℕ ℕ) (α : ℕ → ℕ)
       → max-question-ext d α ＝ max-question-ext-church (church-encode d) α
max-question-agreement (D.η n)   α = refl
max-question-agreement (D.β φ n) α = †
 where
  IH : max-question-ext (φ (α n)) α
     ＝ max-question-ext-church (church-encode (φ (α n))) α
  IH = max-question-agreement (φ (α n)) α

  † : max₀ n (max-question-ext (φ (α n)) α)
    ＝ church-encode (D.β φ n) (λ _ → 0) (λ g x → max₀ x (g (α x)))
  † = ap (max₀ n) IH

main-lemma : (t : 〈〉 ⊢ (κ ⇒ ι)) (α : 〈〉 ⊢ κ)
           → ⟦ max-question-int · (⌜dialogue-tree⌝ t) ⟧₀ ⟦ α ⟧₀
           ＝ max-question-ext (dialogue-tree t) ⟦ α ⟧₀
main-lemma (Rec t t₁ t₂) α = {!!}
main-lemma (ƛ t)         α = {!!}
main-lemma (t₁ · t₂)     α = {!!}

internal-mod-cont-correct : (t : 〈〉 ⊢ (κ ⇒ ι)) (α β : 〈〉 ⊢ κ)
                          → ⟦ α ⟧₀ ＝⦅ ⟦ internal-mod-cont t · α ⟧₀ ⦆ ⟦ β ⟧₀
                          → ⟦ t · α ⟧₀ ＝ ⟦ t ·  β ⟧₀
internal-mod-cont-correct t α β p = †
 where
  ⌜m⌝ : B-context【 〈〉 】 (κ ⇒ ι) ⊢ ι
  ⌜m⌝ = internal-mod-cont t · α

  m : ℕ
  m = ⟦ ⌜m⌝ ⟧₀

  ε : eloquent ⟦ t ⟧₀
  ε = eloquence-theorem ⟦ t ⟧₀ (t , refl)

  dₜ : D ℕ ℕ ℕ
  dₜ = pr₁ ε

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

  ‡ : ⟦ α ⟧₀ ＝⦅ m₀ ⦆ ⟦ β ⟧₀
  ‡ = {!!}

  † : ⟦ t ⟧₀ ⟦ α ⟧₀ ＝ ⟦ t ⟧₀ ⟦ β ⟧₀
  † = pr₂ (c₀ ⟦ α ⟧₀) ⟦ β ⟧₀ ‡

\end{code}
