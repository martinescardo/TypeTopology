\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module EffectfulForcing.Internal.InternalModCont where

open import MLTT.Spartan hiding (rec; _^_)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
open import EffectfulForcing.Internal.Correctness using (⌜dialogue⌝; ⌜dialogue-tree⌝-correct')
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


max-question-in-path : {Γ : Cxt}
                     → B-context【 Γ 】(κ ⇒ ι) ⊢ (⌜B⌝ ι (κ ⇒ ι)) ⇒ κ ⇒ ι
max-question-in-path = {!!}

internal-mod-cont : {Γ : Cxt} → Γ ⊢ (κ ⇒ ι) → B-context【 Γ 】 (κ ⇒ ι) ⊢ (κ ⇒ ι)
internal-mod-cont = {!!}


-- Use the 3 results:

_ = ⌜dialogue-tree⌝-correct'
_ = eloquence-theorem
_ = continuity-implies-continuity₀

internal-mod-cont-correct : (t : 〈〉 ⊢ (κ ⇒ ι)) (α β : 〈〉 ⊢ κ)
                          → ⟦ α ⟧₀ ＝⦅ ⟦ internal-mod-cont t · α ⟧₀ ⦆ ⟦ β ⟧₀
                          → ⟦ t · α ⟧₀ ＝ ⟦ t ·  β ⟧₀
internal-mod-cont-correct t α β p =
 ⟦ t · α ⟧₀                                 ＝⟨ refl ⟩
 ⟦ t ⟧₀ ⟦ α ⟧₀                              ＝⟨ Ⅰ    ⟩
 ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ ⟦ α ⟧₀ ＝⟨ {!!} ⟩
 ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ ⟦ β ⟧₀ ＝⟨ Ⅹ    ⟩
 ⟦ t ⟧₀ ⟦ β ⟧₀                              ＝⟨ refl ⟩
 ⟦ t ·  β ⟧₀                                ∎
  where
   Ⅰ : ⟦ t ⟧₀ ⟦ α ⟧₀ ＝ ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ ⟦ α ⟧₀
   Ⅰ = ⌜dialogue-tree⌝-correct' t ⟦ α ⟧₀

   Ⅹ : ⟦ ⌜dialogue⌝ (⌜dialogue-tree⌝ t) ⟧₀ ⟦ β ⟧₀ ＝ ⟦ t ⟧₀ ⟦ β ⟧₀
   Ⅹ = ⌜dialogue-tree⌝-correct' t ⟦ β ⟧₀ ⁻¹

   † : ⟦ t ⟧₀ ⟦ α ⟧₀ ＝ ⟦ t ⟧₀ ⟦ β ⟧₀
   † = {!⌜dialogue-tree⌝-correct' t ⟦ α ⟧₀!}

{--

--}

\end{code}
