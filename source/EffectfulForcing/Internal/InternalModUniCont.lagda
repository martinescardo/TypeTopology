Ayberk Tosun.

Continuation of the development in `InternalModCont`.

Started on 2023-10-07.

\begin{code}

open import UF.FunExt

module EffectfulForcing.Internal.InternalModUniCont (fe : Fun-Ext) where

open import MLTT.Spartan hiding (rec; _^_)
open import MLTT.List
open import Naturals.Order using (max)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Dialogue
 using (eloquent; D; dialogue; eloquent-functions-are-continuous;
        dialogue-continuity; generic)
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; is-continuous₀; continuity-implies-continuity₀;
        _＝⦅_⦆_; _＝⟪_⟫_; modulus-at₀; maximum)
open import EffectfulForcing.Internal.Correctness
 using (Rnorm-generic; is-dialogue-for; extβ; Rnorm-lemma₀; Rnorm)
open import EffectfulForcing.Internal.External
 using (eloquence-theorem; dialogue-tree; ⟪⟫; B⟦_⟧; B⟦_⟧₀)
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type; ι; _⇒_;〖_〗)
open import EffectfulForcing.Internal.InternalModCont fe using (maxᵀ)

\end{code}

First, we define some nicer syntax for inherently typed System T terms.

\begin{code}

_⊢_ : Cxt → type → 𝓤₀  ̇
_⊢_ Γ τ = T Γ τ

infix 4 _⊢_

baire : type
baire = ι ⇒ ι

\end{code}

When we restrict to the Cantor space, the internal modulus of continuity
operator gives us a _uniform_ modulus of continuity. In this section, we prove
this fact.

\begin{code}

is-boolean : 〈〉 ⊢ baire → 𝓤₀  ̇
is-boolean α =
 (n : 〈〉 ⊢ ι) → (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ zero) + (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ succ zero)

max-questionᵤ : D ℕ 𝟚 ℕ → ℕ
max-questionᵤ (D.η n)   = 0
max-questionᵤ (D.β φ n) = max n (max n₁ n₂)
 where
  n₁ : ℕ
  n₁ = max-questionᵤ (φ ₀)

  n₂ : ℕ
  n₂ = max-questionᵤ (φ ₁)


max-questionᵤ⋆ : D⋆ ℕ 𝟚 ℕ ℕ → ℕ
max-questionᵤ⋆ d = d (λ _ → 0) (λ g x → max x (max (g ₀) (g ₁)))

max-questionᵤᵀ : {Γ : Cxt} → Γ ⊢ (⌜B⌝ ι ι) ⇒ ι
max-questionᵤᵀ =
 ƛ (ν₀ · (ƛ Zero) · ƛ (ƛ (maxᵀ · ν₀ · (maxᵀ · (ν₁ · numeral 0) · (ν₁ · numeral 1)))))

max-questionᵤ⋆-agreement : (d : D ℕ 𝟚 ℕ)
                         → max-questionᵤ d ＝ max-questionᵤ⋆ (church-encode d)
max-questionᵤ⋆-agreement (D.η n)   = refl
max-questionᵤ⋆-agreement (D.β φ n) = †
 where
  ch-encode = church-encode

  IH₀ : max-questionᵤ (φ ₀) ＝ max-questionᵤ⋆ (church-encode (φ ₀))
  IH₀ = max-questionᵤ⋆-agreement (φ ₀)

  IH₁ : max-questionᵤ (φ ₁) ＝ max-questionᵤ⋆ (church-encode (φ ₁))
  IH₁ = max-questionᵤ⋆-agreement (φ ₁)

  Ⅰ = ap (λ - → max - (max-questionᵤ (φ ₁))) IH₀
  Ⅱ = ap (λ - → max (max-questionᵤ⋆ (church-encode (φ ₀))) -) IH₁

  ‡ =
   max (max-questionᵤ (φ ₀)) (max-questionᵤ (φ ₁))                           ＝⟨ Ⅰ ⟩
   max (max-questionᵤ⋆ (ch-encode (φ ₀))) (max-questionᵤ (φ ₁))              ＝⟨ Ⅱ ⟩
   max (max-questionᵤ⋆ (ch-encode (φ ₀))) (max-questionᵤ⋆ (ch-encode (φ ₁))) ∎

  † : max-questionᵤ (D.β φ n) ＝ max-questionᵤ⋆ (church-encode (D.β φ n))
  † = ap (max n) ‡

uni-modulus : D ℕ 𝟚 ℕ → ℕ
uni-modulus = succ ∘ max-questionᵤ

internal-uni-mod-correct : (t : 〈〉 ⊢ (baire ⇒ ι)) (α β : 〈〉 ⊢ baire)
                         → is-boolean α
                         → is-boolean β
                         → {!!}
internal-uni-mod-correct = {!!}

\end{code}
