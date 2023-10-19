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
        dialogue-continuity; generic; B; C)
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; _＝⟪_⟫_)
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties
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

When we restrict to the Cantor space, we can define an operation that gives us a
_uniform_ modulus of continuity. In this section, we prove this fact.

To define the Cantor space, it's tempting to augment System T with the type of
Booleans. However, we refrain from doing that here as to avoid repeating all our
proofs on System T. Instead, we adopt the approach of working with `baire` under
the implicit assumption that its range is `{0, 1}`. We define all operations on
baire under this assumption, and prove that modulus of uniform continuity
operation satisfies its specification, under the assumption of being Boolean,
which we define now.

\begin{code}

is-boolean-valued : 〈〉 ⊢ baire → 𝓤₀  ̇
is-boolean-valued α =
 (n : 〈〉 ⊢ ι) → (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ zero) + (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ succ zero)

\end{code}

Following the conventions of the `InternalModCont` module, we define three
versions of the same operation.

  1. `max-questionᵤ`, that works on the external inductive type encoding of
     dialogue trees in Agda,
  2. `max-questionᵤ⋆`, that works on the external Church encoding of dialogue
     trees in Agda, and
  3. `max-questionᵤᵀ`, that is a System T function working on the Church
     encoding of dialogue trees in System T.

\begin{code}

-- TODO
-- Should be called max-question-0-1.
-- or max-boolean-question.
-- or max-question-in-boolean-paths
max-questionᵤ : C ℕ → ℕ
max-questionᵤ (D.η n)   = 0
max-questionᵤ (D.β φ n) = max n (max n₁ n₂)
 where
  n₁ : ℕ
  n₁ = max-questionᵤ (φ ₀)

  n₂ : ℕ
  n₂ = max-questionᵤ (φ ₁)

\end{code}

\begin{code}

max-questionᵤ⋆ : D⋆ ℕ 𝟚 ℕ ℕ → ℕ
max-questionᵤ⋆ d = d (λ _ → 0) (λ g x → max x (max (g ₀) (g ₁)))

max-questionᵤᵀ : {Γ : Cxt} → Γ ⊢ (⌜B⌝ ι ι) ⇒ ι
max-questionᵤᵀ =
 ƛ (ν₀ · (ƛ Zero) · ƛ (ƛ (maxᵀ · ν₀ · (maxᵀ · (ν₁ · numeral 0) · (ν₁ · numeral 1)))))

\end{code}

\begin{code}

max-questionᵤ⋆-agreement : (d : C ℕ)
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

\end{code}

We now define the analogue of `modulus` from `InternalModCont`, following the
same conventions.

\begin{code}

modulusᵤ : C ℕ → ℕ
modulusᵤ = succ ∘ max-questionᵤ

\end{code}

\begin{code}

modulusᵤᵀ : {Γ : Cxt} →  Γ ⊢ baire ⇒ ι → B-context【 Γ 】 ι ⊢ ι
modulusᵤᵀ t = Succ' · (max-questionᵤᵀ · ⌜dialogue-tree⌝ t)

\end{code}

\begin{code}

internal-uni-mod-correct : (t : 〈〉 ⊢ (baire ⇒ ι)) (α β : 〈〉 ⊢ baire)
                         → is-boolean-valued α
                         → is-boolean-valued β
                         → ⟦ α ⟧₀ ＝⦅ ⟦ modulusᵤᵀ t ⟧₀ ⦆ ⟦ β ⟧₀
                         → ⟦ t · α ⟧₀ ＝ ⟦ t · β ⟧₀
internal-uni-mod-correct t α β ψ₁ ψ₂ ϑ = †
 where
  c₀ : is-continuous₀ ⟦ t ⟧₀
  c₀ = {!!}

  † : ⟦ t · α ⟧₀ ＝ ⟦ t · β ⟧₀
  † = {!!}

-- One can prove a theorem saying max-question-in-boolean-paths is the same
-- thing as max-question followed by a pruning.

\end{code}
