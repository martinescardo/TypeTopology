Ayberk Tosun.

Continuation of the development in `InternalModCont`.

Started on 2023-10-07.

\begin{code}

open import UF.FunExt
open import UF.Equiv
open import UF.Retracts

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
        eloquent-functions-are-UC; restriction-is-eloquent;
        dialogue-continuity; generic; B; C; prune)
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; _＝⟪_⟫_; C-restriction; Cantor; Baire; is-uniformly-continuous; _＝⟦_⟧_; BT)
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
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

to-numeral : ℕ → 〈〉 ⊢ ι
to-numeral = numeral {〈〉}

to-nat : 〈〉 ⊢ ι → ℕ
to-nat t = ⟦ t ⟧₀

to-nat-cancels-to-numeral : (n : ℕ) → ⟦ to-numeral n ⟧₀ ＝ n
to-nat-cancels-to-numeral zero     = refl
to-nat-cancels-to-numeral (succ n) = ap succ (to-nat-cancels-to-numeral n)

numeral-is-section : is-section to-numeral
numeral-is-section = to-nat , to-nat-cancels-to-numeral

is-boolean-valuedᵀ : 〈〉 ⊢ baire → 𝓤₀  ̇
is-boolean-valuedᵀ α =
 (n : 〈〉 ⊢ ι) → (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ zero) + (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ succ zero)

boolean-valuedᵀ-lemma : (t : 〈〉 ⊢ baire)
                      → is-boolean-valuedᵀ t
                      → is-boolean-point ⟦ t ⟧₀
boolean-valuedᵀ-lemma t ψ i = cases † ‡ (ψ (numeral i))
 where
  † : ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝ zero → is-boolean-valued (⟦ t ⟧₀ i)
  † p = inl q
   where
    Ⅰ = ap ⟦ t ⟧₀ (to-nat-cancels-to-numeral i ⁻¹)
    Ⅱ = p

    q = ⟦ t ⟧₀ i              ＝⟨ Ⅰ    ⟩
        ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝⟨ Ⅱ    ⟩
        0                     ∎

  ‡ : ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝ 1 → is-boolean-valued (⟦ t ⟧₀ i)
  ‡ p = inr q
   where
    Ⅰ = ap ⟦ t ⟧₀ (to-nat-cancels-to-numeral i ⁻¹)
    Ⅱ = p

    q : ⟦ t ⟧₀ i ＝ 1
    q = ⟦ t ⟧₀ i              ＝⟨ Ⅰ ⟩
        ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝⟨ Ⅱ ⟩
        1                     ∎

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

main-lemma : (t : 〈〉 ⊢ baire ⇒ ι) → ⟦ max-questionᵤᵀ · ⌜dialogue-tree⌝ t ⟧₀
                                    ＝ max-questionᵤ (prune (dialogue-tree t))
main-lemma t = {!!}

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

another-lemma : (f : Baire → ℕ)
              → (α : Baire) (bv : is-boolean-point α)
              → (β : ℕ → 𝟚)
              → to-cantor (α , bv) ＝ β
              → f α ＝ C-restriction f β
another-lemma f α bv β p =
 f α ＝⟨ {!!} ⟩ {!!} ＝⟨ {!!} ⟩ {!!} ∎

kinda-important-lemma : (f : Baire → ℕ) (α : Baire) (bv : is-boolean-point α)
                      → f α ＝ C-restriction f (to-cantor (α , bv))
kinda-important-lemma f α bv =
 f α                                  ＝⟨ {!!} ⟩
 C-restriction f (to-cantor (α , bv)) ∎

\end{code}

\begin{code}

internal-uni-mod-correct : (t : 〈〉 ⊢ (baire ⇒ ι)) (α β : 〈〉 ⊢ baire)
                         → is-boolean-valuedᵀ α
                         → is-boolean-valuedᵀ β
                         → ⟦ α ⟧₀ ＝⦅ ⟦ modulusᵤᵀ t ⟧₀ ⦆ ⟦ β ⟧₀
                         → ⟦ t · α ⟧₀ ＝ ⟦ t · β ⟧₀
internal-uni-mod-correct t α β ψ₁ ψ₂ ϑ = †
 where
  f : (ℕ → ℕ) → ℕ
  f = ⟦ t ⟧₀

  f₀ : Cantor → ℕ
  f₀ = C-restriction f

  ε : eloquent ⟦ t ⟧₀
  ε = eloquence-theorem ⟦ t ⟧₀ (t , refl)

  ε₀ : eloquent f₀
  ε₀ = restriction-is-eloquent f ε

  c : is-uniformly-continuous f₀
  c = eloquent-functions-are-UC f₀ ε₀

  mᵘ : BT ℕ
  mᵘ = pr₁ c

  c₀ : is-uniformly-continuous₀ f₀
  c₀ = uni-continuity-implies-uni-continuity₀ f₀ c

  mᵘ₀ : ℕ
  mᵘ₀ = pr₁ c₀

  rts : ⟦ max-questionᵤᵀ · ⌜dialogue-tree⌝ t ⟧₀ ＝ maximumᵤ mᵘ
  rts = {!!}

  foo : ⟦ modulusᵤᵀ t ⟧₀ ＝ mᵘ₀
  foo = ap succ rts

  α′ : Cantor₀
  α′ = ⟦ α ⟧₀ , boolean-valuedᵀ-lemma α ψ₁

  β′ : Cantor₀
  β′ = ⟦ β ⟧₀ , boolean-valuedᵀ-lemma β ψ₂

  -- θ : ⟦ α ⟧₀ ＝⟦ mᵘ ⟧ ⟦ β ⟧₀
  -- θ = {!!}

  γ : to-cantor α′ ＝⟦ mᵘ ⟧ to-cantor β′
  γ = {!!}

  ‡ : f₀ (to-cantor α′) ＝ f₀ (to-cantor β′)
  ‡ = pr₂ c (to-cantor α′) (to-cantor β′) γ

  Ⅰ = kinda-important-lemma f ⟦ α ⟧₀ (boolean-valuedᵀ-lemma α ψ₁)
  Ⅱ = kinda-important-lemma f ⟦ β ⟧₀ (boolean-valuedᵀ-lemma β ψ₂) ⁻¹

  † : f ⟦ α ⟧₀ ＝ f ⟦ β ⟧₀
  † = f ⟦ α ⟧₀              ＝⟨ Ⅰ ⟩
      f₀ (to-cantor α′)     ＝⟨ ‡ ⟩
      f₀ (to-cantor β′)     ＝⟨ Ⅱ ⟩
      f ⟦ β ⟧₀              ∎

-- One can prove a theorem saying max-question-in-boolean-paths is the same
-- thing as max-question followed by a pruning.

\end{code}
