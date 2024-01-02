Ayberk Tosun.

Continuation of the development in `InternalModCont`.

Started on 2023-10-07.
Finished on 2023-12-30.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import UF.Equiv hiding (⌜_⌝)
open import UF.Retracts

module EffectfulForcing.Internal.InternalModUniCont (fe : Fun-Ext) where

open import EffectfulForcing.Internal.Correctness
 using (Rnorm; Rnorm-generic; Rnorm-lemma₀; extβ; is-dialogue-for)
open import EffectfulForcing.Internal.External
 using (B⟦_⟧; B⟦_⟧₀; dialogue-tree; eloquence-theorem; ⟪⟫)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.InternalModCont fe
 using (maxᵀ; maxᵀ-correct)
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.MFPSAndVariations.Combinators
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; _＝⟪_⟫_; C-restriction; Cantor; Baire;
        is-uniformly-continuous; _＝⟦_⟧_; BT; embedding-𝟚-ℕ)
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
open import EffectfulForcing.MFPSAndVariations.Dialogue
 using (eloquent; D; dialogue; eloquent-functions-are-continuous;
        eloquent-functions-are-UC; restriction-is-eloquent; dialogue-UC;
        dialogue-continuity; generic; B; C; prune)
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type; ι; _⇒_;〖_〗)
open import MLTT.List
open import MLTT.Spartan hiding (rec; _^_)
open import Naturals.Order using (max)

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

max-questionᵤ⋆ : D⋆ ℕ ℕ ℕ ℕ → ℕ
max-questionᵤ⋆ d = d (λ _ → 0) (λ g x → max x (max (g 0) (g 1)))

max-questionᵤᵀ : {Γ : Cxt} → Γ ⊢ (⌜B⌝ ι ι) ⇒ ι
max-questionᵤᵀ =
 ƛ (ν₀ · (ƛ Zero) · ƛ (ƛ (maxᵀ · ν₀ · (maxᵀ · (ν₁ · numeral 0) · (ν₁ · numeral 1)))))

\end{code}


\begin{code}

max-questionᵤ⋆-agreement : (d : B ℕ)
                         → max-questionᵤ (prune d)
                           ＝ max-questionᵤ⋆ (church-encode d)
max-questionᵤ⋆-agreement (D.η n)   = refl
max-questionᵤ⋆-agreement (D.β φ n) = †
 where
  encode = church-encode

  IH₀ : max-questionᵤ (prune (φ 0)) ＝ max-questionᵤ⋆ (encode (φ 0))
  IH₀ = max-questionᵤ⋆-agreement (φ 0)

  IH₁ : max-questionᵤ (prune (φ 1)) ＝ max-questionᵤ⋆ (encode (φ 1))
  IH₁ = max-questionᵤ⋆-agreement (φ 1)

  † : max-questionᵤ (prune (D.β φ n)) ＝ max-questionᵤ⋆ (encode (D.β φ n))
  † =
   max-questionᵤ (D.β ((λ j → prune (φ (embedding-𝟚-ℕ j)))) n)
    ＝⟨ refl ⟩
   max n (max (max-questionᵤ (prune (φ 0))) (max-questionᵤ (prune (φ 1))))
    ＝⟨ Ⅰ ⟩
   max n (max (max-questionᵤ⋆ (encode (φ 0))) (max-questionᵤ (prune (φ 1))))
    ＝⟨ Ⅱ ⟩
   max n (max (max-questionᵤ⋆ (encode (φ 0))) (max-questionᵤ⋆ (encode (φ 1))))
    ＝⟨ refl ⟩
   max-questionᵤ⋆ (encode (D.β φ n))
    ∎
    where
     Ⅰ = ap (λ - → max n (max - (max-questionᵤ (prune (φ 1)))))          IH₀
     Ⅱ = ap (λ - → max n (max (max-questionᵤ⋆ (church-encode (φ 0))) -)) IH₁

max-questionᵀ-agreement : (d : 〈〉 ⊢ ⌜D⋆⌝ ι ι ι ι)
                        → ⟦ max-questionᵤᵀ · d ⟧₀ ＝ max-questionᵤ⋆ ⟦ d ⟧₀
max-questionᵀ-agreement d =
 ⟦ max-questionᵤᵀ · d ⟧₀                                        ＝⟨ refl  ⟩
 ⟦ d ⟧₀ (λ _ → 0) (λ g x → ⟦ maxᵀ ⟧₀ x (⟦ maxᵀ ⟧₀ (g 0) (g 1))) ＝⟨ Ⅰ     ⟩
 ⟦ d ⟧₀ (λ _ → 0) (λ g x → max x (⟦ maxᵀ ⟧₀ (g 0) (g 1)))       ＝⟨ Ⅱ     ⟩
 ⟦ d ⟧₀ (λ _ → 0) (λ g x → max x (max (g 0) (g 1)))             ＝⟨ refl  ⟩
 max-questionᵤ⋆ ⟦ d ⟧₀                                          ∎
  where
   † : (g : ℕ → ℕ) (n : ℕ)
     → ⟦ maxᵀ ⟧₀ n (⟦ maxᵀ ⟧₀ (g 0) (g 1)) ＝ max n (⟦ maxᵀ ⟧₀ (g 0) (g 1))
   † g n = maxᵀ-correct n (⟦ maxᵀ ⟧₀ (g 0) (g 1))

   ‡ : (g : ℕ → ℕ) (n : ℕ)
     → max n (⟦ maxᵀ ⟧₀ (g 0) (g 1)) ＝ max n (max (g 0) (g 1))
   ‡ g n = ap (max n) (maxᵀ-correct (g 0) (g 1))

   Ⅰ = ap (⟦ d ⟧₀ (λ _ → 0)) (dfunext fe λ g → dfunext fe λ n → † g n)
   Ⅱ = ap (⟦ d ⟧₀ (λ _ → 0)) (dfunext fe λ g → dfunext fe λ n → ‡ g n)

\end{code}

\begin{code}

main-lemma : (t : 〈〉 ⊢ baire ⇒ ι)
           → ⟦ max-questionᵤᵀ · ⌜dialogue-tree⌝ t ⟧₀
             ＝ max-questionᵤ (prune (dialogue-tree t))
main-lemma t =
  ⟦ max-questionᵤᵀ · ⌜dialogue-tree⌝ t ⟧₀           ＝⟨ refl ⟩
  ⟦ max-questionᵤᵀ ⟧₀ ⟦ ⌜dialogue-tree⌝ t ⟧₀        ＝⟨ Ⅰ    ⟩
  max-questionᵤ⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀             ＝⟨ Ⅱ    ⟩
  max-questionᵤ⋆ (church-encode (dialogue-tree t )) ＝⟨ Ⅲ    ⟩
  max-questionᵤ (prune (dialogue-tree t))           ∎
   where
    † : Rnorm (B⟦ t ⟧₀ generic) (⌜ t ⌝ · ⌜generic⌝)
    † = Rnorm-lemma₀ t generic ⌜generic⌝ Rnorm-generic

    ext : extβ (λ g x → max x (max (g 0) (g 1)))
    ext f g m n p φ =
     max m (max (f 0) (f 1))   ＝⟨ १ ⟩
     max m (max (g 0) (f 1))   ＝⟨ २ ⟩
     max m (max (g 0) (g 1))   ＝⟨ ३ ⟩
     max n (max (g 0) (g 1))   ∎
      where
       १ = ap (λ - → max m (max - (f 1))) (φ 0)
       २ = ap (λ - → max m (max (g 0) -)) (φ 1)
       ३ = ap (λ - → max - (max (g 0) (g 1))) p

    Ⅰ = max-questionᵀ-agreement (⌜dialogue-tree⌝ t)
    Ⅱ = † ι (λ _ → 0) (λ g x → max x (max (g 0) (g 1))) (λ _ → refl) ext
    Ⅲ = max-questionᵤ⋆-agreement (dialogue-tree t) ⁻¹

mod-of : B ℕ → BT ℕ
mod-of d = pr₁ (dialogue-UC (prune d))

final-step : (d : B ℕ) → max-questionᵤ (prune d) ＝ maximumᵤ (mod-of d)
final-step (D.η n)   = refl
final-step (D.β φ n) =
 max-questionᵤ (prune (D.β φ n))                                           ＝⟨ refl ⟩
 max-questionᵤ (D.β (λ j → prune (φ (embedding-𝟚-ℕ j))) n)                 ＝⟨ refl ⟩
 max n (max (max-questionᵤ (prune (φ 0))) (max-questionᵤ ((prune (φ 1))))) ＝⟨ Ⅰ    ⟩
 max n (max (maximumᵤ (mod-of (φ 0))) (max-questionᵤ ((prune (φ 1)))))     ＝⟨ Ⅱ    ⟩
 max n (max (maximumᵤ (mod-of (φ 0))) (maximumᵤ (mod-of (φ 1))))           ＝⟨ refl ⟩
 maximumᵤ (mod-of (D.β φ n))                                               ∎
  where
   Ⅰ = ap (λ - → max n (max - (max-questionᵤ (prune (φ 1))))) (final-step (φ 0))
   Ⅱ = ap (λ - → max n (max (maximumᵤ (mod-of (φ 0))) -)) (final-step (φ 1))

{-
 max-questionᵤ (prune (dialogue-tree t)) ＝⟨ {!dialogue-tree t!} ⟩
 {!!}                                    ＝⟨ {!!} ⟩
 maximumᵤ (mod-of t)                     ∎
-}

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

-- another-lemma : (f : Baire → ℕ)
--               → (α : Baire) (bv : is-boolean-point α)
--               → (β : ℕ → 𝟚)
--               → to-cantor (α , bv) ＝ β
--               → f α ＝ C-restriction f β
-- another-lemma f α bv β p =
--  f α ＝⟨ {!!} ⟩ {!!} ＝⟨ {!!} ⟩ {!!} ∎

agreement-with-restriction : (f : Baire → ℕ) (α : Baire) (bv : is-boolean-point α)
                           → f α ＝ C-restriction f (to-cantor (α , bv))
agreement-with-restriction f α bv =
  f α                                   ＝⟨ refl ⟩
  f′ (α , bv)                           ＝⟨ † ⟩
  f′ (to-cantor₀ (to-cantor (α , bv)))  ＝⟨ refl ⟩
  f₀ (to-cantor (α , bv))               ∎
   where
    f₀ : Cantor → ℕ
    f₀ = C-restriction f

    f′ : Cantor₀ → ℕ
    f′ = f ∘ pr₁

    † = ap f′ (to-cantor₀-cancels-to-cantor (α , bv) ⁻¹)

\end{code}

\begin{code}

internal-uni-mod-correct : (t : 〈〉 ⊢ (baire ⇒ ι)) (α β : 〈〉 ⊢ baire)
                         → is-boolean-valuedᵀ α
                         → is-boolean-valuedᵀ β
                         → ⟦ α ⟧₀ ＝⦅ ⟦ modulusᵤᵀ t ⟧₀ ⦆ ⟦ β ⟧₀
                         → ⟦ t · α ⟧₀ ＝ ⟦ t · β ⟧₀
internal-uni-mod-correct t αᵀ βᵀ ψ₁ ψ₂ ϑ = †
 where
  f : Baire → ℕ
  f = ⟦ t ⟧₀

  α : Baire
  α = ⟦ αᵀ ⟧₀

  β : Baire
  β = ⟦ βᵀ ⟧₀

  α′ : Cantor₀
  α′ = α , boolean-valuedᵀ-lemma αᵀ ψ₁

  β′ : Cantor₀
  β′ = β , boolean-valuedᵀ-lemma βᵀ ψ₂

  f₀ : Cantor → ℕ
  f₀ = C-restriction f

  ε : eloquent ⟦ t ⟧₀
  ε = eloquence-theorem ⟦ t ⟧₀ (t , refl)

  ε₀ : eloquent f₀
  ε₀ = restriction-is-eloquent f ε

  c : is-uniformly-continuous f₀
  c = eloquent-functions-are-UC f₀ ε₀

  bt : BT ℕ
  bt = mod-of (dialogue-tree t)

  c₀ : is-uniformly-continuous₀ f₀
  c₀ = uni-continuity-implies-uni-continuity₀ f₀ c

  mᵘ₀ : ℕ
  mᵘ₀ = succ (maximumᵤ bt)

  rts : ⟦ max-questionᵤᵀ · ⌜dialogue-tree⌝ t ⟧₀ ＝ maximumᵤ bt
  rts = ⟦ max-questionᵤᵀ · ⌜dialogue-tree⌝ t ⟧₀   ＝⟨ main-lemma t ⟩
        max-questionᵤ (prune (dialogue-tree t))   ＝⟨ final-step (dialogue-tree t) ⟩
        maximumᵤ bt                               ∎

  q : ⟦ modulusᵤᵀ t ⟧₀ ＝ succ (maximumᵤ bt)
  q = ap succ rts

  ϑⁿ : α ＝⦅ ⟦ modulusᵤᵀ t ⟧₀ ⦆ β
  ϑⁿ = ϑ

  θ₂ : α ＝⦅ succ (maximumᵤ bt) ⦆ β
  θ₂ = transport (λ - → α ＝⦅ - ⦆ β) q ϑ

  θ₁ : α ＝⦅ succ (maximum (sequentialize bt)) ⦆ β
  θ₁ = transport
        (λ - → α ＝⦅ - ⦆ β)
        (ap succ (maximumᵤ′-equivalent-to-maximumᵤ bt))
        θ₂

  η : α ＝⟪ sequentialize bt ⟫ β
  η = ＝⦅⦆-implies-＝⟪⟫-for-suitable-modulus α β (sequentialize bt) θ₁

  δ′ : α ＝⟪ sequentialize bt ⟫₀ β
  δ′ = ＝⟪⟫-implies-＝⟪⟫₀ α β (sequentialize bt) η

  δ : α ＝⟦ bt ⟧ β
  δ = ＝⟪⟫₀-implies-＝⟦⟧ α β bt δ′

  γ : to-cantor α′ ＝⟦ bt ⟧ to-cantor β′
  γ = to-cantor-＝⟦⟧
       α
       β
       (boolean-valuedᵀ-lemma αᵀ ψ₁)
       (boolean-valuedᵀ-lemma βᵀ ψ₂)
       bt
       δ


  ‡ : f₀ (to-cantor α′) ＝ f₀ (to-cantor β′)
  ‡ = pr₂ c (to-cantor α′) (to-cantor β′) γ

  Ⅰ = agreement-with-restriction f α (boolean-valuedᵀ-lemma αᵀ ψ₁)
  Ⅱ = agreement-with-restriction f β (boolean-valuedᵀ-lemma βᵀ ψ₂) ⁻¹

  † : f α ＝ f β
  † = f α               ＝⟨ Ⅰ ⟩
      f₀ (to-cantor α′) ＝⟨ ‡ ⟩
      f₀ (to-cantor β′) ＝⟨ Ⅱ ⟩
      f β               ∎

-- One can prove a theorem saying max-question-in-boolean-paths is the same
-- thing as max-question followed by a pruning.

\end{code}
