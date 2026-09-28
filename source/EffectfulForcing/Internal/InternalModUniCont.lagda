--------------------------------------------------------------------------------
author:         Ayberk Tosun
date-started:   2023-10-07
date-completed: 2023-12-30
dates-updated:  [2024-03-12]
--------------------------------------------------------------------------------

Continuation of the development in `InternalModCont` towards uniform continuity.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Retracts

module EffectfulForcing.Internal.InternalModUniCont (fe : Fun-Ext) where

open import EffectfulForcing.Internal.Correctness
 using (Rnorm; Rnorm-generic; Rnorm-lemma₀; is-dialogue-for)
open import EffectfulForcing.Internal.ExtensionalEquality
open import EffectfulForcing.Internal.External
 using (B⟦_⟧; B⟦_⟧₀; dialogue-tree; eloquence-theorem; ⟪⟫)
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.InternalModCont fe
 using (maxᵀ; maxᵀ-correct; ⟦maxᵀ⟧≡max)
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Subst
 using (≡-refl₀)
open import EffectfulForcing.MFPSAndVariations.Church
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; _＝⟪_⟫_; C-restriction; Cantor; Baire;
        is-uniformly-continuous; _＝⟦_⟧_; BT; embedding-𝟚-ℕ)
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
open import EffectfulForcing.MFPSAndVariations.Dialogue
 using (B; C; D; dialogue-continuity; dialogue; eloquent-functions-are-UC;
        eloquent-functions-are-continuous; eloquent; generic; prune;
        restriction-is-eloquent; dialogue-UC)
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type; ι; _⇒_;〖_〗)
open import MLTT.Spartan hiding (rec; _^_)
open import Naturals.Order using (max)

\end{code}

First, we define some nicer syntax for inherently typed System T terms.

\begin{code}

_⊢_ : Cxt → type → 𝓤₀ ̇
_⊢_ Γ τ = T Γ τ

infix 4 _⊢_

baire : type
baire = ι ⇒ ι

\end{code}

In module `EffectfulForcing.Internal.InternalModCont`, we defined a System T
operation that computes moduli of continuity of maps from Baire space into ℕ.
In this module, we develop the same operation for maps on the Cantor space --
but this time it computes the modulus of _uniform_ continuity.

To define the Cantor type, it's tempting to augment System T with the type of
Booleans. However, we refrain from doing that here as to avoid repeating all our
proofs on System T. Instead, we adopt the approach of working with the `baire`
type under the implicit assumption that its range is `{0, 1}`. We define all
operations on the `baire` type under this assumption, and prove that the modulus
of uniform continuity operation satisfies its specification.

\section{Preliminaries}

We define the functions `to-numeral` and `to-nat`.

  * The function `to-numeral` gives the System T representation of a natural
    number.
  * The function `to-nat` gives the natural number represented by a System T
    numeral.

\begin{code}

to-numeral : ℕ → 〈〉 ⊢ ι
to-numeral = numeral {〈〉}

to-nat : 〈〉 ⊢ ι → ℕ
to-nat t = ⟦ t ⟧₀

\end{code}

The function `to-nat` is a retraction of `to-numeral`.

\begin{code}

to-nat-cancels-to-numeral : to-nat ∘ to-numeral ∼ id
to-nat-cancels-to-numeral zero     = refl
to-nat-cancels-to-numeral (succ n) = ap succ (to-nat-cancels-to-numeral n)

numeral-is-section : is-section to-numeral
numeral-is-section = to-nat , to-nat-cancels-to-numeral

\end{code}

In module `EffectfulForcing.MFPSAndVariations.ContinuityProperties`, we defined
the notion of a Boolean point. We now define the same notion for System T
representations of points of the Baire space.

\begin{code}

is-boolean-pointᵀ : 〈〉 ⊢ baire → 𝓤₀ ̇
is-boolean-pointᵀ α =
 (n : 〈〉 ⊢ ι) → (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ 0) + (⟦ α ⟧₀ ⟦ n ⟧₀ ＝ 1)

\end{code}

If a System T term `t` satisfies `is-boolean-pointᵀ`, then its interpretation
`⟦ t ⟧` obviously satisfies `is-boolean-point`.

\begin{code}

boolean-valuedᵀ-lemma : (t : 〈〉 ⊢ baire)
                      → is-boolean-pointᵀ t
                      → is-boolean-point ⟦ t ⟧₀
boolean-valuedᵀ-lemma t ψ i = cases † ‡ (ψ (numeral i))
 where
  ※ = ap ⟦ t ⟧₀ (to-nat-cancels-to-numeral i ⁻¹)

  † : ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝ zero → is-boolean-valued (⟦ t ⟧₀ i)
  † p = inl q
   where
    q : ⟦ t ⟧₀ i ＝ 0
    q = ⟦ t ⟧₀ i ＝⟨ ※ ⟩ ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝⟨ p ⟩ 0 ∎

  ‡ : ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝ 1 → is-boolean-valued (⟦ t ⟧₀ i)
  ‡ p = inr q
   where
    q : ⟦ t ⟧₀ i ＝ 1
    q = ⟦ t ⟧₀ i ＝⟨ ※ ⟩ ⟦ t ⟧₀ ⟦ numeral i ⟧₀ ＝⟨ p ⟩ 1 ∎

\end{code}

Following the conventions of the `InternalModCont` module, we define three
versions of the same operation.

  1. `max-boolean-question`, that works on the external inductive type encoding
     of dialogue trees in Agda,
  2. `max-boolean-question⋆`, that works on the external Church encoding of
     dialogue trees in Agda, and
  3. `max-boolean-questionᵀ`, that is a System T function working on the Church
     encoding of dialogue trees in System T.

\begin{code}

max-boolean-question : C ℕ → ℕ
max-boolean-question (D.η n)   = 0
max-boolean-question (D.β φ n) = max n (max n₁ n₂)
 where
  n₁ : ℕ
  n₁ = max-boolean-question (φ ₀)

  n₂ : ℕ
  n₂ = max-boolean-question (φ ₁)

max-boolean-question⋆ : D⋆ ℕ ℕ ℕ ℕ → ℕ
max-boolean-question⋆ d = d (λ _ → 0) (λ g x → max x (max (g 0) (g 1)))

max-boolean-questionᵀ : {Γ : Cxt} → Γ ⊢ (⌜B⌝ ι ι) ⇒ ι
max-boolean-questionᵀ =
 ƛ
  (ν₀
   · (ƛ Zero)
   · ƛ (ƛ (maxᵀ · ν₀ · (maxᵀ · (ν₁ · numeral 0)
                             · (ν₁ · numeral 1)))))

\end{code}

We now prove two lemmas capturing the agreement of `max-boolean-question`,
`max-boolean-question⋆`, and `max-boolean-questionᵀ`.

\begin{code}

max-boolean-question⋆-agreement : (d : B ℕ)
                                → max-boolean-question (prune d)
                                  ＝ max-boolean-question⋆ (church-encode d)
max-boolean-question⋆-agreement (D.η n)   = refl
max-boolean-question⋆-agreement (D.β φ n) = †
 where
  encode = church-encode

  IH₀ : max-boolean-question (prune (φ 0))
        ＝ max-boolean-question⋆ (encode (φ 0))
  IH₀ = max-boolean-question⋆-agreement (φ 0)

  IH₁ : max-boolean-question (prune (φ 1))
        ＝ max-boolean-question⋆ (encode (φ 1))
  IH₁ = max-boolean-question⋆-agreement (φ 1)

  n₀  = max-boolean-question (prune (φ 0))
  n₁  = max-boolean-question (prune (φ 1))
  n₀⋆ = max-boolean-question⋆ (encode (φ 0))
  n₁⋆ = max-boolean-question⋆ (encode (φ 1))

  Ⅰ = ap (λ - → max n (max - (max-boolean-question (prune (φ 1)))))          IH₀
  Ⅱ = ap (λ - → max n (max (max-boolean-question⋆ (church-encode (φ 0))) -)) IH₁

  † : max-boolean-question (prune (D.β φ n))
      ＝ max-boolean-question⋆ (encode (D.β φ n))
  † =
   max-boolean-question (D.β ((λ j → prune (φ (embedding-𝟚-ℕ j)))) n) ＝⟨refl⟩
   max n (max n₀  n₁)                                                 ＝⟨ Ⅰ    ⟩
   max n (max n₀⋆ n₁)                                                 ＝⟨ Ⅱ    ⟩
   max n (max n₀⋆ n₁⋆)                                                ＝⟨refl⟩
   max-boolean-question⋆ (encode (D.β φ n))                           ∎

max-boolean-questionᵀ-agreement : ⟦ max-boolean-questionᵀ ⟧₀
                                   ≡ max-boolean-question⋆
max-boolean-questionᵀ-agreement {d₁} {d₂} d≡ =
 d≡ (λ _ → refl) f≡
  where
   f₁ : (ℕ → ℕ) → ℕ → ℕ
   f₁ g n = ⟦ maxᵀ ⟧₀ n (⟦ maxᵀ ⟧₀ (g 0) (g 1))

   f₂ : (ℕ → ℕ) → ℕ → ℕ
   f₂ g n = max n (max (g 0) (g 1))

   f≡ : f₁ ≡ f₂
   f≡ g≡ n≡ = ⟦maxᵀ⟧≡max n≡ (⟦maxᵀ⟧≡max (g≡ refl) (g≡ refl))

\end{code}

The following is an analogue of `main-lemma` from the `InternalModCont` module.

\begin{code}

main-lemma : (t : 〈〉 ⊢ baire ⇒ ι)
           → ⟦ max-boolean-questionᵀ · ⌜dialogue-tree⌝ t ⟧₀
             ＝ max-boolean-question (prune (dialogue-tree t))
main-lemma t =
 ⟦ max-boolean-questionᵀ · ⌜dialogue-tree⌝ t ⟧₀             ＝⟨refl⟩
 ⟦ max-boolean-questionᵀ ⟧₀ ⟦ ⌜dialogue-tree⌝ t ⟧₀          ＝⟨ Ⅰ    ⟩
 max-boolean-question⋆ ⟦ ⌜dialogue-tree⌝ t ⟧₀               ＝⟨ Ⅱ    ⟩
 max-boolean-question⋆ (church-encode (dialogue-tree t ))   ＝⟨ Ⅲ    ⟩
 max-boolean-question (prune (dialogue-tree t))             ∎
  where
   † : Rnorm (B⟦ t ⟧₀ generic) (⌜ t ⌝ · ⌜generic⌝)
   † = Rnorm-lemma₀ t generic ⌜generic⌝ Rnorm-generic

   γ : (f : ℕ → ℕ) (g : ℕ → ℕ)
     → ({m n : ℕ} → m ＝ n → f m ＝ g n)
     → {m n : ℕ} → m ＝ n → max m (max (f 0) (f 1)) ＝ max n (max (g 0) (g 1))
   γ f g φ {m} {n} p = max m (max (f 0) (f 1)) ＝⟨ Ⅰ ⟩
                         max n (max (f 0) (f 1)) ＝⟨ Ⅱ ⟩
                         max n (max (g 0) (f 1)) ＝⟨ Ⅲ ⟩
                         max n (max (g 0) (g 1)) ∎
                          where
                           Ⅰ = ap (λ - → max - (max (f 0) (f 1))) p
                           Ⅱ = ap (λ - → max n (max - (f 1))) (φ refl)
                           Ⅲ = ap (λ - → max n (max (g 0) -)) (φ refl)

   Ⅰ = max-boolean-questionᵀ-agreement (≡-refl₀ (⌜dialogue-tree⌝ t))
   Ⅱ = † (λ _ → refl) (λ {f} {g} → γ f g)
   Ⅲ = max-boolean-question⋆-agreement (dialogue-tree t) ⁻¹

\end{code}

We know by `dialogue-UC` that the function encoded by a dialogue tree is
uniformly continuous. We denote by `mod-of` the operation of taking the modulus
of uniform continuity of such a computation encoded by a dialogue tree. It
assumes that the dialogue tree in consideration is binary, and accordingly,
first prunes the tree.

\begin{code}

mod-of : B ℕ → BT ℕ
mod-of d = pr₁ (dialogue-UC (prune d))

\end{code}

We also prove a lemma showing that `max-boolean-question ∘ prune` is the same
thing as `maximumᵤ ∘ mod-of`.

\begin{code}

max-boolean-question-is-maximum-mod-of : (d : B ℕ)
                                        → max-boolean-question (prune d)
                                          ＝ maximumᵤ (mod-of d)
max-boolean-question-is-maximum-mod-of (D.η n)   = refl
max-boolean-question-is-maximum-mod-of (D.β φ n) =
 max-boolean-question (prune (D.β φ n))                            ＝⟨refl⟩
 max-boolean-question (D.β (λ j → prune (φ (embedding-𝟚-ℕ j))) n)  ＝⟨refl⟩
 max n (max n₀ n₁)                                                 ＝⟨ Ⅰ    ⟩
 max n (max (maximumᵤ (mod-of (φ 0))) n₁)                          ＝⟨ Ⅱ    ⟩
 max n (max (maximumᵤ (mod-of (φ 0))) (maximumᵤ (mod-of (φ 1))))   ＝⟨refl⟩
 maximumᵤ (mod-of (D.β φ n))                                       ∎
  where
   Ⅰ   = ap
          (λ - → max n (max - (max-boolean-question (prune (φ 1)))))
          (max-boolean-question-is-maximum-mod-of (φ 0))
   Ⅱ   = ap
          (max n ∘ max (maximumᵤ (mod-of (φ 0))))
          (max-boolean-question-is-maximum-mod-of (φ 1))

   n₀  = max-boolean-question (prune (φ 0))
   n₁  = max-boolean-question (prune (φ 1))

\end{code}

We now proceed to define the analogue of `modulus` from `InternalModCont`,
following the same notational conventions.

\begin{code}

modulusᵤ : C ℕ → ℕ
modulusᵤ = succ ∘ max-boolean-question

\end{code}

The internalized version of `modulusᵤ` is denoted by `modulusᵤᵀ`.

\begin{code}

modulusᵤᵀ : {Γ : Cxt} →  Γ ⊢ baire ⇒ ι → B-context【 Γ 】 ι ⊢ ι
modulusᵤᵀ t = Succ' · (max-boolean-questionᵀ · ⌜dialogue-tree⌝ t)

\end{code}

We also need to write down the completely obvious fact that a function
`f : Baire → ℕ` agrees with the restriction of `f` to Cantor, when considering
Boolean points.

\begin{code}

agreement-with-restriction : (f : Baire → ℕ) (α : Baire)
                           → (bv : is-boolean-point α)
                           → f α ＝ C-restriction f (to-cantor (α , bv))
agreement-with-restriction f α bv =
 f α                                   ＝⟨refl⟩
 f′ (α , bv)                           ＝⟨ †    ⟩
 f′ (to-cantor₀ (to-cantor (α , bv)))  ＝⟨refl⟩
 f₀ (to-cantor (α , bv))               ∎
  where
   f₀ : Cantor → ℕ
   f₀ = C-restriction f

   f′ : Cantor₀ → ℕ
   f′ = f ∘ pr₁

   † = ap f′ (to-cantor₀-cancels-to-cantor (α , bv) ⁻¹)

\end{code}

Refactored and simplified on 2025-02-12.

Finally, we state and prove our main result:

  given any Boolean `t : baire ⇒ ι`, and given any two Boolean points `αᵀ, βᵀ :
  baire`, if `⟦ αᵀ ⟧` is equal to `⟦ βᵀ ⟧` up to `modulusᵤᵀ t`, then `⟦ t · αᵀ
  ⟧` is equal to `⟦ t · βᵀ ⟧`.

\begin{code}

internal-uni-mod-correct₀ : (t : 〈〉 ⊢ baire ⇒ ι) (α β : ℕ → ℕ)
                          → is-boolean-point α
                          → is-boolean-point β
                          → α ＝⦅ ⟦ modulusᵤᵀ t ⟧₀ ⦆ β
                          → ⟦ t ⟧₀ α ＝ ⟦ t ⟧₀ β
internal-uni-mod-correct₀ t α β ψ₁ ψ₂ φ =
 f α ＝⟨ Ⅰ ⟩ f₀ (to-cantor α₀) ＝⟨ Ⅱ ⟩ f₀ (to-cantor β₀) ＝⟨ Ⅲ ⟩ f β ∎
  where
   f : Baire → ℕ
   f = ⟦ t ⟧₀

   α₀ : Cantor₀
   α₀ = α , ψ₁

   β₀ : Cantor₀
   β₀ = β , ψ₂

   f₀ : Cantor → ℕ
   f₀ = C-restriction f

   ε : eloquent f
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

   ξ : ⟦ max-boolean-questionᵀ · ⌜dialogue-tree⌝ t ⟧₀ ＝ maximumᵤ bt
   ξ = ⟦ max-boolean-questionᵀ · ⌜dialogue-tree⌝ t ⟧₀   ＝⟨ Ⅰ ⟩
       max-boolean-question (prune (dialogue-tree t))   ＝⟨ Ⅱ ⟩
       maximumᵤ bt                                      ∎
        where
         Ⅰ = main-lemma t
         Ⅱ = max-boolean-question-is-maximum-mod-of (dialogue-tree t)

   q : ⟦ modulusᵤᵀ t ⟧₀ ＝ succ (maximumᵤ bt)
   q = ap succ ξ

   ψ : α ＝⦅ succ (maximumᵤ bt) ⦆ β
   ψ = transport (λ - → α ＝⦅ - ⦆ β) q φ

   ρ : α ＝⦅ succ (maximum (sequentialize bt)) ⦆ β
   ρ = transport
        (λ - → α ＝⦅ - ⦆ β)
        (ap succ (maximumᵤ′-equivalent-to-maximumᵤ bt))
        ψ

   η : α ＝⟪ sequentialize bt ⟫ β
   η = ＝⦅⦆-implies-＝⟪⟫ α β (sequentialize bt) ρ

   ζ : α ＝⟪ sequentialize bt ⟫₀ β
   ζ = ＝⟪⟫-implies-＝⟪⟫₀ α β (sequentialize bt) η

   δ : α ＝⟦ bt ⟧ β
   δ = ＝⟪⟫₀-implies-＝⟦⟧ α β bt ζ

   γ : to-cantor α₀ ＝⟦ bt ⟧ to-cantor β₀
   γ = to-cantor-＝⟦⟧ ψ₁ ψ₂ bt δ

   Ⅱ = pr₂ c (to-cantor α₀) (to-cantor β₀) γ

   Ⅰ = agreement-with-restriction f α ψ₁
   Ⅲ = agreement-with-restriction f β ψ₂ ⁻¹

internal-uni-mod-correct : (t : 〈〉 ⊢ baire ⇒ ι) (αᵀ βᵀ : 〈〉 ⊢ baire)
                         → is-boolean-pointᵀ αᵀ
                         → is-boolean-pointᵀ βᵀ
                         → ⟦ αᵀ ⟧₀ ＝⦅ ⟦ modulusᵤᵀ t ⟧₀ ⦆ ⟦ βᵀ ⟧₀
                         → ⟦ t · αᵀ ⟧₀ ＝ ⟦ t · βᵀ ⟧₀
internal-uni-mod-correct t αᵀ βᵀ ψ₁ ψ₂ φ =
 internal-uni-mod-correct₀
  t
  ⟦ αᵀ ⟧₀
  ⟦ βᵀ ⟧₀
  (boolean-valuedᵀ-lemma αᵀ ψ₁)
  (boolean-valuedᵀ-lemma βᵀ ψ₂)
  φ

\end{code}

Added on 2025-02-11.

\begin{code}

_is-a-modulus-of-uniform-continuity-for_ : ℕ → ((ℕ → 𝟚) → ℕ) → 𝓤₀ ̇
m is-a-modulus-of-uniform-continuity-for f =
 (α β : ℕ → 𝟚) → α ＝⦅ m ⦆ β → f α ＝ f β

\end{code}
