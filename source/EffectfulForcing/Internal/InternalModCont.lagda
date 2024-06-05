Ayberk Tosun

Based on some previous work by Martín Escardó.

In this module, we prove the correctness of the internal modulus of continuity
operator.

\begin{code}

{-# OPTIONS --safe --without-K #-}

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
 using (eloquent; D; dialogue; eloquent-functions-are-continuous;
        dialogue-continuity; generic)
open import EffectfulForcing.MFPSAndVariations.Continuity
 using (is-continuous; _＝⟪_⟫_)
open import EffectfulForcing.MFPSAndVariations.ContinuityProperties fe
open import EffectfulForcing.Internal.Correctness
 using (Rnorm-generic; is-dialogue-for; Rnorm-lemma₀; Rnorm;
        dialogue-tree-agreement; ⌜dialogue⌝)
open import EffectfulForcing.Internal.External
 using (eloquence-theorem; dialogue-tree; ⟪⟫; B⟦_⟧; B⟦_⟧₀)
open import EffectfulForcing.Internal.Subst
open import EffectfulForcing.Internal.ExtensionalEquality
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

There is also `max-question₀` which is an alternative definition of
`max-question` that uses `dialogue-continuity`. This is used to facilitate a
proof.

\begin{code}

max-question : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question (D.η n)   α = 0
max-question (D.β φ n) α = max n (max-question (φ (α n)) α)

max-question₀ : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question₀ d α = maximum (pr₁ (dialogue-continuity d α))

max-question₀-agreement : (d : D ℕ ℕ ℕ) (α : ℕ → ℕ)
                        → max-question d α ＝ max-question₀ d α
max-question₀-agreement (D.η n)   α = refl
max-question₀-agreement (D.β φ n) α =
 ap (max n) (max-question₀-agreement (φ (α n)) α)

max-question⋆ : D⋆ ℕ ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
max-question⋆ d α = d (λ _ → 0) (λ g x → max x (g (α x)))

max-questionᵀ : {Γ : Cxt} → Γ ⊢ (⌜B⌝ ι ι) ⇒ baire ⇒ ι
max-questionᵀ = ƛ (ƛ (ν₁ · ƛ Zero · ƛ (ƛ (maxᵀ · ν₀ · (ν₁ · (ν₂ · ν₀))))))

max-question⋆-agreement : (d : D ℕ ℕ ℕ) (α : ℕ → ℕ)
                        → max-question d α ＝ max-question⋆ (church-encode d) α
max-question⋆-agreement (D.η n)   α = refl
max-question⋆-agreement (D.β φ n) α = †
 where
  IH : max-question (φ (α n)) α
     ＝ max-question⋆ (church-encode (φ (α n))) α
  IH = max-question⋆-agreement (φ (α n)) α

  † : max n (max-question (φ (α n)) α)
    ＝ church-encode (D.β φ n) (λ _ → 0) (λ g x → max x (g (α x)))
  † = ap (max n) IH

-- Re-factored to avoid using function extensionality together with Bruno Paiva.
max-questionᵀ-agreement-with-max-question⋆ : ⟦ max-questionᵀ ⟧₀ ≡ max-question⋆
max-questionᵀ-agreement-with-max-question⋆ q {α} {β} eq = q (λ _ → refl) ‡
 where
  ‡ : {f g : ℕ → ℕ}
    → (k : f ≡ g) {i j : ℕ} → i ＝ j → ⟦ maxᵀ ⟧₀ i (f (α i)) ＝ max j (g (β j))
  ‡ {f} {g} φ {i} {_} refl = transport
                              (λ - → ⟦ maxᵀ ⟧₀ i - ＝ max i (g (β i)))
                              (φ (eq refl) ⁻¹)
                              (maxᵀ-correct i (g (β i)))

\end{code}

The modulus of continuity given by a dialogue tree is the successor of the
maximum question in it. Again, we define three different versions of the modulus
of continuity operation following the same conventions.

  1. `modulus` following `max-question`,
  2. `modulus₀` following `max-question₀`, and
  3. `modulusᵀ` following `max-questionᵀ`.

\begin{code}

modulus : D ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
modulus d α = succ (max-question d α)

modulus₀ : (d : D ℕ ℕ ℕ) → (ℕ → ℕ) → ℕ
modulus₀ d α = succ (max-question₀ d α)

modulus⋆ : D⋆ ℕ ℕ ℕ ℕ → (ℕ → ℕ) → ℕ
modulus⋆ d α = succ (max-question⋆ d α)

modulusᵀ : 〈〉 ⊢ ⌜B⌝ ι ι ⇒ (ι ⇒ ι) ⇒ ι
modulusᵀ = ƛ (ƛ (Succ' · (max-questionᵀ · ν₁ · ν₀)))

\end{code}

The correctness of `modulusᵀ` is given in `internal-mod-cont-correct` below. To
prove this, we use the lemma `main-lemma`, which contains the main content of
the proof.

\begin{code}


main-lemma : (t : 〈〉 ⊢ (baire ⇒ ι)) (α : ℕ → ℕ)
           → ⟦ max-questionᵀ · (⌜dialogue-tree⌝ t) ⟧₀ α
             ＝ max-question₀ (dialogue-tree t) α
main-lemma t α =
 ⟦ max-questionᵀ · ⌜dialogue-tree⌝ t ⟧₀ α                 ＝⟨ refl ⟩
 ⟦ max-questionᵀ ⟧₀ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α              ＝⟨ Ⅰ    ⟩
 max-question⋆ (church-encode (dialogue-tree t)) α        ＝⟨ Ⅱ    ⟩
 max-question  (dialogue-tree t) α                        ＝⟨ Ⅲ    ⟩
 max-question₀ (dialogue-tree t) α                        ∎
  where
   † : Rnorm (B⟦ t ⟧₀ generic) (⌜ t ⌝ · ⌜generic⌝)
   † = Rnorm-lemma₀ t generic ⌜generic⌝ Rnorm-generic

   Ⅰ = max-questionᵀ-agreement-with-max-question⋆
        (dialogue-tree-agreement t)
        (ap α)
   Ⅱ = max-question⋆-agreement (dialogue-tree t) α ⁻¹
   Ⅲ = max-question₀-agreement (dialogue-tree t) α

internal-mod-cont-correct : (t : 〈〉 ⊢ (baire ⇒ ι)) (α β : 〈〉 ⊢ baire)
                          → ⟦ α ⟧₀ ＝⦅ ⟦ modulusᵀ · (⌜dialogue-tree⌝ t) · α ⟧₀ ⦆ ⟦ β ⟧₀
                          → ⟦ t · α ⟧₀ ＝ ⟦ t ·  β ⟧₀
internal-mod-cont-correct t α β p = †
 where
  ε : eloquent ⟦ t ⟧₀
  ε = eloquence-theorem ⟦ t ⟧₀ (t , refl)

  c : is-continuous ⟦ t ⟧₀
  c = eloquent-functions-are-continuous ⟦ t ⟧₀ ε

  c₀ : is-continuous₀ ⟦ t ⟧₀
  c₀ = continuity-implies-continuity₀ ⟦ t ⟧₀ c

  m₀ : ℕ
  m₀ = succ (max-question₀ (dialogue-tree t) ⟦ α ⟧₀)

  q : ⟦ modulusᵀ · (⌜dialogue-tree⌝ t) · α ⟧₀ ＝ m₀
  q = ap succ (main-lemma t ⟦ α ⟧₀)

  ‡ : ⟦ α ⟧₀ ＝⦅ m₀ ⦆ ⟦ β ⟧₀
  ‡ = transport (λ - → ⟦ α ⟧₀ ＝⦅ - ⦆ ⟦ β ⟧₀) q p

  † : ⟦ t ⟧₀ ⟦ α ⟧₀ ＝ ⟦ t ⟧₀ ⟦ β ⟧₀
  † = pr₂ (c₀ ⟦ α ⟧₀) ⟦ β ⟧₀ ‡

\end{code}

While I was working on the proof, I wrote down the following fact, which turned
out not to be necessary for the proof. However, I am not taking it out of this
file as it might be useful in the future.

Update: the fact has now been commented out, because it was something
non-essential that required function extensionality and I have not removed the
use of function extensionality from it yet.

\begin{code}

-- church-encode-to-D-rec : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : 𝓣  ̇}
--                      → (d : D X Y Z)
--                      → (η′ : Z → A)
--                      → (β′ : (Y → A) → X → A)
--                      → church-encode d η′ β′ ＝ D-rec η′ β′ d
-- church-encode-to-D-rec (D.η _)   η′ β′ = refl
-- church-encode-to-D-rec {Y = Y} (D.β φ x) η′ β′ = ap (λ - → β′ - x) {!!} -- (dfunext fe †)
--  where
--   † : (y : Y) → church-encode (φ y) η′ β′ ＝ D-rec η′ β′ (φ y)
--   † y = church-encode-to-D-rec (φ y) η′ β′

\end{code}
