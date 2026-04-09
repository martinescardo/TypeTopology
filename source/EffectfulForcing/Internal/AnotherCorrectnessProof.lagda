Chuangjie Xu, April 2026

This module gives a more direct proof that dialogue trees
extracted from type-2 System T functionals are themselves
definable in System T.

The proof uses a logical relation between the standard
interpretation of System T and its Church-encoded
dialogue-tree interpretation, together with an explicit
representation relation between Church values and inductive
dialogue trees.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module EffectfulForcing.Internal.AnotherCorrectnessProof where

open import MLTT.Spartan hiding (rec)

open import EffectfulForcing.MFPSAndVariations.Combinators
   using (rec)
open import EffectfulForcing.MFPSAndVariations.SystemT
   using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Internal
   using (⌜D⋆⌝ ; ⌜η⌝ ; ⌜β⌝ ; ⌜kleisli-extension⌝ ; ⌜generic⌝ ;
          B-type〖_〗 ; B-context【_】 ; ∈Cxt-B-type ;
          ⌜Kleisli-extension⌝ ; ⌜_⌝ ; ⌜dialogue-tree⌝)
open import EffectfulForcing.MFPSAndVariations.Dialogue
   using (D ; η ; β ; dialogue ; generic ; kleisli-extension)

\end{code}

We fix the type of dialogue trees to be `D ℕ ℕ ℕ`, using them
to represent type-2 functions. We also fix the result type of
the Church encoding to be the System T type `(ι ⇒ ι) ⇒ ι` of
type-2 functionals.

\begin{code}

Type-2 : Type
Type-2 = (ℕ → ℕ) → ℕ

type-2 : type
type-2 = (ι ⇒ ι) ⇒ ι

𝒟 : Type
𝒟 = D ℕ ℕ ℕ

⌜𝒟⌝ : type
⌜𝒟⌝ = ⌜D⋆⌝ ι ι ι type-2

⟨_⟩ᴰ : type → type
⟨ ρ ⟩ᴰ = B-type〖 ρ 〗 type-2

⟪_⟫ᴰ : Cxt → Cxt
⟪ Γ ⟫ᴰ = B-context【 Γ 】 type-2

\end{code}

Evaluation of Church-encoded dialogue trees

Recall that the dialogue function is defined as follows:

  dialogue : D X Y Z → (X → Y) → Z
  dialogue (η z)   α = z
  dialogue (β φ x) α = dialogue (φ(α x)) α

We define corresponding leaf and branching algebras in System T,
thereby internalizing the dialogue function itself.

\begin{code}

⌜leaf⌝ : {Γ : Cxt}
   → T Γ (ι ⇒ type-2)
⌜leaf⌝ = ƛ (ƛ ν₁)

leaf : ℕ → Type-2
leaf = λ n α → n

⌜branch⌝ : {Γ : Cxt}
   → T Γ ((ι ⇒ type-2) ⇒ ι ⇒ type-2)
⌜branch⌝ = ƛ (ƛ (ƛ (ν₂ · (ν₀ · ν₁) · ν₀)))

branch : (ℕ → Type-2) → ℕ → Type-2
branch = λ g i α → g (α i) α

⌜dialogue⌝ : {Γ : Cxt}
   → T Γ (⌜𝒟⌝ ⇒ (ι ⇒ ι) ⇒ ι)
⌜dialogue⌝ = ƛ (ν₀ · ⌜leaf⌝ · ⌜branch⌝)

\end{code}

Representable Church values

The semantic type `〖 ⌜𝒟⌝ 〗` is a higher-order function space,
so its elements need not satisfy the fold laws of genuine
dialogue trees. Accordingly, we restrict attention to those
Church values that are represented by genuine inductive
dialogue trees.

To do this, we define `run`, which interprets an inductive
dialogue tree using the standard branching algebra, but with
an arbitrary choice of leaf algebra `e`. We then say that a
dialogue tree `d` represents a Church value `t` when both
yield the same result for every choice of leaf algebra `e`
and oracle `α`.

The main technical reason for using `run` rather than the
ordinary `dialogue` function is that the proof that
`⌜kleisli-extension⌝` preserves the logical relation needs
arbitrary leaf algebras. The function `dialogue` fixes the
leaf algebra to `leaf`, but in the logical-relation argument
we must vary the leaf algebra while keeping the branching
algebra fixed. The definition of `run` is tailored to exactly
this argument.

\begin{code}

run : 𝒟 → (ℕ → Type-2) → Type-2
run (η n) e α = e n α
run (β g i) e α = run (g (α i)) e α

_represents_ : 𝒟 → 〖 ⌜𝒟⌝ 〗 → Type
d represents t = ∀ (e : ℕ → Type-2) (α : ℕ → ℕ) → t e branch α ＝ run d e α

\end{code}

The first lemma shows that `run` agrees with the usual
`dialogue` function when the leaf algebra is `leaf`. From this
we obtain correctness of `⌜dialogue⌝` on represented Church
values.

\begin{code}

run-dialogue : (d : 𝒟) (α : ℕ → ℕ) → run d leaf α ＝ dialogue d α
run-dialogue (η _) α = refl
run-dialogue (β g i) α = run-dialogue (g (α i)) α

⌜dialogue⌝-correct : {Γ : Cxt} (γ : 【 Γ 】)
   → (d : 𝒟) (t : 〖 ⌜𝒟⌝ 〗) → d represents t
   → ∀ (α : ℕ → ℕ) → ⟦ ⌜dialogue⌝ ⟧ γ t α ＝ dialogue d α
⌜dialogue⌝-correct _ d _ r α = r leaf α ∙ run-dialogue d α

\end{code}

Compatibility with `⌜kleisli-extension⌝`

To prove preservation of representation under
`⌜kleisli-extension⌝`, we use two auxiliary lemmas. The first,
`run-ext`, says that changing the leaf algebra pointwise does
not affect the result of `run`. The second, `run-κ`, states
that the inductive operation `kleisli-extension` is
interpreted by composing `run` with the continuation.
Together they show that representation is preserved by
`⌜kleisli-extension⌝`.

\begin{code}

run-ext : (d : 𝒟) {e₀ e₁ : ℕ → Type-2}
   → (∀ n α → e₀ n α ＝ e₁ n α)
   → ∀ α → run d e₀ α ＝ run d e₁ α
run-ext (η n)   ξ α = ξ n α
run-ext (β g i) ξ α = run-ext (g (α i)) ξ α

run-κ : (h : ℕ → 𝒟) (t : 𝒟) (e : ℕ → Type-2) (α : ℕ → ℕ)
   → run (kleisli-extension h t) e α ＝ run t (λ n → run (h n) e) α
run-κ h (η n)   e α = refl
run-κ h (β g i) e α = run-κ h (g (α i)) e α

⌜kleisli-extension⌝-preserves-representation : {Γ : Cxt} (γ : 【 Γ 】)
   → (g : ℕ → 𝒟) (h : ℕ → 〖 ⌜𝒟⌝ 〗)
   → (∀ i → g i represents (h i))
   → (d : 𝒟) (t : 〖 ⌜𝒟⌝ 〗) → d represents t
   → kleisli-extension g d represents ⟦ ⌜kleisli-extension⌝ ⟧ γ h t
⌜kleisli-extension⌝-preserves-representation _ g h ζ d t r e α = goal
 where
  claim₀ : t (λ n → h n e branch) branch α ＝ run d (λ n → h n e branch) α
  claim₀ = r (λ n → h n e branch) α
  claim₁ : run d (λ n → h n e branch) α ＝ run d (λ n → run (g n) e) α
  claim₁ = run-ext d (λ n β → ζ n e β) α
  claim₂ : run d (λ n → run (g n) e) α ＝ run (kleisli-extension g d) e α
  claim₂ = (run-κ g d e α) ⁻¹
  goal : t (λ n → h n e branch) branch α ＝ run (kleisli-extension g d) e α
  goal = claim₀ ∙ claim₁ ∙ claim₂

\end{code}

Logical relation

The base relation `Rι` says that a natural number `n` is related
to a Church value `t` when `t` is represented by an inductive
dialogue tree that evaluates to `n` at the oracle `α`.

\begin{code}

Rι : (ℕ → ℕ) → 〖 ι 〗 → 〖 ⌜𝒟⌝ 〗 → Type
Rι α n t =  Σ d ꞉ 𝒟 , (d represents t) × (n ＝ dialogue d α)

R : (ℕ → ℕ) → {ρ : type} → 〖 ρ 〗 → 〖 ⟨ ρ ⟩ᴰ 〗 → Type
R α {ι} = Rι α
R α {σ ⇒ τ} f g = ∀ x y → R α x y → R α (f x) (g y)

Rˣ : (ℕ → ℕ) → {Γ : Cxt} → 【 Γ 】 → 【 ⟪ Γ ⟫ᴰ 】 → Type
Rˣ α {Γ} γ δ = ∀{ρ}(i : ∈Cxt ρ Γ) → R α (γ i) (δ (∈Cxt-B-type i))

\end{code}

The logical relation is preserved by `⌜η⌝`,
`⌜kleisli-extension⌝`, and `⌜generic⌝`.

The key base-type preservation step is `Rκ`. The auxiliary
lemma `R[KE]` then lifts it to the hereditary logical relation
at all types.

\begin{code}

Rη : (α : ℕ → ℕ)
   → {Γ : Cxt} (γ : 【 Γ 】) (n : 〖 ι 〗)
   → Rι α n (⟦ ⌜η⌝ ⟧ γ n)
Rη _ _ n = η n , (λ _ _ → refl) , refl

dialogue-κ : (h : ℕ → 𝒟) (t : 𝒟) (α : ℕ → ℕ)
           → dialogue (kleisli-extension h t) α ＝ dialogue (h (dialogue t α)) α
dialogue-κ h (η n) α = refl
dialogue-κ h (β g i) α = dialogue-κ h (g (α i)) α

Rκ : (α : ℕ → ℕ)
   → {Γ : Cxt} (γ : 【 Γ 】)
   → (f : 〖 ι ⇒ ι 〗) (g : 〖 ι ⇒ ⌜𝒟⌝ 〗)
   → (∀ i → Rι α (f i) (g i))
   → ∀ (n : 〖 ι 〗) (t : 〖 ⌜𝒟⌝ 〗)
   → Rι α n t
   → Rι α (f n) (⟦ ⌜kleisli-extension⌝ ⟧ γ g t)
Rκ α γ f g ζ n t (d , r , refl) = kleisli-extension h d , rep , value
 where
  h : ℕ → 𝒟
  h i = pr₁ (ζ i)
  ζ' : ∀ i → (h i) represents (g i)
  ζ' i = pr₁ (pr₂ (ζ i))
  rep : kleisli-extension h d represents ⟦ ⌜kleisli-extension⌝ ⟧ γ g t
  rep = ⌜kleisli-extension⌝-preserves-representation γ h g ζ' d t r
  base : f (dialogue d α) ＝ dialogue (h (dialogue d α)) α
  base = pr₂ (pr₂ (ζ (dialogue d α)))
  step : dialogue (kleisli-extension h d) α ＝ dialogue (h (dialogue d α)) α
  step = dialogue-κ h d α
  value : f (dialogue d α) ＝ dialogue (kleisli-extension h d) α
  value = base ∙ step ⁻¹

R[KE] : (α : ℕ → ℕ)
   → {ρ : type} {Γ : Cxt} (γ : 【 Γ 】)
   → (f : 〖 ι ⇒ ρ 〗) (g : 〖 ι ⇒ ⟨ ρ ⟩ᴰ 〗)
   → (∀ i → R α (f i) (g i))
   → R α f (⟦ ⌜Kleisli-extension⌝ ⟧ γ g)
R[KE] α {ι} {_} γ f g ζ x y χ = Rκ α γ f g ζ x y χ
R[KE] α {σ ⇒ τ} γ f g ζ x y χ u v θ =
   R[KE] α _ (λ z → f z u) (λ z → g z v) (λ i → ζ i u v θ) x y χ

RΩ : (α : ℕ → ℕ)
   → ∀ n t → Rι α n t → Rι α (α n) (⟦ ⌜generic⌝ ⟧₀ t)
RΩ α n t (d , r , refl) = generic d , rep , value
 where
  rep : (generic d) represents (⟦ ⌜generic⌝ ⟧₀ t)
  rep = ⌜kleisli-extension⌝-preserves-representation ⟨⟩
               (β η) (⟦ ⌜β⌝ · ⌜η⌝ ⟧₀) (λ _ _ _ → refl) d t r
  value : α (dialogue d α) ＝ dialogue (generic d) α
  value = (dialogue-κ (β η) d α) ⁻¹

\end{code}

Fundamental theorem of the logical relation

We now prove that every System T term is related to its
Church-encoded translation.

\begin{code}

FundamentalLemma : (α : ℕ → ℕ)
   → {Γ : Cxt} {ρ : type} (t : T Γ ρ)
   → (γ : 【 Γ 】) (δ : 【 ⟪ Γ ⟫ᴰ 】) → Rˣ α γ δ
   → R α (⟦ t ⟧ γ) (⟦ ⌜ t ⌝ ⟧ δ)
FundamentalLemma α Zero γ δ ξ = Rη α γ zero
FundamentalLemma α (Succ t) γ δ ξ =
   Rκ α γ succ
      (λ i → ⟦ ⌜η⌝ ⟧ (δ ‚ i) (succ i))
      (λ i → Rη α (δ ‚ i) (succ i))
      (⟦ t ⟧ γ) (⟦ ⌜ t ⌝ ⟧ δ)
      (FundamentalLemma α t γ δ ξ)
FundamentalLemma α (Rec f g t) γ δ ξ = goal
 where
  claim : ∀ i
        → R α (rec (⟦ f ⟧ γ) (⟦ g ⟧ γ) i)
              (rec (⟦ comp · ⌜ f ⌝ · ⌜η⌝ ⟧ δ) (⟦ ⌜ g ⌝ ⟧ δ) i)
  claim zero = FundamentalLemma α g γ δ ξ
  claim (succ i) = FundamentalLemma α f γ δ ξ i _ (Rη α γ i) _ _ (claim i)
  goal : R α (rec (⟦ f ⟧ γ) (⟦ g ⟧ γ) (⟦ t ⟧ γ))
             (⟦ ⌜Kleisli-extension⌝ ⟧ _
                (rec (⟦ comp · ⌜ f ⌝ · ⌜η⌝ ⟧ δ) (⟦ ⌜ g ⌝ ⟧ δ))
                (⟦ ⌜ t ⌝ ⟧ δ))
  goal = R[KE] α _
            (rec (⟦ f ⟧ γ) (⟦ g ⟧ γ))
            (rec (⟦ comp · ⌜ f ⌝ · ⌜η⌝ ⟧ δ) (⟦ ⌜ g ⌝ ⟧ δ))
            claim
            (⟦ t ⟧ γ) (⟦ ⌜ t ⌝ ⟧ δ)
            (FundamentalLemma α t γ δ ξ)
FundamentalLemma α (ν i) γ δ ξ = ξ i
FundamentalLemma α (ƛ t) γ δ ξ x y θ =
   FundamentalLemma α t (γ ‚ x) (δ ‚ y) ξ,,θ
 where
  ξ,,θ : Rˣ α (γ ‚ x) (δ ‚ y)
  ξ,,θ (∈Cxt0 _) = θ
  ξ,,θ (∈CxtS _ i) = ξ i
FundamentalLemma α (t · u) γ δ ξ =
   FundamentalLemma α t γ δ ξ
      (⟦ u ⟧ γ) (⟦ ⌜ u ⌝ ⟧ δ)
      (FundamentalLemma α u γ δ ξ)

\end{code}

Correctness theorem

The fundamental theorem yields a represented dialogue tree for
every closed term of type `(ι ⇒ ι) ⇒ ι`. The final theorem
compares the standard interpretation of such a term with the
evaluation of the extracted Church-encoded dialogue tree.

\begin{code}

⌜dialogue-tree⌝-correct : (t : T₀ ((ι ⇒ ι) ⇒ ι))
   → (α : ℕ → ℕ)
   → ⟦ t ⟧₀ α ＝ ⟦ ⌜dialogue⌝ · ⌜dialogue-tree⌝ t ⟧₀ α
⌜dialogue-tree⌝-correct t α = eq₀  ∙ eq₁ ⁻¹
 where
  cor : Rι α (⟦ t ⟧₀ α) (⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀)
  cor = FundamentalLemma α t ⟨⟩ ⟨⟩ (λ ()) α ⟦ ⌜generic⌝ ⟧₀ (RΩ α)
  d : 𝒟
  d = pr₁ cor
  r : d represents ⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀
  r = pr₁ (pr₂ cor)
  eq₀ : ⟦ t ⟧₀ α ＝ dialogue d α
  eq₀ = pr₂ (pr₂ cor)
  eq₁ : ⟦ ⌜dialogue⌝ ⟧₀ ⟦ ⌜dialogue-tree⌝ t ⟧₀ α ＝ dialogue d α
  eq₁ = ⌜dialogue⌝-correct ⟨⟩ d ⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀ r α

\end{code}
