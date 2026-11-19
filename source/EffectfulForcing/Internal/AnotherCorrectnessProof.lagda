Chuangjie Xu, April 2026

Updated in November 2026

This module gives a more direct proof that dialogue trees
extracted from type-2 System T functionals are themselves
definable in System T.

The proof uses a logical relation between the standard
interpretation of System T and its Church-encoded
dialogue-tree interpretation, together with an explicit
encoding relation between Church values and inductive
dialogue trees.

This proof was originally developed as an instance of the
author's parametrized syntactic translation of System T.
That more general framework isolates the essential
ingredients of the argument and leads naturally to a logical
relation designed to be preserved under Kleisli extension.
This preservation property is the crucial step in the
fundamental lemma on which the correctness result rests.

The parametrized translation framework was introduced in the
following paper:

  Chuangjie Xu. A Gentzen-Style Monadic Translation of Gödel’s
  System T. In 5th International Conference on Formal
  Structures for Computation and Deduction (FSCD 2020).
  Leibniz International Proceedings in Informatics (LIPIcs),
  Volume 167, pp. 25:1-25:17, Schloss Dagstuhl –
  Leibniz-Zentrum für Informatik (2020)
  https://doi.org/10.4230/LIPIcs.FSCD.2020.25

\begin{code}

{-# OPTIONS --without-K --safe #-}

module EffectfulForcing.Internal.AnotherCorrectnessProof where

open import MLTT.Spartan hiding (rec)

open import EffectfulForcing.MFPSAndVariations.Church
 using (church-encode)
open import EffectfulForcing.MFPSAndVariations.Combinators
 using (rec)
open import EffectfulForcing.MFPSAndVariations.Dialogue
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Internal
open import EffectfulForcing.Internal.ExtensionalEquality

\end{code}

We fix the type of dialogue trees to be `D ℕ ℕ ℕ`, using them
to represent type-2 functions. We also fix the result type of
the Church encoding to be the System T type `(ι ⇒ ι) ⇒ ι` of
type-2 functionals.

\begin{code}

Type-2 : 𝓤₀ ̇
Type-2 = (ℕ → ℕ) → ℕ

type-2 : type
type-2 = (ι ⇒ ι) ⇒ ι

𝒟 : 𝓤₀ ̇
𝒟 = D ℕ ℕ ℕ

⌜𝒟⌝ : type
⌜𝒟⌝ = ⌜D⋆⌝ ι ι ι type-2

⟨_⟩ᴰ : type → type
⟨ ρ ⟩ᴰ = B-type〖 ρ 〗 type-2

⟪_⟫ᴰ : Cxt → Cxt
⟪ Γ ⟫ᴰ = B-context【 Γ 】 type-2

\end{code}

Evaluation of Church-encoded dialogue trees.

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

The encoding relation between Church values and dialogue trees.

The type `〖 ⌜𝒟⌝ 〗` contains arbitrary functions of the leaf and query
interpretations. Having this type alone does not ensure that a value
represents an inductive dialogue tree. We therefore define an encoding
relation that identifies values built from the Church constructors
according to the structure of such a tree.

\begin{code}

data _encodes_ : 〖 ⌜𝒟⌝ 〗 → 𝒟 → 𝓤₀ ̇ where
 enc-η : (n : ℕ)
       → (⟦ ⌜η⌝ ⟧₀ n) encodes (η n)
 enc-β : {g : ℕ → 〖 ⌜𝒟⌝ 〗} {φ : ℕ → 𝒟}
       → ((j : ℕ) → (g j) encodes (φ j))
       → (i : ℕ)
       → (⟦ ⌜β⌝ ⟧₀ g i) encodes (β φ i)

\end{code}

The followings justify the encoding relation: every encoded value is
hereditarily extensionally equal to the canonical encoding of its tree,
and every tree is encoded by its canonical encoding.

\begin{code}

encodes→≡ : (t : 〖 ⌜𝒟⌝ 〗) (d : 𝒟)
          → t encodes d
          → t ≡[ ⌜𝒟⌝ ] (church-encode d)
encodes→≡ _ _ (enc-η n) p _ = p refl
encodes→≡ _ _ (enc-β {g} {φ} enc i) {a} {a'} p {b} {b'} q = q claim refl
 where
  claim : {j k : ℕ} → j ≡ k
        → (g j a b) ≡[ type-2 ] (church-encode (φ k) a' b')
  claim {j} refl = encodes→≡ (g j) (φ j) (enc j) p q

canonical-encodes : (d : 𝒟) → (church-encode d) encodes d
canonical-encodes (η n)   = enc-η n
canonical-encodes (β φ i) = enc-β (λ j → canonical-encodes (φ j)) i

\end{code}

`⌜kleisli-extension⌝` preserves the encoding relation.

\begin{code}

enc-κ : {g : ℕ → 〖 ⌜𝒟⌝ 〗} {f : ℕ → 𝒟} {t : 〖 ⌜𝒟⌝ 〗} {d : 𝒟}
      → ((i : ℕ) → (g i) encodes (f i))
      → t encodes d
      → (⟦ ⌜kleisli-extension⌝ ⟧₀ g t) encodes (kleisli-extension f d)
enc-κ p (enc-η n) = p n
enc-κ p (enc-β q i) = enc-β (λ j → enc-κ p (q j)) i

\end{code}

Evaluating a Church value with `leaf` and `branch` gives the same result
as evaluating its encoded tree. Consequently, two trees encoded by the
same Church value agree at every oracle.

\begin{code}

encodes-eval
 : {t : 〖 ⌜𝒟⌝ 〗} {d : 𝒟}
 → t encodes d
 → (α : ℕ → ℕ) → t leaf branch α ≡ dialogue d α
encodes-eval (enc-η n)   α = refl
encodes-eval (enc-β p i) α = encodes-eval (p (α i)) α

encodes-eval-agree
 : {t : 〖 ⌜𝒟⌝ 〗} {d d' : 𝒟}
 → t encodes d
 → t encodes d'
 → (α : ℕ → ℕ) → dialogue d α ≡ dialogue d' α
encodes-eval-agree enc enc' α
 = (encodes-eval enc α)⁻¹ ∙ (encodes-eval enc' α)

\end{code}

Logical relation.

For a fixed oracle α, the base relation Rι relates n to t by
exhibiting a dialogue tree that t encodes and whose evaluation
at α is n.

\begin{code}

Rι : (ℕ → ℕ) → 〖 ι 〗 → 〖 ⌜𝒟⌝ 〗 → 𝓤₀ ̇
Rι α n t =  Σ d ꞉ 𝒟 , (t encodes d) × (n ＝ dialogue d α)

R : (ℕ → ℕ) → {ρ : type} → 〖 ρ 〗 → 〖 ⟨ ρ ⟩ᴰ 〗 → 𝓤₀ ̇
R α {ι} = Rι α
R α {σ ⇒ τ} f g = ∀ x y → R α x y → R α (f x) (g y)

Rˣ : (ℕ → ℕ) → {Γ : Cxt} → 【 Γ 】 → 【 ⟪ Γ ⟫ᴰ 】 → 𝓤₀ ̇
Rˣ α {Γ} γ δ = ∀ {ρ} (i : ∈Cxt ρ Γ) → R α (γ i) (δ (∈Cxt-B-type i))

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
Rη α γ n = η n , enc-η n , refl

Rκ : (α : ℕ → ℕ)
   → {Γ : Cxt} (γ : 【 Γ 】)
   → (f : 〖 ι ⇒ ι 〗) (g : 〖 ι ⇒ ⌜𝒟⌝ 〗)
   → (∀ i → Rι α (f i) (g i))
   → (n : 〖 ι 〗) (t : 〖 ⌜𝒟⌝ 〗)
   → Rι α n t
   → Rι α (f n) (⟦ ⌜kleisli-extension⌝ ⟧ γ g t)
Rκ α γ f g ζ n t (d , enc , refl)
 = kleisli-extension ζ₀ d
 , enc-κ ζ₁ enc 
 , (ζ₂ n ∙ decode-kleisli-extension ζ₀ d α)
 where
  ζ₀ = λ i → pr₁ (ζ i)
  ζ₁ = λ i → pr₁ (pr₂ (ζ i))
  ζ₂ = λ i → pr₂ (pr₂ (ζ i))

R[KE] : (α : ℕ → ℕ)
      → {ρ : type} {Γ : Cxt} (γ : 【 Γ 】)
      → (f : 〖 ι ⇒ ρ 〗) (g : 〖 ι ⇒ ⟨ ρ ⟩ᴰ 〗)
      → (∀ i → R α (f i) (g i))
      → R α f (⟦ ⌜Kleisli-extension⌝ ⟧ γ g)
R[KE] α {ι} {_} γ f g ζ x y χ = Rκ α γ f g ζ x y χ
R[KE] α {σ ⇒ τ} γ f g ζ x y χ u v θ =
 R[KE] α _ (λ z → f z u) (λ z → g z v) (λ i → ζ i u v θ) x y χ

RΩ : (α : ℕ → ℕ)
   → (n : ℕ) (t : 〖 ⌜𝒟⌝ 〗) → Rι α n t → Rι α (α n) (⟦ ⌜generic⌝ ⟧₀ t)
RΩ α = Rκ α ⟨⟩ α (⟦ ⌜β⌝ · ⌜η⌝ ⟧₀) (λ i → β η i , enc-β enc-η i , refl)

\end{code}

Fundamental theorem of the logical relation.

We now prove that every System T term is related to its
Church-encoded translation in related environments.

\begin{code}

FundamentalLemma : (α : ℕ → ℕ)
                 → {Γ : Cxt} {ρ : type} (t : T Γ ρ)
                 → (γ : 【 Γ 】) (δ : 【 ⟪ Γ ⟫ᴰ 】) → Rˣ α γ δ
                 → R α (⟦ t ⟧ γ) (⟦ ⌜ t ⌝ ⟧ δ)
FundamentalLemma α Zero γ δ ξ = Rη α γ zero
FundamentalLemma α (Succ t) γ δ ξ
 = Rκ α γ succ (λ i → ⟦ ⌜η⌝ ⟧ (δ ‚ i) (succ i))
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
  goal = R[KE] α _ (rec (⟦ f ⟧ γ) (⟦ g ⟧ γ))
                   (rec (⟦ comp · ⌜ f ⌝ · ⌜η⌝ ⟧ δ) (⟦ ⌜ g ⌝ ⟧ δ))
                   claim
                   (⟦ t ⟧ γ)
                   (⟦ ⌜ t ⌝ ⟧ δ)
                   (FundamentalLemma α t γ δ ξ)
FundamentalLemma α (ν i) γ δ ξ = ξ i
FundamentalLemma α (ƛ t) γ δ ξ x y θ
 = FundamentalLemma α t (γ ‚ x) (δ ‚ y) ξ,,θ
 where
  ξ,,θ : Rˣ α (γ ‚ x) (δ ‚ y)
  ξ,,θ (∈Cxt0 _) = θ
  ξ,,θ (∈CxtS _ i) = ξ i
FundamentalLemma α (t · u) γ δ ξ
 = FundamentalLemma α t γ δ ξ
    (⟦ u ⟧ γ) (⟦ ⌜ u ⌝ ⟧ δ) (FundamentalLemma α u γ δ ξ)

\end{code}

Correctness theorem.

The fundamental theorem implies that for each closed term t of
type `(ι ⇒ ι) ⇒ ι`, ⟦ ⌜dialogue-tree⌝ t ⟧₀ encodes a dialogue
tree whose evaluation agrees with ⟦ t ⟧₀ at every oracle.

\begin{code}

⌜dialogue-tree⌝-correct
 : (t : T₀ ((ι ⇒ ι) ⇒ ι))
 → Σ d ꞉ 𝒟 , (⟦ ⌜dialogue-tree⌝ t ⟧₀ encodes d)
           × ((α : ℕ → ℕ) → ⟦ t ⟧₀ α ＝ dialogue d α)
⌜dialogue-tree⌝-correct t = d , enc , val
 where
  cor : (α : ℕ → ℕ) → Rι α (⟦ t ⟧₀ α) (⟦ ⌜ t ⌝ · ⌜generic⌝ ⟧₀)
  cor α = FundamentalLemma α t ⟨⟩ ⟨⟩ ∈Cxt-〈〉-elim α ⟦ ⌜generic⌝ ⟧₀ (RΩ α)
  d : 𝒟
  d = pr₁ (cor (λ _ → 0))
  enc : ⟦ ⌜dialogue-tree⌝ t ⟧₀ encodes d
  enc = pr₁ (pr₂ (cor (λ _ → 0)))
  val : (α : ℕ → ℕ) → ⟦ t ⟧₀ α ＝ dialogue d α
  val α using (_ , enc' , val') ← cor α = val' ∙ encodes-eval-agree enc' enc α

\end{code}

Evaluating the extracted Church-encoded tree in System T
recovers the functional denoted by the original term.

\begin{code}

⌜dialogue⌝-⌜dialogue-tree⌝-correct
 : (t : T₀ ((ι ⇒ ι) ⇒ ι))
 → (α : ℕ → ℕ)
 → ⟦ t ⟧₀ α ＝ ⟦ ⌜dialogue⌝ · ⌜dialogue-tree⌝ t ⟧₀ α
⌜dialogue⌝-⌜dialogue-tree⌝-correct t α
 using (d , enc , val) ← ⌜dialogue-tree⌝-correct t
 = val α ∙ (encodes-eval enc α)⁻¹

\end{code}
