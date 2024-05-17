--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-15
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module EffectfulForcing.Internal.Ordinals
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Ordinals.Brouwer
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

import Ordinals.NotationInterpretation0 ua pt as NotationInterpretation

open suprema pt sr

-- TODO decide where to place all of this, I suggest
-- Ordinals.BrouwerArithmetic for arithmetic operations on Brouwer codes
-- Ordinals.BrouwerOrderingProperties for the ordering properties

-- TODO remove --allow-unsolved-metas and add back --safe

\end{code}

By `⦅_⦆`, we denote the standard interpretation of ordinals.

\begin{code}

⦅_⦆ : B → Ordinal 𝓤₀
⦅ b ⦆ = NotationInterpretation.⟦_⟧₀ sr b

\end{code}

Ordinals form an ordinal themselves when ordered under the subordinal relation
`◁`.

The successor constructor `S` gives a higher ordinal.

\begin{code}

B-⊲-S : (b : B) → ⦅ b ⦆ ⊲ ⦅ S b ⦆
B-⊲-S b = (inr ⋆) , eqtoidₒ (ua 𝓤₀) fe ⦅ b ⦆ (⦅ S b ⦆ ↓ inr ⋆) goal
 where
  f : ⟨ ⦅ b ⦆ ⟩ → ⟨ ⦅ S b ⦆ ↓ inr ⋆ ⟩
  f a = inl a , ⋆

  g : ⟨ ⦅ S b ⦆ ↓ inr ⋆ ⟩ → ⟨ ⦅ b ⦆ ⟩
  g (inl a , inla<inr⋆) = a

  gf : ∀ x → g (f x) ＝ x
  gf _ = refl

  fg : ∀ x → f (g x) ＝ x
  fg (inl a , inla<inr⋆) = refl

  f-is-order-preserving : is-order-preserving ⦅ b ⦆ (⦅ S b ⦆ ↓ inr ⋆) f
  f-is-order-preserving a b a<b = a<b

  g-is-order-preserving : is-order-preserving (⦅ S b ⦆ ↓ inr ⋆) ⦅ b ⦆ g
  g-is-order-preserving (inl a , inla<inr⋆) (inl b , inlb<inr⋆) a<b = a<b

  goal : ⦅ b ⦆ ≃ₒ (⦅ S b ⦆ ↓ inr ⋆)
  goal = f , f-is-order-preserving , qinvs-are-equivs f (g , gf , fg) , g-is-order-preserving

B-⊴-L : (ϕ : ℕ → B) (n : ℕ) → ⦅ ϕ n ⦆ ⊴ ⦅ L ϕ ⦆
B-⊴-L ϕ n = sup-is-upper-bound (λ i → ⦅ ϕ i ⦆) n

⊴-and-⊲-implies-⊲ : (α β γ :  Ordinal 𝓤) → α ⊴ β → β ⊲ γ → α ⊲ γ
⊴-and-⊲-implies-⊲ α β γ (f , hf) (c , eq) = {!!}

B-rec : {X : 𝓤₀ ̇ } → X → (X → X) → ((ℕ → X) → X) → B → X
B-rec z s l Z     = z
B-rec z s l (S d) = s (B-rec z s l d)
B-rec z s l (L ϕ) = l (B-rec z s l ∘ ϕ)

\end{code}

Addition of Brouwer trees.

\begin{code}

B-add : B → B → B
B-add u v = B-rec v S L u

\end{code}

Multiplication of Brouwer trees.

\begin{code}

B-mul : B → B → B
B-mul u v = B-rec Z (λ r → B-add u r) L v

\end{code}

Exponentiation of Brouwer trees.

\begin{code}

B-exp : B → B → B
B-exp u v = B-rec (S Z) (λ r → B-mul u r) L v

\end{code}

Given a natural number `n : ℕ`, `B-finite n` denotes the finite ordinal
corresponding to `n`.

\begin{code}

B-finite : ℕ → B
B-finite = rec Z S

\end{code}

By taking the limit of all finite ordinals, we obtain `ω`.

\begin{code}

B-ω : B
B-ω = L B-finite

\end{code}

We now write down the sequence of iterating the operation of exponentiating `ω`
to itself.

\begin{code}

B-ω-tower : ℕ → B
B-ω-tower = rec B-ω (B-exp B-ω)

ω-tower-0 : B-ω-tower 0 ＝ B-ω
ω-tower-0 = refl

ω-tower-1 : B-ω-tower 1 ＝ (B-exp B-ω B-ω)
ω-tower-1 = refl

\end{code}

and so on and so on...

When we take the limit of this sequence, we obtain `ε₀`.

\begin{code}

B-ε₀ : B
B-ε₀ = L B-ω-tower

ε₀ : Ordinal 𝓤₀
ε₀ = ⦅ B-ε₀ ⦆

\end{code}

The following is taken from Peter Hancock's MGS lecture notes on
(ordinal-theoretic) proof theory.

We can define the ordering relation on Brouwer codes directly. We start
by defining a type of downward paths from an ordinal that pass through
at least one successor ordinal.

By induction on the paths and the base ordinal, we can give the corresponding
ordinal that the path ended at.

\begin{code}

downpath-through-S : B → 𝓤₀ ̇
downpath-through-S Z     = 𝟘
downpath-through-S (S b) = 𝟙 + downpath-through-S b
downpath-through-S (L ϕ) = Σ n ꞉ ℕ , downpath-through-S (ϕ n)

path-to-ordinal : {b : B} → downpath-through-S b → B
path-to-ordinal {S b} (inl ⋆) = b
path-to-ordinal {S b} (inr p) = path-to-ordinal p
path-to-ordinal {L ϕ} (n , p) = path-to-ordinal p

\end{code}

We define `b ⊑ c` by induction on the code `b` according to the following
three cases:
  - `z ⊑ c` holds for all codes `c`
  - `S b ⊑ c` holds if there is a path `p` down from `c` such that
    `b ⊑ path-to-ordinal p`
  - `L ϕ ⊑ c` if `ϕ n ⊑ c` for all natural numbers `n`

Notice that this relation is not proposition-valued due to the successor
case which asks for existence of a path.

From `_⊑_` we can define the strict relation `_⊏_`. Again, this will also
not be proposition-valued.

\begin{code}

data _⊑_ : B → B → 𝓤₀ ̇ where
 Z-⊑ : (c : B) → Z ⊑ c
 S-⊑ : (b c : B) (p : downpath-through-S c) → b ⊑ path-to-ordinal p → S b ⊑ c
 L-⊑ : (ϕ : ℕ → B) (c : B) → ((n : ℕ) → ϕ n ⊑ c) → L ϕ ⊑ c

_⊏_ : B → B → 𝓤₀ ̇
b ⊏ c = Σ p ꞉ downpath-through-S c , b ⊑ path-to-ordinal p

\end{code}
