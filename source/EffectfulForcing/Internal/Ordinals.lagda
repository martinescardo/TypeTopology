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
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' = Univalence-gives-Fun-Ext ua

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Ordinals.Arithmetic fe
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
B-⊲-S b = (inr ⋆) , eqtoidₒ (ua 𝓤₀) fe' ⦅ b ⦆ (⦅ S b ⦆ ↓ inr ⋆) goal
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

data PathThroughS : B → 𝓤₀ ̇ where
 stop     : (b : B) → PathThroughS (S b)
 continue : {b : B} → PathThroughS b → PathThroughS (S b)
 pick     : (ϕ : ℕ → B) (n : ℕ) → PathThroughS (ϕ n) → PathThroughS (L ϕ)

Path-to-ordinal : {b : B} → PathThroughS b → B
Path-to-ordinal (stop b)     = b
Path-to-ordinal (continue p) = Path-to-ordinal p
Path-to-ordinal (pick ϕ n p) = Path-to-ordinal p

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
 S-⊑ : (b c : B) (p : PathThroughS c) → b ⊑ Path-to-ordinal p → S b ⊑ c
 L-⊑ : (ϕ : ℕ → B) (c : B) → ((n : ℕ) → ϕ n ⊑ c) → L ϕ ⊑ c

-- TODO tidy up

-- Crucial lemma to prove that L gives the least upper bound
lemma : (b c : B)
      → ((p : PathThroughS b) → Σ q ꞉ PathThroughS c , Path-to-ordinal p ＝ Path-to-ordinal q)
      → b ⊑ c
lemma Z c h     = Z-⊑ c
lemma (S b) c h = S-⊑ b c q (transport (b ⊑_) e IH)
 where
  p : PathThroughS (S b)
  p = stop b

  q : PathThroughS c
  q = pr₁ (h p)

  e : Path-to-ordinal p ＝ Path-to-ordinal q
  e = pr₂ (h p)

  IH : b ⊑ b
  IH = lemma b b (λ r → r , refl)
lemma (L ϕ) c h = L-⊑ ϕ c IH
 where
  IH : (n : ℕ) → ϕ n ⊑ c
  IH n = lemma (ϕ n) c (h ∘ pick ϕ n)


_⊏_ : B → B → 𝓤₀ ̇
b ⊏ c = Σ p ꞉ PathThroughS c , b ⊑ Path-to-ordinal p

\end{code}

Trying to figure out some properties of this order

\begin{code}

_ : L (λ n → rec Z S n) ⊑ L (λ n → rec Z S n)
_ = L-⊑ _ _ aux
 where
  aux : (n : ℕ) → rec Z S n ⊑ L (λ n → rec Z S n)
  aux zero     = Z-⊑ (L (rec Z S))
  aux (succ n) = S-⊑ _ _ (pick _ n {!!}) {!!}

⊑-trans : (b c d : B) → b ⊑ c → c ⊑ d → b ⊑ d
⊑-trans b c d h l = {!!}

mutual
 L-is-monotonic : (ϕ ψ : ℕ → B)
                → ((n : ℕ) → ϕ n ⊑ ψ n)
                → L ϕ ⊑ L ψ
 L-is-monotonic ϕ ψ h = L-⊑ ϕ (L ψ) IH
  where
   IH : (n : ℕ) → ϕ n ⊑ L ψ
   IH n = ⊑-trans (ϕ n) (ψ n) (L ψ) (h n) (L-is-upper-bound ψ n)

 L-is-upper-bound : (ϕ : ℕ → B) (n : ℕ) → ϕ n ⊑ L ϕ
 L-is-upper-bound ϕ n = lemma (ϕ n) (L ϕ) (λ p → pick ϕ n p , refl)

⊑-refl : (b : B) → b ⊑ b
⊑-refl Z     = Z-⊑ Z
⊑-refl (S b) = S-⊑ b (S b) (stop b) (⊑-refl b)
⊑-refl (L ϕ) = L-⊑ ϕ (L ϕ) (L-is-upper-bound ϕ)

S-is-inflationary : (b : B) → b ⊑ S b
S-is-inflationary Z     = Z-⊑ (S Z)
S-is-inflationary (S b) = S-⊑ b (S (S b)) (stop (S b)) (S-is-inflationary b)
S-is-inflationary (L ϕ) = L-⊑ ϕ (S (L ϕ)) aux
 where
  aux : (i : ℕ) → ϕ i ⊑ S (L ϕ)
  aux i = ⊑-trans (ϕ i) (S (ϕ i)) (S (L ϕ))
                (S-is-inflationary (ϕ i))
                (S-⊑ (ϕ i) (S (L ϕ)) (stop (L ϕ)) (L-is-upper-bound ϕ i))

path-to-ordinal-⊑-ordinal : (b : B) (p : PathThroughS b)
                          →  Path-to-ordinal p ⊑ b
path-to-ordinal-⊑-ordinal (S b) (stop b) = S-is-inflationary b
path-to-ordinal-⊑-ordinal (S b) (continue p) =
 ⊑-trans (Path-to-ordinal p) b (S b)
  (path-to-ordinal-⊑-ordinal b p) (S-is-inflationary b)
path-to-ordinal-⊑-ordinal (L ϕ) (pick ϕ n p) =
 ⊑-trans (Path-to-ordinal p) (ϕ n) (L ϕ)
  (path-to-ordinal-⊑-ordinal (ϕ n) p) (L-is-upper-bound ϕ n)

⦅⦆-sends-⊑-to-⊴ : (b c : B) → b ⊑ c → ⦅ b ⦆ ⊴ ⦅ c ⦆
⦅⦆-sends-⊑-to-⊴ Z     c (Z-⊑ c) = 𝟘-elim , (λ x → 𝟘-elim x) , (λ x → 𝟘-elim x)
⦅⦆-sends-⊑-to-⊴ (S b) c (S-⊑ b c p h) = f , f-is-initial-segment , f-is-order-preserving
 where
  IH : ⦅ b ⦆ ⊴ ⦅ Path-to-ordinal p ⦆
  IH = ⦅⦆-sends-⊑-to-⊴ b (Path-to-ordinal p) h

  f : ⟨ ⦅ b ⦆ +ₒ 𝟙ₒ ⟩  → ⟨ ⦅ c ⦆ ⟩
  f = {!!}

  f-is-initial-segment : is-initial-segment ⦅ S b ⦆ ⦅ c ⦆ f
  f-is-initial-segment x = {!!}

  f-is-order-preserving : is-order-preserving ⦅ S b ⦆ ⦅ c ⦆ f
  f-is-order-preserving x = {!!}
⦅⦆-sends-⊑-to-⊴ (L ϕ) c (L-⊑ ϕ c x) = {!!}

\end{code}
