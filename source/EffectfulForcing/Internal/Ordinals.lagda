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

compose-path : {b : B} (p : PathThroughS b) → PathThroughS (Path-to-ordinal p)
             → PathThroughS b
compose-path (stop b)     q = continue q
compose-path (continue p) q = continue (compose-path p q)
compose-path (pick ϕ n p) q = pick ϕ n (compose-path p q)

compose-path-correct : {b : B}
                       (p : PathThroughS b)
                       (q : PathThroughS (Path-to-ordinal p))
                     → Path-to-ordinal q ＝ Path-to-ordinal (compose-path p q)
compose-path-correct (stop b)     q = refl
compose-path-correct (continue p) q = compose-path-correct p q
compose-path-correct (pick ϕ n p) q = compose-path-correct p q

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

_⊏_ : B → B → 𝓤₀ ̇
b ⊏ c = Σ p ꞉ PathThroughS c , b ⊑ Path-to-ordinal p

\end{code}

Before proving this gives a preorder on Brouwer ordinals, we need to understand
the relation `_⊑_` better. As this relation is defined by induction on the first
argument, we can often find ourselves in trouble if the first argument is
a variable. For such cases, looking at paths gives a useful sufficient condition
for `b ⊑ c`.

\begin{code}

sufficient-path-condition-for-⊑ : (b c : B)
                                → ((p : PathThroughS b)
                                      → Σ q ꞉ PathThroughS c ,
                                        Path-to-ordinal p ＝ Path-to-ordinal q)
                                → b ⊑ c
sufficient-path-condition-for-⊑ Z c h     = Z-⊑ c
sufficient-path-condition-for-⊑ (S b) c h = S-⊑ b c q (transport (b ⊑_) e IH)
 where
  p : PathThroughS (S b)
  p = stop b

  q : PathThroughS c
  q = pr₁ (h p)

  e : Path-to-ordinal p ＝ Path-to-ordinal q
  e = pr₂ (h p)

  IH : b ⊑ b
  IH = sufficient-path-condition-for-⊑ b b (λ r → r , refl)
sufficient-path-condition-for-⊑ (L ϕ) c h = L-⊑ ϕ c IH
 where
  IH : (n : ℕ) → ϕ n ⊑ c
  IH n = sufficient-path-condition-for-⊑ (ϕ n) c (h ∘ pick ϕ n)

\end{code}

Very similar reasoning also allows us to prove the following result. Once we
know that `_⊑_` is reflexive, then we can always succeeding lemma, but
interestingly, the only proof of reflexivity we are aware of must use the
preceding lemma. An attempt to prove reflexivity using `simulation-implies-⊑`
will eventually require proving `Path-to-ordinal p ⊑ Path-to-ordinal p` for
some path `p : PathThroughS b`, but Agda does not realize that
`Path-to-ordinal p` is always structurally smaller than `b`.

\begin{code}

simulation-implies-⊑ : (b c : B)
                     → ((p : PathThroughS b)
                           → Σ q ꞉ PathThroughS c ,
                             Path-to-ordinal p ⊑ Path-to-ordinal q)
                     → b ⊑ c
simulation-implies-⊑ Z c h     = Z-⊑ c
simulation-implies-⊑ (S b) c h = S-⊑ b c q e
 where
  p : PathThroughS (S b)
  p = stop b

  q : PathThroughS c
  q = pr₁ (h p)

  e : Path-to-ordinal p ⊑ Path-to-ordinal q
  e = pr₂ (h p)
simulation-implies-⊑ (L ϕ) c h = L-⊑ ϕ c IH
 where
  IH : (n : ℕ) → ϕ n ⊑ c
  IH n = simulation-implies-⊑ (ϕ n) c (h ∘ pick ϕ n)


path-to-ordinal-⊑ : {b : B} (p : PathThroughS b) → Path-to-ordinal p ⊑ b
path-to-ordinal-⊑ p = sufficient-path-condition-for-⊑ (Path-to-ordinal p) _
                        (λ q → compose-path p q , compose-path-correct p q)

compose-path-⊑ : {b : B}
                 (p : PathThroughS b) (q : PathThroughS (Path-to-ordinal p))
               → Path-to-ordinal (compose-path p q) ⊑ Path-to-ordinal p
compose-path-⊑ (stop b)     q = path-to-ordinal-⊑ q
compose-path-⊑ (continue p) q = compose-path-⊑ p q
compose-path-⊑ (pick ϕ n p) q = compose-path-⊑ p q

⊑-implies-simulation : {b c : B}
      → b ⊑ c
      → (p : PathThroughS b)
      → Σ q ꞉ PathThroughS c , Path-to-ordinal p ⊑ Path-to-ordinal q
⊑-implies-simulation (S-⊑ b c q h) (stop b)     = q , h
⊑-implies-simulation (S-⊑ b c q h) (continue p) =
 compose-path q r , transport (Path-to-ordinal p ⊑_) (compose-path-correct q r) l
 where
  IH : Σ r ꞉ PathThroughS (Path-to-ordinal q) , Path-to-ordinal p ⊑ Path-to-ordinal r
  IH = ⊑-implies-simulation h p

  r : PathThroughS (Path-to-ordinal q)
  r = pr₁ IH

  l : Path-to-ordinal p ⊑ Path-to-ordinal r
  l = pr₂ IH
⊑-implies-simulation (L-⊑ ϕ c h)   (pick ϕ n p) = ⊑-implies-simulation (h n) p

\end{code}

With this we can now prove that the constructors `S` and `L` of Brouwer
ordinals always give bigger ordinals.

\begin{code}

S-is-inflationary : (b : B) → b ⊑ S b
S-is-inflationary b = sufficient-path-condition-for-⊑ b (S b)
                                                      (λ p → continue p , refl)

L-is-upper-bound : (ϕ : ℕ → B) (n : ℕ) → ϕ n ⊑ L ϕ
L-is-upper-bound ϕ n = sufficient-path-condition-for-⊑ (ϕ n) (L ϕ)
                                                       (λ p → pick ϕ n p , refl)

\end{code}

\begin{code}

⊑-refl : (b : B) → b ⊑ b
⊑-refl Z     = Z-⊑ Z
⊑-refl (S b) = S-⊑ b (S b) (stop b) (⊑-refl b)
⊑-refl (L ϕ) = L-⊑ ϕ (L ϕ) (L-is-upper-bound ϕ)


⊑-trans : (b c d : B) → b ⊑ c → c ⊑ d → b ⊑ d
⊑-trans Z     c d (Z-⊑ c)       l = Z-⊑ d
⊑-trans (S b) c d (S-⊑ b c p h) l =
 S-⊑ b d {!!} {!!}
--⊑-trans (S b) (S c) d (S-⊑ b (S c) p h) (S-⊑ c d q l) =
-- {!!}
--⊑-trans (S b) (L ϕ) d (S-⊑ b (L ϕ) p h) (L-⊑ ϕ d l) =
-- {!!}
⊑-trans (L ϕ) c d (L-⊑ ϕ c h)   l = L-⊑ ϕ d (λ n → ⊑-trans (ϕ n) c d (h n) l)


L-is-monotonic : (ϕ ψ : ℕ → B)
               → ((n : ℕ) → ϕ n ⊑ ψ n)
               → L ϕ ⊑ L ψ
L-is-monotonic ϕ ψ h = L-⊑ ϕ (L ψ) IH
 where
  IH : (n : ℕ) → ϕ n ⊑ L ψ
  IH n = ⊑-trans (ϕ n) (ψ n) (L ψ) (h n) (L-is-upper-bound ψ n)

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
