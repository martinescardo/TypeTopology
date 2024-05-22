--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Ordinals.Brouwer
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module Ordinals.BrouwerOrdering where

\end{code}

The following is taken from Peter Hancock's MGS 2008 lecture notes on
(ordinal-theoretic) proof theory. These are available at
`https://www.cs.bham.ac.uk/~mhe/events/MGS08/notes/proofTheory.pdf`

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

path-to-ordinal-⊑ : {b : B} (p : PathThroughS b) → Path-to-ordinal p ⊑ b
path-to-ordinal-⊑ p = sufficient-path-condition-for-⊑ (Path-to-ordinal p) _
                        (λ q → compose-path p q , compose-path-correct p q)

compose-path-⊑ : {b : B}
                 (p : PathThroughS b) (q : PathThroughS (Path-to-ordinal p))
               → Path-to-ordinal (compose-path p q) ⊑ Path-to-ordinal p
compose-path-⊑ (stop b)     q = path-to-ordinal-⊑ q
compose-path-⊑ (continue p) q = compose-path-⊑ p q
compose-path-⊑ (pick ϕ n p) q = compose-path-⊑ p q

\end{code}

Very similar reasoning also allows us to prove the following result. Once we
know that `_⊑_` is reflexive, then we can always succeeding lemma, but
interestingly, the only proof of reflexivity we are aware of must use the
preceding lemma. An attempt to prove reflexivity using `simulation-implies-⊑`
will eventually require proving `Path-to-ordinal p ⊑ Path-to-ordinal p` for
some path `p : PathThroughS b`, but Agda does not realize that
`Path-to-ordinal p` is always structurally smaller than `b`.

\begin{code}

_simulates_ : B → B → 𝓤₀ ̇
b simulates c = (p : PathThroughS b)
              → Σ q ꞉ PathThroughS c , Path-to-ordinal p ⊑ Path-to-ordinal q

simulation-implies-⊑ : (b c : B) → b simulates c → b ⊑ c
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

⊑-implies-simulation : {b c : B} → b ⊑ c → b simulates c
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

From these, along with the alternate characterisation of `_⊑_`, we can
now prove that the strict and non-strict ordering satisfy most of the properties
we would expect.

\begin{code}

⊑-refl : (b : B) → b ⊑ b
⊑-refl Z     = Z-⊑ Z
⊑-refl (S b) = S-⊑ b (S b) (stop b) (⊑-refl b)
⊑-refl (L ϕ) = L-⊑ ϕ (L ϕ) (L-is-upper-bound ϕ)

⊏-irrefl : (b : B) → ¬ (b ⊏ b)
⊏-irrefl = {!!}

⊑-trans : (b c d : B) → b ⊑ c → c ⊑ d → b ⊑ d
⊑-trans Z     c d (Z-⊑ c)       l = Z-⊑ d
⊑-trans (S b) c d (S-⊑ b c p h) l =
 S-⊑ b d q (⊑-trans b (Path-to-ordinal p) (Path-to-ordinal q) h m)
 where
  q : PathThroughS d
  q = pr₁ (⊑-implies-simulation l p)

  m : Path-to-ordinal p ⊑ Path-to-ordinal q
  m = pr₂ (⊑-implies-simulation l p)
⊑-trans (L ϕ) c d (L-⊑ ϕ c h) l = L-⊑ ϕ d (λ n → ⊑-trans (ϕ n) c d (h n) l)

⊏-implies-⊑ : (a b : B) → a ⊏ b → a ⊑ b
⊏-implies-⊑ a b (p , h) = ⊑-trans a (Path-to-ordinal p) b h (path-to-ordinal-⊑ p)

⊑-and-⊏-implies-⊏ : (a b c : B) → a ⊑ b → b ⊏ c → a ⊏ c
⊑-and-⊏-implies-⊏ a b c h (p , l) = p , ⊑-trans a b (Path-to-ordinal p) h l

⊏-and-⊑-implies-⊏ : (a b c : B) → a ⊏ b → b ⊑ c → a ⊏ c
⊏-and-⊑-implies-⊏ a b c (p , h) l =
 q , ⊑-trans a (Path-to-ordinal p) (Path-to-ordinal q) h m
 where
  aux : Σ q ꞉ PathThroughS c , Path-to-ordinal p ⊑ Path-to-ordinal q
  aux = ⊑-implies-simulation l p

  q : PathThroughS c
  q = pr₁ aux

  m : Path-to-ordinal p ⊑ Path-to-ordinal q
  m = pr₂ aux

\end{code}

Some more results that may become useful at some point.

\begin{code}

path-to-ordinal-⊏ : {b : B} (p : PathThroughS b) → Path-to-ordinal p ⊏ b
path-to-ordinal-⊏ p = p , ⊑-refl (Path-to-ordinal p)


L-is-monotonic : (ϕ ψ : ℕ → B)
               → ((n : ℕ) → ϕ n ⊑ ψ n)
               → L ϕ ⊑ L ψ
L-is-monotonic ϕ ψ h =
 L-⊑ ϕ (L ψ) (λ n → ⊑-trans (ϕ n) (ψ n) (L ψ) (h n) (L-is-upper-bound ψ n))

\end{code}

TODO check this ordering agrees with the ordering of ordinals.

\begin{code}

module OrderingsAgree
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

 import Ordinals.NotationInterpretation0 ua pt as NotationInterpretation

 open import Ordinals.Arithmetic fe
 open import Ordinals.Equivalence
 open import Ordinals.Maps
 open import Ordinals.OrdinalOfOrdinals ua
 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open import Ordinals.Type
 open import Ordinals.Underlying

 open suprema pt sr

 ⦅_⦆ : B → Ordinal 𝓤₀
 ⦅ b ⦆ = NotationInterpretation.⟦_⟧₀ sr b

 path-to-elem : {b : B} (p : PathThroughS b) → ⟨ ⦅ b ⦆ ⟩
 path-to-elem (stop b)     = inr ⋆
 path-to-elem (continue p) = inl (path-to-elem p)
 path-to-elem (pick ϕ n p) = sum-to-sup (λ i → ⦅ ϕ i ⦆) (n , (path-to-elem p))


 ⦅⦆-sends-⊑-to-⊴ : (b c : B) → b ⊑ c → ⦅ b ⦆ ⊴ ⦅ c ⦆
 ⦅⦆-sends-⊑-to-⊴ Z     c (Z-⊑ c) = 𝟘-elim , (λ x → 𝟘-elim x) , (λ x → 𝟘-elim x)
 ⦅⦆-sends-⊑-to-⊴ (S b) c (S-⊑ b c p h) = f , f-is-initial-segment , f-is-order-preserving
  where
   IH : ⦅ b ⦆ ⊴ ⦅ c ⦆
   IH = ⦅⦆-sends-⊑-to-⊴ b c (⊑-trans b (Path-to-ordinal p) c h (path-to-ordinal-⊑ p))

   g : ⟨ ⦅ b ⦆ ⟩ → ⟨ ⦅ c ⦆ ⟩
   g = pr₁ IH

   g-is-initial-segment : is-initial-segment ⦅ b ⦆ ⦅ c ⦆ g
   g-is-initial-segment = pr₁ (pr₂ IH)

   g-is-order-preserving : is-order-preserving ⦅ b ⦆ ⦅ c ⦆ g
   g-is-order-preserving = pr₂ (pr₂ IH)

   --foo : (x : ⟨ ⦅ b ⦆ ⟩) → g x ≺⟨ ⦅ c ⦆ ⟩ path-to-elem p
   --foo = {!!}

   f : ⟨ ⦅ b ⦆ +ₒ 𝟙ₒ ⟩  → ⟨ ⦅ c ⦆ ⟩
   f (inl x) = g x
   f (inr ⋆) = path-to-elem p

   f-is-initial-segment : is-initial-segment ⦅ S b ⦆ ⦅ c ⦆ f
   f-is-initial-segment (inl x) y l = inl (pr₁ (g-is-initial-segment x y l))
                                    , pr₁ (pr₂ (g-is-initial-segment x y l))
                                    , pr₂ (pr₂ (g-is-initial-segment x y l))
   f-is-initial-segment (inr ⋆) y l = {!!}
                                    , {!!}
                                    , {!!}

   f-is-order-preserving : is-order-preserving ⦅ S b ⦆ ⦅ c ⦆ f
   f-is-order-preserving (inl x) (inl y) l = g-is-order-preserving x y l
   f-is-order-preserving (inl x) (inr ⋆) ⋆ = {!!}
 ⦅⦆-sends-⊑-to-⊴ (L ϕ) c (L-⊑ ϕ c x) = {!!}

\end{code}
