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

The following is inspired by Peter Hancock's MGS 2008 lecture notes on
(ordinal-theoretic) proof theory. These are available at
`https://www.cs.bham.ac.uk/~mhe/events/MGS08/notes/proofTheory.pdf`

We can define the ordering relation on Brouwer codes directly. We start by
defining a syntactic and extensional notion of strict subtree `_◂_`, from which
we define the weak (`_⊑_`) and strict (`_⊏_`) pre-orderings of trees.

This approach is equivalent to the use of paths in the foregoing notes, but
lends itself to easier formalisation.

\begin{code}

data _◂_ : B → B → 𝓤₀ ̇ where
 ◂-stop : {b c : B}
        → b ≈ c
        → b ◂ S c

 ◂-continue : {b c : B}
            → b ◂ c
            → b ◂ S c

 ◂-pick : {b : B} (ϕ : ℕ → B) (n : ℕ)
        → b ◂ ϕ n
        → b ◂ L ϕ

≈-preserves-◂-left : {b c d : B}
                  → b ◂ c
                  → b ≈ d
                  → d ◂ c
≈-preserves-◂-left (◂-stop h)     l = ◂-stop (≈-trans (≈-sym l) h)
≈-preserves-◂-left (◂-continue h) l = ◂-continue (≈-preserves-◂-left h l)
≈-preserves-◂-left (◂-pick ϕ n h) l = ◂-pick ϕ n (≈-preserves-◂-left h l)

≈-preserves-◂-right : {b c d : B}
                   → b ◂ c
                   → c ≈ d
                   → b ◂ d
≈-preserves-◂-right (◂-stop h) (S≈ l) = ◂-stop (≈-trans h l)
≈-preserves-◂-right (◂-continue h) (S≈ l) =
 ◂-continue (≈-preserves-◂-right h l)
≈-preserves-◂-right (◂-pick ϕ n h) (L≈ ϕ ψ l) =
 ◂-pick ψ n (≈-preserves-◂-right h (l n))

◂-trans : {b c d : B}
        → b ◂ c
        → c ◂ d
        → b ◂ d
◂-trans h (◂-stop l)     = ≈-preserves-◂-right (◂-continue h) (S≈ l)
◂-trans h (◂-continue l) = ◂-continue (◂-trans h l)
◂-trans h (◂-pick ϕ n l) = ◂-pick ϕ n (◂-trans h l)

\end{code}

We define `b ⊑ c` by induction on the code `b` according to the following
three cases:
 - `z ⊑ c` holds for all codes `c`
 - `S b ⊑ c` holds if there is a strict subtree path `d` of `c` such that `b ⊑ d`
 - `L ϕ ⊑ c` if `ϕ n ⊑ c` for all natural numbers `n`

Notice that this relation is not proposition-valued due to the successor
case which asks for existence of a path.

From `_⊑_` we can define the strict relation `_⊏_`. Again, this will also
not be proposition-valued.

\begin{code}

data _⊑_ : B → B → 𝓤₀ ̇ where
 Z-⊑ : (c : B)
     → Z ⊑ c

 S-⊑ : (b d c : B)
     → b ⊑ d
     → d ◂ c
     → S b ⊑ c

 L-⊑ : (ϕ : ℕ → B) (c : B)
     → (∀ n → ϕ n ⊑ c)
     → L ϕ ⊑ c

_⊏_ : B → B → 𝓤₀ ̇
b ⊏ c = Σ d ꞉ B , b ⊑ d × d ◂ c

_⊒⊑_ : B → B → 𝓤₀ ̇
b ⊒⊑ c = b ⊑ c × c ⊑ b

infix 3 _⊑_
infix 3 _⊏_
infix 3 _⊒⊑_

≈-preserves-⊑-left : {b c d : B}
                   → b ⊑ c
                   → b ≈ d
                   → d ⊑ c
≈-preserves-⊑-left (Z-⊑ c) Z≈ = Z-⊑ c
≈-preserves-⊑-left (S-⊑ b e c h l) (S≈ m) =
 S-⊑ _ e c (≈-preserves-⊑-left h m) l
≈-preserves-⊑-left (L-⊑ ϕ c h) (L≈ ϕ ψ l) =
 L-⊑ ψ c (λ n → ≈-preserves-⊑-left (h n) (l n))

≈-preserves-⊑-right : {b c d : B}
                    → b ⊑ c
                    → c ≈ d
                    → b ⊑ d
≈-preserves-⊑-right (Z-⊑ _)         _ = Z-⊑ _
≈-preserves-⊑-right (S-⊑ b e c h l) m = S-⊑ b e _ h (≈-preserves-◂-right l m)
≈-preserves-⊑-right (L-⊑ ϕ c h) m =
 L-⊑ ϕ _ (λ n → ≈-preserves-⊑-right (h n) m)

≈-preserves-⊏-left : {b c d : B}
                   → b ⊏ c
                   → b ≈ d
                   → d ⊏ c
≈-preserves-⊏-left (e , h , l) m = e , ≈-preserves-⊑-left h m , l

≈-preserves-⊏-right : {b c d : B}
                    → b ⊏ c
                    → c ≈ d
                    → b ⊏ d
≈-preserves-⊏-right (e , h , l) m = e , h , ≈-preserves-◂-right l m

\end{code}

Before proving this gives a preorder on Brouwer ordinals, we need to understand
the relation `_⊑_` better. As this relation is defined by induction on the first
argument, we can often find ourselves in trouble if the first argument is a
variable. For such cases, looking at strict subtrees gives a useful sufficient
condition for `b ⊑ c`.

\begin{code}

share-subtrees-implies-⊑ : (b c : B)
                         → (∀ d → d ◂ b → d ◂ c)
                         → b ⊑ c
share-subtrees-implies-⊑ Z     c h = Z-⊑ c
share-subtrees-implies-⊑ (S b) c h = S-⊑ b b c IH (h b (◂-stop (≈-refl b)))
 where
  IH : b ⊑ b
  IH = share-subtrees-implies-⊑ b b (λ d l → l)
share-subtrees-implies-⊑ (L ϕ) c h = L-⊑ ϕ c IH
 where
  IH : (n : ℕ) → ϕ n ⊑ c
  IH n = share-subtrees-implies-⊑ (ϕ n) c (λ d l → h d (◂-pick ϕ n l))

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
b simulates c = (d : B) → d ◂ b → Σ e ꞉ B , e ◂ c × d ⊑ e

simulation-implies-⊑ : (b c : B) → b simulates c → b ⊑ c
simulation-implies-⊑ Z     c h = Z-⊑ c
simulation-implies-⊑ (S b) c h = S-⊑ b d c m l
 where
  d : B
  d = pr₁ (h b (◂-stop (≈-refl b)))

  l : d ◂ c
  l = pr₁ (pr₂ (h b (◂-stop (≈-refl b))))

  m : b ⊑ d
  m = pr₂ (pr₂ (h b (◂-stop (≈-refl b))))
simulation-implies-⊑ (L ϕ) c h = L-⊑ ϕ c IH
 where
  IH : (n : ℕ) → ϕ n ⊑ c
  IH n = simulation-implies-⊑ (ϕ n) c (λ d l → h d (◂-pick ϕ n l))

⊑-implies-simulation : {b c : B} → b ⊑ c → b simulates c
⊑-implies-simulation (S-⊑ b e c h m) d (◂-stop n) =
 e , m , ≈-preserves-⊑-left h (≈-sym n)
⊑-implies-simulation (S-⊑ b e c h r) d (◂-continue l) =
 f , ◂-trans x r , y
 where
  IH : Σ f ꞉ B , f ◂ e × d ⊑ f
  IH = ⊑-implies-simulation h d l

  f : B
  f = pr₁ IH

  x : f ◂ e
  x = pr₁ (pr₂ IH)

  y : d ⊑ f
  y = pr₂ (pr₂ IH)
⊑-implies-simulation (L-⊑ ϕ _ x) d (◂-pick ϕ n l) = ⊑-implies-simulation (x n) d l

\end{code}

With this we can now prove that the constructors `S` and `L` of Brouwer
ordinals always give bigger ordinals.

\begin{code}

S-is-inflationary : (b : B) → b ⊑ S b
S-is-inflationary b = share-subtrees-implies-⊑ b (S b)
                                               (λ d h → ◂-continue h)

L-is-upper-bound : (ϕ : ℕ → B) (n : ℕ) → ϕ n ⊑ L ϕ
L-is-upper-bound ϕ n = share-subtrees-implies-⊑ (ϕ n) (L ϕ)
                                                (λ d h → ◂-pick ϕ n h)

\end{code}

From these, along with the alternate characterisation of `_⊑_`, we can
now prove that the strict and non-strict ordering satisfy most of the properties
we would expect.

\begin{code}

⊑-refl : (b : B) → b ⊑ b
⊑-refl Z     = Z-⊑ Z
⊑-refl (S b) = S-⊑ b b (S b) (⊑-refl b) (◂-stop (≈-refl b))
⊑-refl (L ϕ) = L-⊑ ϕ (L ϕ) (L-is-upper-bound ϕ)

⊑-trans : (b c d : B) → b ⊑ c → c ⊑ d → b ⊑ d
⊑-trans Z     c d (Z-⊑ c)       l = Z-⊑ d
⊑-trans (S b) c d (S-⊑ b e c h m) l =
 S-⊑ b f d (⊑-trans b e f h p) n
 where
  -- The situation looks like:
  --   b ⊑ e ◂ c ⊑ d
  -- using the simulation property on `c ⊑ d` we get some `f` giving
  --   b ⊑ e ⊑ f ◂ d
  -- by the inductive hypothesis this tells us that
  --   b ⊑ f ◂ d
  -- which proves `S b ⊑ d`

  f : B
  f = pr₁ (⊑-implies-simulation l e m)

  n : f ◂ d
  n = pr₁ (pr₂ (⊑-implies-simulation l e m))

  p : e ⊑ f
  p = pr₂ (pr₂ (⊑-implies-simulation l e m))
⊑-trans (L ϕ) c d (L-⊑ ϕ c h) l = L-⊑ ϕ d (λ n → ⊑-trans (ϕ n) c d (h n) l)

◂-implies-⊑ : {b c : B} → b ◂ c → b ⊑ c
◂-implies-⊑ h = share-subtrees-implies-⊑ _ _ λ d l → ◂-trans l h

⊏-implies-⊑ : (a b : B) → a ⊏ b → a ⊑ b
⊏-implies-⊑ a b (c , h , l) = ⊑-trans a c b h (◂-implies-⊑ l)

⊑-and-⊏-implies-⊏ : (a b c : B) → a ⊑ b → b ⊏ c → a ⊏ c
⊑-and-⊏-implies-⊏ a b c h (d , l , m) = d , ⊑-trans a b d h l , m

⊏-and-⊑-implies-⊏ : (a b c : B) → a ⊏ b → b ⊑ c → a ⊏ c
⊏-and-⊑-implies-⊏ a b c (d , h , l) m =
  e , ⊑-trans _ _ _ h o , n
 where
  aux : Σ e ꞉ B , e ◂ c × d ⊑ e
  aux = ⊑-implies-simulation m d l

  e : B
  e = pr₁ aux

  n : e ◂ c
  n = pr₁ (pr₂ aux)

  o : d ⊑ e
  o = pr₂ (pr₂ aux)

⊏-trans : (b c d : B) → b ⊏ c → c ⊏ d → b ⊏ d
⊏-trans b c d h l = ⊑-and-⊏-implies-⊏ b c d (⊏-implies-⊑ b c h) l

◂-implies-⊏ : {b c : B} → b ◂ c → b ⊏ c
◂-implies-⊏ {b} {c} h = b , ⊑-refl b , h

S-is-strictly-inflationary : (b : B) → b ⊏ S b
S-is-strictly-inflationary b = b , ⊑-refl b , ◂-stop (≈-refl b)

⊏-irrefl : (b : B) → ¬ (b ⊏ b)
⊏-irrefl (S b) (c , h , ◂-stop l) =
 ⊏-irrefl b (⊏-and-⊑-implies-⊏ b (S b) b (S-is-strictly-inflationary b) (≈-preserves-⊑-right h l))
⊏-irrefl (S b) (c , h , ◂-continue l) =
  ⊏-irrefl b (⊏-trans _ _ _ (⊏-and-⊑-implies-⊏ _ _ _ I II) III)
 where
  I : b ⊏ S b
  I = S-is-strictly-inflationary b

  II : S b ⊑ c
  II = h

  III : c ⊏ b
  III = ◂-implies-⊏ l
⊏-irrefl (L ϕ) (c , L-⊑ ϕ c h , ◂-pick ϕ n l) =
 ⊏-irrefl (ϕ n) (⊑-and-⊏-implies-⊏ _ _ _ (h n) (◂-implies-⊏ l))

⊒⊑-refl : (b : B) → b ⊒⊑ b
⊒⊑-refl b = ⊑-refl b , ⊑-refl b

⊒⊑-sym : (b c : B) → b ⊒⊑ c → c ⊒⊑ b
⊒⊑-sym b c (h , l) = l , h

⊒⊑-trans : (b c d : B) → b ⊒⊑ c → c ⊒⊑ d → b ⊒⊑ d
⊒⊑-trans b c d (h , l) (m , n) = ⊑-trans b c d h m , ⊑-trans d c b n l

\end{code}

Some more results that may become useful at some point.

\begin{code}

Z-is-minimal : (b : B) → ¬ (b ⊏ Z)
Z-is-minimal Z =  ⊏-irrefl Z

S-reflects-⊏ : (b c : B) → S b ⊏ S c → b ⊏ c
S-reflects-⊏ b c (d , S-⊑ b e d h m , ◂-stop n) =
 e , h , ≈-preserves-◂-right m n
S-reflects-⊏ b c (d , S-⊑ b e d h m , ◂-continue l) =
 e , h , ◂-trans m l

⊏-implies-S-⊑ : (b c : B) → b ⊏ c → S b ⊑ c
⊏-implies-S-⊑ b c (d , h , l) = S-⊑ b d c h l

S-is-monotonic : (b c : B)
               → b ⊑ c
               → S b ⊑ S c
S-is-monotonic b c h = S-⊑ b c (S c) h (◂-stop (≈-refl c))

L-is-monotonic : (ϕ ψ : ℕ → B)
               → ((n : ℕ) → ϕ n ⊑ ψ n)
               → L ϕ ⊑ L ψ
L-is-monotonic ϕ ψ h =
 L-⊑ ϕ (L ψ) (λ n → ⊑-trans (ϕ n) (ψ n) (L ψ) (h n) (L-is-upper-bound ψ n))

S-preserves-⊒⊑ : (b c : B) → b ⊒⊑ c → S b ⊒⊑ S c
S-preserves-⊒⊑ b c (h , l) = S-is-monotonic b c h , S-is-monotonic c b l

L-preserves-⊒⊑ : (ϕ ψ : ℕ → B) → ((n : ℕ) → ϕ n ⊒⊑ ψ n) → L ϕ ⊒⊑ L ψ
L-preserves-⊒⊑ ϕ ψ h = L-is-monotonic ϕ ψ (λ n → pr₁ (h n)) ,
                       L-is-monotonic ψ ϕ (λ n → pr₂ (h n))

--Z-not-⊒⊑-S : (b : B) → ¬ (Z ⊒⊑ S b)
--Z-not-⊒⊑-S Z (_ , S-⊑ .Z d .Z l x) = {!!}
--Z-not-⊒⊑-S (S b) (_ , _) = {!!}
--Z-not-⊒⊑-S (L x) (_ , _) = {!!}

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

 -- ⦅⦆-sends-⊑-to-⊴ : (b c : B) → b ⊑ c → ⦅ b ⦆ ⊴ ⦅ c ⦆
 -- ⦅⦆-sends-⊑-to-⊴ Z     c (Z-⊑ c) = 𝟘-elim , (λ x → 𝟘-elim x) , (λ x → 𝟘-elim x)
 -- ⦅⦆-sends-⊑-to-⊴ (S b) c (S-⊑ b c p h) = f , f-is-initial-segment , f-is-order-preserving
 --  where
 --   IH : ⦅ b ⦆ ⊴ ⦅ c ⦆
 --   IH = ⦅⦆-sends-⊑-to-⊴ b c (⊑-trans b (Path-to-ordinal p) c h (path-to-ordinal-⊑ p))

 --   g : ⟨ ⦅ b ⦆ ⟩ → ⟨ ⦅ c ⦆ ⟩
 --   g = pr₁ IH

 --   g-is-initial-segment : is-initial-segment ⦅ b ⦆ ⦅ c ⦆ g
 --   g-is-initial-segment = pr₁ (pr₂ IH)

 --   g-is-order-preserving : is-order-preserving ⦅ b ⦆ ⦅ c ⦆ g
 --   g-is-order-preserving = pr₂ (pr₂ IH)

 --   --foo : (x : ⟨ ⦅ b ⦆ ⟩) → g x ≺⟨ ⦅ c ⦆ ⟩ path-to-elem p
 --   --foo = {!!}

 --   f : ⟨ ⦅ b ⦆ +ₒ 𝟙ₒ ⟩  → ⟨ ⦅ c ⦆ ⟩
 --   f (inl x) = g x
 --   f (inr ⋆) = path-to-elem p

 --   f-is-initial-segment : is-initial-segment ⦅ S b ⦆ ⦅ c ⦆ f
 --   f-is-initial-segment (inl x) y l = inl (pr₁ (g-is-initial-segment x y l))
 --                                    , pr₁ (pr₂ (g-is-initial-segment x y l))
 --                                    , pr₂ (pr₂ (g-is-initial-segment x y l))
 --   f-is-initial-segment (inr ⋆) y l = {!!}
 --                                    , {!!}
 --                                    , {!!}

 --   f-is-order-preserving : is-order-preserving ⦅ S b ⦆ ⦅ c ⦆ f
 --   f-is-order-preserving (inl x) (inl y) l = g-is-order-preserving x y l
 --   f-is-order-preserving (inl x) (inr ⋆) ⋆ = {!!}
 -- ⦅⦆-sends-⊑-to-⊴ (L ϕ) c (L-⊑ ϕ c x) = {!!}

\end{code}
