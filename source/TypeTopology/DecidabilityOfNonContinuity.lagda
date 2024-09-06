Martin Escardo, 7 May 2014, with many additions in the summer of 2024.

For any function f : ℕ∞ → ℕ, it is decidable whether f is non-continuous.

  (f : ℕ∞ → ℕ) → ¬ continuous f + ¬¬ continuous f.

Based on the paper

[1] Martin Escardo. Constructive decidability of classical continuity.
    Mathematical Structures in Computer Science , Volume 25,
    October 2015 , pp. 1578 - 1589
    https://doi.org/10.1017/S096012951300042X

The title of this paper is a bit misleading. It should probably have
been called "Decidability of non-continuity". In any case, it is not
wrong.

TODO. Parametrize this module by a discrete type, rather than use 𝟚 or
ℕ as the types of values of functions.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.DecidabilityOfNonContinuity (fe : funext 𝓤₀ 𝓤₀) where

open import CoNaturals.Type
open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import NotionsOfDecidability.Decidable
open import NotionsOfDecidability.SemiDecidable hiding (LPO)
open import Taboos.LPO
open import TypeTopology.ADecidableQuantificationOverTheNaturals fe
open import UF.DiscreteAndSeparated

\end{code}

TODO. Give a more sensible name of the following fact. It is the name
given in [1].

This is an iterated version of Theorem 8.2 of [2], which also deserves
a better name here, and it is the crucial lemma to prove the
decidability of non-continuity.

[2] Martin Escardo. Infinite sets that satisfy the principle of
    omniscience in all varieties of constructive mathematics, Journal
    of Symbolic Logic, volume 78, number 3, September 2013, pages
    764-784.

    https://doi.org/10.2178/jsl.7803040

\begin{code}

Lemma-3·1 : (A : ℕ∞ → ℕ∞ → 𝓤 ̇ )
          → ((x y : ℕ∞) → is-decidable (A x y))
          → is-decidable ((m : ℕ) → ¬ ((n : ℕ) → A (ι m) (ι n)))
Lemma-3·1 {𝓤} A δ = III
 where
  B : ℕ∞ → 𝓤 ̇
  B u = (n : ℕ) → A u (ι n)

  I :  (x : ℕ∞) → is-decidable (B x)
  I x = Theorem-8·2' (A x) (δ x)

  II :  (x : ℕ∞) → is-decidable (¬ B x)
  II x = ¬-preserves-decidability (I x)

  III : is-decidable ((n : ℕ) → ¬ B (ι n))
  III = Theorem-8·2' (λ x → ¬ B x) II

\end{code}

The following is the original formulation of the above in [1], which
we keep nameless as it is not needed for our purposes and in any case
is just a direct particular case.

\begin{code}

_ : (q : ℕ∞ → ℕ∞ → 𝟚)
  → is-decidable ((m : ℕ) → ¬ ((n : ℕ) → q (ι m) (ι n) ＝ ₁))
_ = λ q → Lemma-3·1 (λ x y → q x y ＝ ₁) (λ x y → 𝟚-is-discrete (q x y) ₁)

\end{code}

Omitting the inclusion function, or coercion,

   ι : ℕ → ℕ∞,

a map f : ℕ∞ → ℕ is called continuous iff

   ∃ m : ℕ , ∀ n ≥ m , f n ＝ f ∞,

where m and n range over the natural numbers.

The negation of this statement is (constructively) equivalent to

   ∀ m : ℕ , ¬ ∀ n ≥ m , f n ＝ f ∞.

We can implement ∀ y ≥ x , A y as ∀ x , A (max x y), so that the
continuity of f amounts to

   ∃ m : ℕ ,  ∀ n : ℕ , f (max m n) ＝ f ∞,

and its negation to

   ∀ m : ℕ , ¬ ∀ n : ℕ , f (max m n) ＝ f ∞,

and it is convenient to do so here.

The above paper [1] mentions that its mathematical development can be
carried out in a number of foundations, including type theory, but it
doesn't say what "∃" should be taken to mean in HoTT/UF. It turns out
(added summer 2024 - see below) that it doesn't matter whether `∃` is
interpreted to mean `Σ` or the propositional truncation of `Σ`,
although this is non trivial and is proved below (summer 2024), but
does follow from what is developed in [1].

For the following, we adopt `∃` to mean the propositional truncation
of `Σ` (as we generally do in TypeTopology).

For the next few things, because we are going to prove facts about the
negation of continuity, it doesn't matter whether we define the notion
with ∃ or Σ, and we choose the latter for convenience.

\begin{code}

continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
continuous f = Σ m ꞉ ℕ , ((n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)

\end{code}

Later we are going to use the terminology `is-continuous f` for the
propositional truncation of the type `continuous f`, but also it will
be more appropriate to think of the type `continuous f` as that of
continuity data for f.

\begin{code}

continuity-data = continuous

\end{code}

The following is Theorem 3.2 of [1].

\begin{code}

module _ (f : ℕ∞ → ℕ) where

 private
  Theorem-3·2 : is-decidable (¬ continuous f)
  Theorem-3·2 = map-decidable
                 uncurry
                 curry
                 (Lemma-3·1
                   (λ x y → f (max x y) ＝ (f ∞))
                   (λ x y → ℕ-is-discrete (f (max x y)) (f ∞)))

\end{code}

For our purposes, the following terminology is better.

\begin{code}

 the-negation-of-continuity-is-decidable = Theorem-3·2

\end{code}

TODO. The paper [1] also discusses the following.

 1. MP gives that continuity and doubly negated continuity agree.

 2. WLPO is equivalent to the existence of a noncontinuous function
    ℕ∞ → ℕ.

 3. ¬ WLPO is equivalent to the doubly negated continuity of all
    functions ℕ∞ → ℕ.

 4. If MP and ¬ WLPO then all functions ℕ∞ → ℕ are continuous.

Added 24th July 2024. Still based on the paper [1]. We write down the
proofs of (2) and (3).

\begin{code}

open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness fe

noncontinuous-map-gives-WLPO : (f : ℕ∞ → ℕ) → ¬ continuous f → WLPO
noncontinuous-map-gives-WLPO f f-non-cts = VI
 where
  g : (u : ℕ∞)
    → Σ v₀ ꞉ ℕ∞ , (f (max u v₀) ＝ f ∞ → (v : ℕ∞) → f (max u v) ＝ f ∞)
  g u = ℕ∞-Compact∙
         (λ v → f (max u v) ＝ f ∞)
         (λ v → ℕ-is-discrete (f (max u v)) (f ∞))

  G : ℕ∞ → ℕ∞
  G u = max u (pr₁ (g u))

  G-property₀ : (u : ℕ∞) → f (G u) ＝ f ∞ → (v : ℕ∞) → f (max u v) ＝ f ∞
  G-property₀ u = pr₂ (g u)

  G-property₁ : (u : ℕ∞)
              → (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
              → f (G u) ≠ f ∞
  G-property₁ u (v , d) = contrapositive
                            (λ (e : f (G u) ＝ f ∞) → G-property₀ u e v)
                            d

  I : (u : ℕ∞)
    → ¬¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
    → (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
  I u = Σ-Compactness-gives-Complemented-choice
          ℕ∞-Compact
          (λ v → f (max u v) ≠ f ∞)
          (λ v → ¬-preserves-decidability
                  (ℕ-is-discrete (f (max u v)) (f ∞)))

  II : (u : ℕ∞)
     → ¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
     → (v : ℕ∞) → f (max u v) ＝ f ∞
  II u ν v = discrete-is-¬¬-separated
              ℕ-is-discrete
              (f (max u v))
              (f ∞)
              (λ (d : f (max u v) ≠ f ∞) → ν (v , d))

  III : (u : ℕ∞)
      → ¬ ((v : ℕ∞) → f (max u v) ＝ f ∞)
      → ¬¬ (Σ v ꞉ ℕ∞ , f (max u v) ≠ f ∞)
  III u = contrapositive (II u)

  G-property₂ : (u : ℕ∞)
              → ¬ ((v : ℕ∞) → f (max u v) ＝ f ∞)
              → f (G u) ≠ f ∞
  G-property₂ u a = G-property₁ u (I u (III u a))

  G-propertyₙ : (n : ℕ) → f (G (ι n)) ≠ f ∞
  G-propertyₙ n = G-property₂ (ι n) h
   where
    h : ¬ ((v : ℕ∞) → f (max (ι n) v) ＝ f ∞)
    h a = f-non-cts (n , a ∘ ι)

  G-property∞ : G ∞ ＝ ∞
  G-property∞ = max∞-property (pr₁ (g ∞))

  IV : (u : ℕ∞) → u ＝ ∞ → f (G u) ＝ f ∞
  IV u refl = ap f G-property∞

  V : (u : ℕ∞) → f (G u) ＝ f ∞ → u ＝ ∞
  V u a = not-finite-is-∞ fe h
   where
    h : (n : ℕ) → u ≠ ι n
    h n refl = G-propertyₙ n a

  VI : WLPO
  VI u = map-decidable (V u) (IV u) (ℕ-is-discrete (f (G u)) (f ∞))

\end{code}

In the following fact we can replace Σ by ∃ because WLPO is a
proposition. Hence WLPO is the propositional truncation of the type
Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f.

TODO. Add this code for this observation.

The following is from [1] with the same proof.

\begin{code}

open import Taboos.BasicDiscontinuity fe
open import Naturals.Properties

WLPO-iff-there-is-a-noncontinous-map : WLPO ↔ (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
WLPO-iff-there-is-a-noncontinous-map =
  I ,
  (λ (f , ν) → noncontinuous-map-gives-WLPO f ν)
 where
  I : WLPO → Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f
  I wlpo = f , f-non-cts
   where
    p : ℕ∞ → 𝟚
    p = pr₁ (WLPO-is-discontinuous wlpo)

    p-spec : ((n : ℕ) → p (ι n) ＝ ₀) × (p ∞ ＝ ₁)
    p-spec = pr₂ (WLPO-is-discontinuous wlpo)

    g : 𝟚 → ℕ
    g ₀ = 0
    g ₁ = 1

    f : ℕ∞ → ℕ
    f = g ∘ p

    f₀ : (n : ℕ) → f (ι n) ＝ 0
    f₀ n =  f (ι n) ＝⟨ ap g (pr₁ p-spec n) ⟩
            g ₀     ＝⟨ refl ⟩
            0       ∎

    f∞ : (n : ℕ) → f (ι n) ≠ f ∞
    f∞ n e = zero-not-positive 0
              (0       ＝⟨ f₀ n ⁻¹ ⟩
               f (ι n) ＝⟨ e ⟩
               f ∞     ＝⟨ ap g (pr₂ p-spec) ⟩
               1       ∎)

    f-non-cts : ¬ continuous f
    f-non-cts (m , a) = f∞ m
                         (f (ι m)             ＝⟨ ap f ((max-idemp fe (ι m))⁻¹) ⟩
                          f (max (ι m) (ι m)) ＝⟨ a m ⟩
                          f ∞                 ∎)

¬WLPO-iff-all-maps-are-¬¬-continuous : ¬ WLPO ↔ ((f : ℕ∞ → ℕ) → ¬¬ continuous f)
¬WLPO-iff-all-maps-are-¬¬-continuous =
 (λ nwlpo f f-non-cts
   → contrapositive
      (rl-implication WLPO-iff-there-is-a-noncontinous-map)
      nwlpo
      (f , f-non-cts)) ,
 (λ (a : (f : ℕ∞ → ℕ) → ¬¬ continuous f)
   → contrapositive
      (lr-implication WLPO-iff-there-is-a-noncontinous-map)
      (λ (f , f-non-cts) → a f f-non-cts))

\end{code}

Hence ¬ WLPO can be considered as a (rather weak) continuity principle.

It is shown in [2] that negative consistent axioms can be postulated
in MLTT without loss of canonicity, and Andreas Abel filled important
gaps and formalized this in Agda [3] using a logical-relations
technique. Hence we can, if we wish, postulate ¬ WLPO without loss of
canonicity, and get a weak continuity axiom for free. But notice that
we can also postulate ¬¬ WLPO without loss of continuity, to get a
weak classical axiom for free. Of course, we can't postulate both at
the same time.

[2] T. Coquand, N.A. Danielsson, M.H. Escardo, U. Norell and Chuangjie Xu.
Negative consistent axioms can be postulated without loss of canonicity.
https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

[3] Andreas Abel. Negative Axioms.
    https://github.com/andreasabel/logrel-mltt/tree/master/Application/NegativeAxioms


Added 16 August 2024. This is not in [1].

The above definition of continuity is "continuity at the point ∞".
(And it is also not a proposition.)

Next we show that this is equivalent to usual continuity, as in the
module Cantor, using the fact that ℕ∞ is a subspace of the Cantor type
ℕ → 𝟚.

Moreover, in the particular case of the subspace ℕ∞ of the Cantor
space, continuity of functions ℕ∞ → ℕ is equivalent to uniform
continuity, constructively, without the need of Brouwerian axioms.

So what we will do next is to show that all imaginable notions of
(uniform) continuity for functions ℕ∞ → ℕ are equivalent,
constructively.

Moreover, the truncated and untruncated notions are also equivalent.

Added 20th August. Continuity as property gives continuity data.

\begin{code}

open import Naturals.RootsTruncation
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module continuity-criteria (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open exit-truncations pt

 is-continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-continuous f = ∃ m ꞉ ℕ , ((n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)

 module _ (f : ℕ∞ → ℕ) where

  continuity-data-gives-continuity-property : continuity-data f → is-continuous f
  continuity-data-gives-continuity-property = ∣_∣

  continuity-property-gives-continuity-data : is-continuous f → continuity-data f
  continuity-property-gives-continuity-data =
   exit-truncation (λ m → A (ι m)) (λ m → A-is-decidable (ι m))
   where
    A : ℕ∞ → 𝓤₀ ̇
    A x = (n : ℕ) → f (max x (ι n)) ＝ f ∞

    A-is-decidable : (x : ℕ∞) → is-decidable (A x)
    A-is-decidable x = Theorem-8·2'
                        (λ y → f (max x y) ＝ f ∞)
                        (λ y → ℕ-is-discrete (f (max x y)) (f ∞))
\end{code}

Next, we show that continuity is equivalent to a more familiar notion
of continuity and also equivalent to the uniform version of the of the
more familiar version. We first work with the untruncated versions.

Notice that ι denotes the inclusion ℕ → ℕ∞ and also the inclusion
ℕ∞ → (ℕ → 𝟚), where the context has to be used to disambiguate.

We first define when two extended natural numbers x and y agree up to
precision k, written x ＝⟪ k ⟫ y.

\begin{code}

open import TypeTopology.Cantor hiding (continuous ; continuity-data)

_＝⟪_⟫_ : ℕ∞ → ℕ → ℕ∞ → 𝓤₀ ̇
x ＝⟪ k ⟫ y = ι x ＝⟦ k ⟧ ι y

traditional-continuity-data : (ℕ∞ → ℕ) → 𝓤₀ ̇
traditional-continuity-data f =
 (x : ℕ∞) → Σ m ꞉ ℕ , ((y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

traditional-uniform-continuity-data : (ℕ∞ → ℕ) → 𝓤₀ ̇
traditional-uniform-continuity-data f =
 Σ m ꞉ ℕ , ((x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

\end{code}

We now need a lemma about the relation x ＝⟪ k ⟫ y.

\begin{code}

lemma₀ : (k : ℕ) (n : ℕ) → ∞ ＝⟪ k ⟫ (max (ι k) (ι n))
lemma₀ 0        n        = ⋆
lemma₀ (succ k) 0        = refl , lemma₀ k 0
lemma₀ (succ k) (succ n) = refl , lemma₀ k n

module _ (f : ℕ∞ → ℕ) where

 traditional-uniform-continuity-data-gives-traditional-continuity-data
  : traditional-uniform-continuity-data f
  → traditional-continuity-data f
 traditional-uniform-continuity-data-gives-traditional-continuity-data
  (m , m-property) x = m , m-property x

 traditional-continuity-data-gives-continuity-data
  : traditional-continuity-data f
  → continuity-data f
 traditional-continuity-data-gives-continuity-data f-cts-traditional = II
  where
   m : ℕ
   m = pr₁ (f-cts-traditional ∞)

   m-property : (y : ℕ∞) → ∞ ＝⟪ m ⟫ y → f ∞ ＝ f y
   m-property = pr₂ (f-cts-traditional ∞)

   I : (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞
   I n = (m-property (max (ι m) (ι n)) (lemma₀ m n))⁻¹

   II : continuous f
   II = m , I

\end{code}

We now need more lemmas about the relation x ＝⟪ k ⟫ y.

\begin{code}

 lemma₁ : (k : ℕ) (y : ℕ∞) → ∞ ＝⟪ k ⟫ y → max (ι k) y ＝ y
 lemma₁ 0        y ⋆       = refl
 lemma₁ (succ k) y (h , t) = γ
  where
   have-h : ₁ ＝ ι y 0
   have-h = h

   have-t : ∞ ＝⟪ k ⟫ (Pred y)
   have-t = t

   IH : max (ι k) (Pred y) ＝ Pred y
   IH = lemma₁ k (Pred y) t

   δ : ι (max (Succ (ι k)) y) ∼ ι y
   δ 0        = h
   δ (succ i) = ap (λ - → ι - i) IH

   γ : max (Succ (ι k)) y ＝ y
   γ = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe δ)

 lemma₂ : (x y : ℕ∞) (k : ℕ)
        → x ＝⟪ k ⟫ y
        → (x ＝ y) + (∞ ＝⟪ k ⟫ x)
 lemma₂ x y 0        ⋆       = inr ⋆
 lemma₂ x y (succ k) (h , t) = γ
  where
   IH : (Pred x ＝ Pred y) + (∞ ＝⟪ k ⟫ (Pred x))
   IH = lemma₂ (Pred x) (Pred y) k t

   γl∼ : Pred x ＝ Pred y → ι x ∼ ι y
   γl∼ p 0        = h
   γl∼ p (succ i) = ap (λ - → ι - i) p

   γl : Pred x ＝ Pred y → x ＝ y
   γl p = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe (γl∼ p))

   γr : ∞ ＝⟪ k ⟫ (Pred x) → (x ＝ y) + (∞ ＝⟪ succ k ⟫ x)
   γr q = 𝟚-equality-cases
           (λ (p : ι x 0 ＝ ₀)
                 → inl (x    ＝⟨ is-Zero-equal-Zero fe p ⟩
                        Zero ＝⟨ (is-Zero-equal-Zero fe (h ⁻¹ ∙ p))⁻¹ ⟩
                        y    ∎))
           (λ (p : ι x 0 ＝ ₁)
                 → inr ((p ⁻¹) , q))

   γ : (x ＝ y) + (∞ ＝⟪ succ k ⟫ x)
   γ = Cases IH (inl ∘ γl) γr

 lemma₃ : (x y : ℕ∞) (k : ℕ)
        → x ＝⟪ k ⟫ y
        → (x ＝ y) + (max (ι k) x ＝ x) × (max (ι k) y ＝ y)
 lemma₃ x y k e = III
  where
   I : ∞ ＝⟪ k ⟫ x → ∞ ＝⟪ k ⟫ y
   I q = ＝⟦⟧-trans (ι ∞) (ι x) (ι y) k q e

   II : (x ＝ y) + (∞ ＝⟪ k ⟫ x)
      → (x ＝ y) + (max (ι k) x ＝ x) × (max (ι k) y ＝ y)
   II (inl p) = inl p
   II (inr q) = inr (lemma₁ k x q , lemma₁ k y (I q))

   III : (x ＝ y) + (max (ι k) x ＝ x) × (max (ι k) y ＝ y)
   III = II (lemma₂ x y k e)

 continuity-data-gives-traditional-uniform-continuity-data
  : continuity-data f
  → traditional-uniform-continuity-data f
 continuity-data-gives-traditional-uniform-continuity-data
  (m , m-property) = m , m-property'
  where
   have-m-property : (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞
   have-m-property = m-property

   I : (z : ℕ∞) → max (ι m) z ＝ z → f z ＝ f ∞
   I z p = γ
    where
     q∞ : f (max (ι m) ∞) ＝ f ∞
     q∞ = ap f (max∞-property' fe (ι m))

     q : (u : ℕ∞) → f (max (ι m) u) ＝ f ∞
     q = ℕ∞-density fe ℕ-is-¬¬-separated m-property q∞

     γ = f z             ＝⟨ ap f (p ⁻¹) ⟩
         f (max (ι m) z) ＝⟨ q z ⟩
         f ∞             ∎

   m-property' : (x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y
   m-property' x y e =
    Cases (lemma₃ x y m e)
     (λ (p : x ＝ y) → ap f p)
     (λ (q , r) → f x ＝⟨ I x q ⟩
                  f ∞ ＝⟨ I y r ⁻¹ ⟩
                  f y ∎)

\end{code}

This closes a circle, so that that all notions of continuity data are
logically equivalent.

TODO. They should also be equivalent as types, but this is not
important for our purposes, because we are interested in continuity as
property. But maybe it would be interesting to code this anyway.

Added 21 August 2023. We now establish the logical equivalence with
the remaining propositional versions of continuity.

So far we know that, for f : ℕ∞ → ℕ,

    continuity-data f                    ↔ is-continuous f
        ↕
    traditional-continuity-data
        ↕
    traditional-uniform-continuity-data


We now complete this to the logical equivalences

    continuity-data f                   ↔ is-continuous f
        ↕
    traditional-continuity-data         ↔ is-traditionally-continuous
        ↕
    traditional-uniform-continuity-data ↔ is-traditionally-uniformly-continuous

so that all six (truncated and untruncated) notions of (uniform)
continuity for functions ℕ∞ → ℕ are logically equivalent.

\begin{code}

module more-continuity-criteria (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open exit-truncations pt

 is-traditionally-continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-traditionally-continuous f =
  (x : ℕ∞) → ∃ m ꞉ ℕ , ((y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

 is-traditionally-uniformly-continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-traditionally-uniformly-continuous f =
  ∃ m ꞉ ℕ , ((x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

 module _ (f : ℕ∞ → ℕ) where

  traditional-continuity-data-gives-traditional-continuity
   : traditional-continuity-data f
   → is-traditionally-continuous f
  traditional-continuity-data-gives-traditional-continuity d x
   = ∣ d x ∣

  traditional-continuity-gives-traditional-continuity-data
   : is-traditionally-continuous f
   → traditional-continuity-data f
  traditional-continuity-gives-traditional-continuity-data f-cts x
   = exit-truncation (C x) (C-is-decidable x) (f-cts x)
   where
    C : ℕ∞ → ℕ → 𝓤₀ ̇
    C x m = (y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y

    C-is-decidable : (x : ℕ∞) (m : ℕ) → is-decidable (C x m)
    C-is-decidable x m =
     ℕ∞-Π-Compact
      (λ y → x ＝⟪ m ⟫ y → f x ＝ f y)
      (λ y → →-preserves-decidability
              (＝⟦⟧-is-decidable (ι x) (ι y) m)
              (ℕ-is-discrete (f x) (f y)))

  traditional-uniform-continuity-data-gives-traditional-uniform-continuity
   : traditional-uniform-continuity-data f
   → is-traditionally-uniformly-continuous f
  traditional-uniform-continuity-data-gives-traditional-uniform-continuity
   = ∣_∣

  traditional-uniform-continuity-gives-traditional-uniform-continuity-data
   : is-traditionally-uniformly-continuous f
   → traditional-uniform-continuity-data f
  traditional-uniform-continuity-gives-traditional-uniform-continuity-data f-uc
   = exit-truncation U U-is-decidable f-uc
   where
    U : ℕ → 𝓤₀ ̇
    U m = (x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y

    U-is-decidable : (m : ℕ) → is-decidable (U m)
    U-is-decidable m =
     ℕ∞-Π-Compact
      (λ x → (y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)
      (λ x → ℕ∞-Π-Compact
              (λ y → x ＝⟪ m ⟫ y → f x ＝ f y)
              (λ y → →-preserves-decidability
                      (＝⟦⟧-is-decidable (ι x) (ι y) m)
                      (ℕ-is-discrete (f x) (f y))))
\end{code}

Added 2nd September 2024. This is also not in [1].

The type `ℕ∞-extension g` is that of all extensions of g : ℕ → ℕ to
functions ℕ∞ → ℕ.

Our first question is when this type is a proposition (so that it
could be called `ℕ∞-extendable g`).

Notice that LPO is stronger than WLPO, and hence, by taking the
contrapositive, ¬ WLPO is stronger than ¬ LPO:

     LPO →  WLPO
  ¬ WLPO → ¬ LPO

\begin{code}

_extends_ : (ℕ∞ → ℕ) → (ℕ → ℕ) → 𝓤₀ ̇
f extends g = f ∘ ι ∼ g

ℕ∞-extension : (ℕ → ℕ) → 𝓤₀ ̇
ℕ∞-extension g = Σ f ꞉ (ℕ∞ → ℕ) , (f extends g)

\end{code}

The following says that if all functions ℕ∞ → ℕ are continuous, or,
more generally, if just ¬ WLPO holds, then the type of ℕ∞-extensions
of g has at most one element.

(In my view, this is a situation where it would be more sensible to
use the terminology `is-subsingleton` rather than `is-prop`. In fact,
I generally prefer the former terminology over the latter, but here we
try to be consistent with the terminology of the HoTT/UF community.)

\begin{code}

¬WLPO-gives-ℕ∞-extension-is-prop
 : funext 𝓤₀ 𝓤₀
 → (g : ℕ → ℕ)
 → ¬ WLPO
 → is-prop (ℕ∞-extension g)
¬WLPO-gives-ℕ∞-extension-is-prop fe g nwlpo (f , h) (f' , h') = VI
 where
  I : (n : ℕ) → f (ι n) ＝ f' (ι n)
  I n = h n ∙ (h' n)⁻¹

  IV : f ∞ ＝ f' ∞
  IV = agreement-cotaboo' ℕ-is-discrete nwlpo f f' I

  V : f ∼ f'
  V = ℕ∞-density fe ℕ-is-¬¬-separated I IV

  VI : (f , h) ＝ (f' , h')
  VI = to-subtype-＝ (λ - → Π-is-prop fe (λ n → ℕ-is-set)) (dfunext fe V)

\end{code}

Therefore the non-propositionality of the type `ℕ∞-extension g` gives
the classical principle ¬¬ WLPO.

\begin{code}

ℕ∞-extension-is-not-prop-gives-¬¬WLPO
 : funext 𝓤₀ 𝓤₀
 → (g : ℕ → ℕ)
 → ¬ is-prop (ℕ∞-extension g)
 → ¬¬ WLPO
ℕ∞-extension-is-not-prop-gives-¬¬WLPO fe g
 = contrapositive (¬WLPO-gives-ℕ∞-extension-is-prop fe g)

\end{code}

We are unable, at the time of writing (4th September 2024) to
establish the converse.  However, if we strengthen the classical
principle ¬¬ WLPO to LPO, we can. We begin with a classical extension
lemma, which is then applied to prove this claim.

\begin{code}

LPO-gives-ℕ∞-extension
 : LPO
 → (g : ℕ → ℕ) (y : ℕ)
 → Σ f ꞉ (ℕ∞ → ℕ) , (f extends g) × (f ∞ ＝ y)
LPO-gives-ℕ∞-extension lpo g y
 = f , h , e
 where
  F : (x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , x ＝ ι n) → ℕ
  F x (inl (n , p)) = g n
  F x (inr ν)       = y

  f : ℕ∞ → ℕ
  f x = F x (lpo x)

  H : (k : ℕ) (d : is-decidable (Σ n ꞉ ℕ , ι k ＝ ι n)) → F (ι k) d ＝ g k
  H k (inl (n , p)) = ap g (ℕ-to-ℕ∞-lc (p ⁻¹))
  H k (inr ν)       = 𝟘-elim (ν (k , refl))

  h : f ∘ ι ∼ g
  h k = H k (lpo (ι k))

  L : (d : is-decidable (Σ n ꞉ ℕ , ∞ ＝ ι n)) → F ∞ d ＝ y
  L (inl (n , p)) = 𝟘-elim (∞-is-not-finite n p)
  L (inr _)       = refl

  e : f ∞ ＝ y
  e = L (lpo ∞)


LPO-gives-ℕ∞-extension-is-not-prop
 : (g : ℕ → ℕ)
 → LPO
 → ¬ is-prop (ℕ∞-extension g)
LPO-gives-ℕ∞-extension-is-not-prop g lpo ext-is-prop
  = I (LPO-gives-ℕ∞-extension lpo g 0) (LPO-gives-ℕ∞-extension lpo g 1)
 where
  I : (Σ f  ꞉ (ℕ∞ → ℕ) , (f  extends g) × (f  ∞ ＝ 0))
    → (Σ f' ꞉ (ℕ∞ → ℕ) , (f' extends g) × (f' ∞ ＝ 1))
    → 𝟘
  I (f , h , e) (f' , h' , e') =
   zero-not-positive 0
    (0    ＝⟨ e ⁻¹ ⟩
     f  ∞ ＝⟨ ap ((λ (- , _) → - ∞)) (ext-is-prop (f , h) (f' , h')) ⟩
     f' ∞ ＝⟨ e' ⟩
     1    ∎)

\end{code}

It is direct that if there is at most one extension, then LPO can't
hold.

\begin{code}

ℕ∞-extension-is-prop-gives-¬LPO
 : (g : ℕ → ℕ)
 → is-prop (ℕ∞-extension g)
 → ¬ LPO
ℕ∞-extension-is-prop-gives-¬LPO g i lpo =
 LPO-gives-ℕ∞-extension-is-not-prop g lpo i

\end{code}

So we have the chain of implications

    ¬ WLPO → is-prop (ℕ∞-extension g) → ¬ LPO.

Recall that LPO → WLPO, and so ¬ WLPO → ¬ LPO in any case. We don't
know whether the implication ¬ WLPO → ¬ LPO can be reversed in general
(we would guess not).

We also have the chain of implications

    LPO → ¬ is-prop (ℕ∞-extension g) → ¬¬ WLPO.

So the type ¬ is-prop (ℕ∞-extension g) sits between two constructive
taboos and so is an inherently classical statement.

Added 4th September 2024.

Our next question is when the type `ℕ∞-extension g` is pointed,
without assuming classical or anticlassical axioms.

\begin{code}

open import Naturals.Order renaming (max to maxℕ ; max-idemp to maxℕ-idemp)

eventually-constant : (ℕ → ℕ) → 𝓤₀ ̇
eventually-constant g = Σ m ꞉ ℕ , ((n : ℕ) → g (maxℕ m n) ＝ g m)

continuous-extension-gives-eventual-constancy
 : (g : ℕ → ℕ)
   ((f , h) : ℕ∞-extension g)
 → continuous f
 → eventually-constant g
continuous-extension-gives-eventual-constancy g (f , h) (m , a)
 = m , (λ n → g (maxℕ m n)        ＝⟨ (h (maxℕ m n))⁻¹ ⟩
              f (ι (maxℕ m n))    ＝⟨ ap f (max-fin fe m n) ⟩
              f (max (ι m) (ι n)) ＝⟨ a n ⟩
              f ∞                 ＝⟨ (a m)⁻¹ ⟩
              f (max (ι m) (ι m)) ＝⟨ ap f (max-idemp fe (ι m)) ⟩
              f (ι m)             ＝⟨ h m ⟩
              g m                 ∎)

pointed-consequence
 : (g : ℕ → ℕ)
 → ℕ∞-extension g
 → WLPO + ¬¬ eventually-constant g
pointed-consequence g (f , h) = III
 where
  II : is-decidable (¬ continuous f) → WLPO + ¬¬ eventually-constant g
  II (inl l) = inl (noncontinuous-map-gives-WLPO f l)
  II (inr r) = inr (¬¬-functor
                     (continuous-extension-gives-eventual-constancy g (f , h)) r)

  III : WLPO + ¬¬ eventually-constant g
  III = II (the-negation-of-continuity-is-decidable f)

¬WLPO-gives-that-non-eventually-constant-functions-have-no-extensions
 : (g : ℕ → ℕ)
 → ¬ WLPO
 → ¬ eventually-constant g
 → ¬ ℕ∞-extension g
¬WLPO-gives-that-non-eventually-constant-functions-have-no-extensions g nwlpo nec
 = contrapositive
    (pointed-consequence g)
    (cases nwlpo (¬¬-intro nec))

\end{code}

To be continued. We can actually get a much stronger consequence from
the pointedness of the type of extensions, to be coded here soon.
