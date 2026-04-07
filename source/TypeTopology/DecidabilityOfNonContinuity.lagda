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

The summer 2024 additions give some applications of this.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.DecidabilityOfNonContinuity (fe : funext 𝓤₀ 𝓤₀) where

open import CoNaturals.Type
open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import Naturals.Order renaming
                            (max to maxℕ ;
                             max-idemp to maxℕ-idemp ;
                             max-comm to maxℕ-comm)
open import Notation.CanonicalMap
open import Notation.Order
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import Taboos.LPO
open import Taboos.MarkovsPrinciple
open import TypeTopology.ADecidableQuantificationOverTheNaturals fe
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

For convenience, we first recall the version of Theorem 8.2 of [1],
which is used a number of times in this file, in a slighly
reformulated way which is convenient for our purposes.

[2] Martin Escardo. Infinite sets that satisfy the principle of
    omniscience in all varieties of constructive mathematics, Journal
    of Symbolic Logic, volume 78, number 3, September 2013, pages
    764-784.

    https://doi.org/10.2178/jsl.7803040

\begin{code}

_ : (A : ℕ∞ → 𝓤 ̇ )
  → is-complemented A
  → is-decidable ((n : ℕ) → A (ι n))
_ = Theorem-8·2'

\end{code}

Notice that A is defined on ℕ∞, but the decidability condition
quantifies over ℕ. So this gives an instance of WLPO that holds in
constructive mathematics.

The following, which is an iteration of the above, uses the numbering
of the paper [1], again in a slightly reformulated way, which is more
convenient for our purposes.

But notice that it isn't a simple iteration, because a negation is
inserted in the inner step.

\begin{code}

Lemma-3·1
 : (A : ℕ∞ → ℕ∞ → 𝓤 ̇ )
 → ((x y : ℕ∞) → is-decidable (A x y))
 → is-decidable ((m : ℕ) → ¬ ((n : ℕ) → A (ι m) (ι n)))
Lemma-3·1 {𝓤} A δ
 = III
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

_ : (q : ℕ∞ → ℕ∞ → 𝟚) → is-decidable ((m : ℕ) → ¬ ((n : ℕ) → q (ι m) (ι n) ＝ ₁))
_ = λ q → Lemma-3·1 (λ x y → q x y ＝ ₁) (λ x y → 𝟚-is-discrete (q x y) ₁)

\end{code}

Omitting the inclusion function, or coercion,

   ι : ℕ → ℕ∞,

a map f : ℕ∞ → ℕ is called continuous iff

   ∃ m : ℕ , ∀ n ≥ m , f n ＝ f ∞,

where m and n range over the natural numbers.

The negation of this statement is (constructively) equivalent to

   ∀ m : ℕ , ¬ ∀ n ≥ m , f n ＝ f ∞

via currying and uncurrying.

We can implement ∀ y ≥ x , A y as ∀ x , A (max x y), so that the
continuity of f amounts to

   ∃ m : ℕ ,  ∀ n : ℕ , f (max m n) ＝ f ∞,

and its negation to

   ∀ m : ℕ , ¬ ∀ n : ℕ , f (max m n) ＝ f ∞,

and it is technically convenient to do so here, in particular because
in proofs we may want to generalize the range of m or n from ℕ to ℕ∞.

The above paper [1] mentions that its mathematical development can be
carried out in a number of foundations, including dependent type
theory, but it doesn't say what "∃" should be taken to mean in
HoTT/UF. Fortunately, it turns out (added summer 2024 - see below)
that it doesn't matter whether `∃` is interpreted to mean `Σ` or the
propositional truncation of `Σ`, although this is nontrivial and is
proved below, but does follow more or less immediately from what is
developed in [1].

We start with the Σ formulation of existence for the definition of
continuity.

\begin{code}

_is-modulus-of-continuity-of_ : ℕ → (ℕ∞ → ℕ) → 𝓤₀ ̇
m is-modulus-of-continuity-of f = (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞

being-modulus-of-continuity-is-prop
 : (f : ℕ∞ → ℕ)
   (m : ℕ)
 → is-prop (m is-modulus-of-continuity-of f)
being-modulus-of-continuity-is-prop f m
 = Π-is-prop fe (λ n → ℕ-is-set)

continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
continuous f = Σ m ꞉ ℕ , m is-modulus-of-continuity-of f

modulus-of-continuity-of : (f : ℕ∞ → ℕ) → continuous f → ℕ
modulus-of-continuity-of f = pr₁

modulus-of-continuity-property
 : {f : ℕ∞ → ℕ}
   (c : continuous f)
 → (modulus-of-continuity-of f c) is-modulus-of-continuity-of f
modulus-of-continuity-property = pr₂

\end{code}

Later we are going to use the terminology `is-continuous f` for the
propositional truncation of the type `continuous f`, but also it will
be more appropriate to think of the type `continuous f` as that of
continuity data for f.

\begin{code}

continuity-data = continuous

\end{code}

The following is Theorem 3.2 of [1] and is a direct application of
Lemma 3.1, if perhaps not obvious at first sight.

\begin{code}

private
 Theorem-3·2
  : (f : ℕ∞ → ℕ)
  → is-decidable (¬ continuous f)
 Theorem-3·2 f
  = map-decidable
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

The paper [1] also discusses the following.

 1. MP gives that continuity and doubly negated continuity agree.

 2. WLPO is equivalent to the existence of a noncontinuous function
    ℕ∞ → ℕ.

 3. ¬ WLPO is equivalent to the doubly negated continuity of all
    functions ℕ∞ → ℕ.

 4. If MP and ¬ WLPO then all functions ℕ∞ → ℕ are continuous.

All of them are proved below, but not in this order.

We first prove (2).

\begin{code}

open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness fe

noncontinuous-map-gives-WLPO
 : (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
 → WLPO
noncontinuous-map-gives-WLPO (f , f-non-cts)
 = VI
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

Added 7th September 2024. We now prove (3)(→).

\begin{code}

¬WLPO-gives-all-functions-are-not-not-continuous
 : ¬ WLPO
 → (f : ℕ∞ → ℕ)
 → ¬¬ continuous f
¬WLPO-gives-all-functions-are-not-not-continuous nwlpo f
 = contrapositive
    (λ (ν : ¬ continuous f) → noncontinuous-map-gives-WLPO (f , ν))
    nwlpo

\end{code}

And now we prove (1).

\begin{code}

MP-gives-that-not-not-continuous-functions-are-continuous
 : MP 𝓤₀
 → (f : ℕ∞ → ℕ)
 → ¬¬ continuous f
 → continuous f
MP-gives-that-not-not-continuous-functions-are-continuous mp f
 = mp (λ m → (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)
      (λ m → Theorem-8·2'
              (λ x → f (max (ι m) x) ＝ f ∞)
              (λ x → ℕ-is-discrete (f (max (ι m) x)) (f ∞)))

\end{code}

The converse of the above is trivial (double negation introduction)
and so we will not add it in code, even if it turns out to be needed
in future additions. The following also is an immediate consequence of
the above, but we choose to record it explicitly.

And now we prove (4). Assuming MP and ¬ WLPO, all functions ℕ∞ → ℕ are
continuous.

\begin{code}

MP-and-¬WLPO-give-that-all-functions-are-continuous
 : MP 𝓤₀
 → ¬ WLPO
 → (f : ℕ∞ → ℕ)
 → continuous f
MP-and-¬WLPO-give-that-all-functions-are-continuous mp nwlpo f
 = MP-gives-that-not-not-continuous-functions-are-continuous
    mp
    f
    (¬WLPO-gives-all-functions-are-not-not-continuous nwlpo f)

\end{code}

End of 7th September 2024 addition.

In the following fact we can replace Σ by ∃ because WLPO is a
proposition. Hence WLPO is the propositional truncation of the type
Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f.

TODO. Add code for this observation.

The following is from [1] with the same proof.

\begin{code}

open import Taboos.BasicDiscontinuity fe
open import Naturals.Properties

WLPO-gives-noncontinous-map
 : WLPO
 → (Σ f ꞉ (ℕ∞ → ℕ) , ¬ continuous f)
WLPO-gives-noncontinous-map wlpo
 = f , f-non-cts
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
          g ₀     ＝⟨refl⟩
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

\end{code}

And a corollary is that the negation of WLPO amounts to a weak
continuity principle that says that all functions are not-not
continuous.

\begin{code}

¬WLPO-iff-all-maps-are-¬¬-continuous
 : ¬ WLPO ↔ ((f : ℕ∞ → ℕ) → ¬¬ continuous f)
¬WLPO-iff-all-maps-are-¬¬-continuous
 = (λ nwlpo → curry (contrapositive noncontinuous-map-gives-WLPO nwlpo)) ,
   (λ (a : (f : ℕ∞ → ℕ) → ¬¬ continuous f)
     → contrapositive
        WLPO-gives-noncontinous-map
        (uncurry a))

\end{code}

It is shown in [3] that negative consistent axioms can be postulated
in MLTT without loss of canonicity, and Andreas Abel filled important
gaps and formalized this in Agda [4] using a logical-relations
technique. Hence we can, if we wish, postulate ¬ WLPO without loss of
canonicity, and get a weak continuity axiom for free. But notice that
we can also postulate ¬¬ WLPO without loss of continuity, to get a
weak classical axiom for free. Of course, we can't postulate both at
the same time while retaining canonicity (and consistency!).

[3] T. Coquand, N.A. Danielsson, M.H. Escardo, U. Norell and Chuangjie Xu.
Negative consistent axioms can be postulated without loss of canonicity.
https://www.cs.bham.ac.uk/~mhe/papers/negative-axioms.pdf

[4] Andreas Abel. Negative Axioms.
    https://github.com/andreasabel/logrel-mltt/tree/master/Application/NegativeAxioms

Added 16 August 2024. This is not in [1].

The above definition of continuity is "continuity at the point ∞", and
also it is not a proposition but rather data.

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

open import Naturals.ExitTruncation
open import UF.PropTrunc

module continuity-criteria (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open exit-truncations pt

 is-continuous : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-continuous f = ∃ m ꞉ ℕ , m is-modulus-of-continuity-of f

 module _ (f : ℕ∞ → ℕ) where

  continuity-data-gives-continuity-property
   : continuity-data f
   → is-continuous f
  continuity-data-gives-continuity-property
   = ∣_∣

  private
   δ : (m : ℕ) → is-decidable ((n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞)
   δ m = Theorem-8·2'
          (λ y → f (max (ι m) y) ＝ f ∞)
          (λ y → ℕ-is-discrete (f (max (ι m) y)) (f ∞))

  continuity-property-gives-continuity-data
   : is-continuous f
   → continuity-data f
  continuity-property-gives-continuity-data
   = exit-truncation (_is-modulus-of-continuity-of f) δ

\end{code}

Abbreviation.

\begin{code}

  cty-data = continuity-property-gives-continuity-data

\end{code}

The continuity data calculated above gives the minimal modulus of
continuity.

\begin{code}

  continuity-data-minimality
   : (c : is-continuous f)
     (m : ℕ)
   → m is-modulus-of-continuity-of f
   → modulus-of-continuity-of f (cty-data c) ≤ m
  continuity-data-minimality
   = exit-truncation-minimality (_is-modulus-of-continuity-of f) δ

\end{code}

Next, we show that continuity is equivalent to a more familiar notion
of continuity and also equivalent to the uniform version of the of the
more familiar version. We first work with the untruncated versions.

Notice that ι denotes the inclusion ℕ → ℕ∞ and also the inclusion
ℕ∞ → (ℕ → 𝟚), where the context has to be used to disambiguate.

We first define when two extended natural numbers x and y agree up to
precision k, written x ＝⟪ k ⟫ y.

\begin{code}

open import TypeTopology.Cantor

_＝⟪_⟫_ : ℕ∞ → ℕ → ℕ∞ → 𝓤₀ ̇
x ＝⟪ k ⟫ y = ι x ＝⟦ k ⟧ ι y

traditional-continuity-data
 : (ℕ∞ → ℕ) → 𝓤₀ ̇
traditional-continuity-data f
 = (x : ℕ∞) → Σ m ꞉ ℕ , ((y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

traditional-uniform-continuity-data
 : (ℕ∞ → ℕ) → 𝓤₀ ̇
traditional-uniform-continuity-data f
 = Σ m ꞉ ℕ , ((x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

\end{code}

We now need a lemma about the relation x ＝⟪ k ⟫ y.

\begin{code}

lemma₀
 : (k : ℕ)
   (n : ℕ)
 → ∞ ＝⟪ k ⟫ (max (ι k) (ι n))
lemma₀ 0        n        = ⋆
lemma₀ (succ k) 0        = refl , lemma₀ k 0
lemma₀ (succ k) (succ n) = refl , lemma₀ k n

module _ (f : ℕ∞ → ℕ) where

 traditional-uniform-continuity-data-gives-traditional-continuity-data
  : traditional-uniform-continuity-data f
  → traditional-continuity-data f
 traditional-uniform-continuity-data-gives-traditional-continuity-data
  (m , m-is-modulus) x = m , m-is-modulus x

 traditional-continuity-data-gives-continuity-data
  : traditional-continuity-data f
  → continuity-data f
 traditional-continuity-data-gives-continuity-data f-cts-traditional
  = II
  where
   m : ℕ
   m = pr₁ (f-cts-traditional ∞)

   m-is-modulus : (y : ℕ∞) → ∞ ＝⟪ m ⟫ y → f ∞ ＝ f y
   m-is-modulus = pr₂ (f-cts-traditional ∞)

   I : (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞
   I n = (m-is-modulus (max (ι m) (ι n)) (lemma₀ m n))⁻¹

   II : continuous f
   II = m , I

\end{code}

We now need more lemmas about the relation x ＝⟪ k ⟫ y.

\begin{code}

 lemma₁
  : (k : ℕ)
    (y : ℕ∞)
  → ∞ ＝⟪ k ⟫ y
  → max (ι k) y ＝ y
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

 lemma₂
  : (x y : ℕ∞)
    (k : ℕ)
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

 lemma₃
  : (x y : ℕ∞)
    (k : ℕ)
  → x ＝⟪ k ⟫ y
  → (x ＝ y) + (max (ι k) x ＝ x) × (max (ι k) y ＝ y)
 lemma₃ x y k e
  = III
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
  (m , m-is-modulus) = m , m-is-modulus'
  where
   qₙ : (n : ℕ) → f (max (ι m) (ι n)) ＝ f ∞
   qₙ = m-is-modulus

   I : (z : ℕ∞) → max (ι m) z ＝ z → f z ＝ f ∞
   I z p = γ
    where
     q∞ : f (max (ι m) ∞) ＝ f ∞
     q∞ = ap f (max∞-property' fe (ι m))

     q : (u : ℕ∞) → f (max (ι m) u) ＝ f ∞
     q = ℕ∞-density fe ℕ-is-¬¬-separated qₙ q∞

     γ = f z             ＝⟨ ap f (p ⁻¹) ⟩
         f (max (ι m) z) ＝⟨ q z ⟩
         f ∞             ∎

   m-is-modulus' : (x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y
   m-is-modulus' x y e =
    Cases (lemma₃ x y m e)
     (λ (p : x ＝ y) → ap f p)
     (λ (q , r) → f x ＝⟨ I x q ⟩
                  f ∞ ＝⟨ I y r ⁻¹ ⟩
                  f y ∎)

\end{code}

This closes a circle, so that that all notions of continuity data are
logically equivalent.

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

 is-traditionally-continuous
  : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-traditionally-continuous f
  = (x : ℕ∞) → ∃ m ꞉ ℕ , ((y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

 is-traditionally-uniformly-continuous
  : (ℕ∞ → ℕ) → 𝓤₀ ̇
 is-traditionally-uniformly-continuous f
  = ∃ m ꞉ ℕ , ((x y : ℕ∞) → x ＝⟪ m ⟫ y → f x ＝ f y)

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

The type `ℕ∞-extensions-of g`, formally defined below, is that of all
extensions of g : ℕ → ℕ to functions ℕ∞ → ℕ.

Our first question is when this type is a proposition, so that it
could be called `is-ℕ∞-extendable g`.

Notice that LPO is stronger than WLPO, and hence, by taking the
contrapositive, ¬ WLPO is stronger than ¬ LPO:

     LPO →  WLPO
  ¬ WLPO → ¬ LPO

\begin{code}

restriction : (ℕ∞ → ℕ) → (ℕ → ℕ)
restriction f = f ∘ ι

_extends_ : (ℕ∞ → ℕ) → (ℕ → ℕ) → 𝓤₀ ̇
f extends g = restriction f ∼ g

ℕ∞-extensions-of : (ℕ → ℕ) → 𝓤₀ ̇
ℕ∞-extensions-of g = Σ f ꞉ (ℕ∞ → ℕ) , f extends g

\end{code}

The following says that if all functions ℕ∞ → ℕ are continuous, or,
more generally, if just ¬ WLPO holds, then the type of ℕ∞-extensions
of g has at most one element.

(In my view, this is a situation where it would be more sensible to
use the terminology `is-subsingleton` rather than `is-prop`. In fact,
I generally prefer the former terminology over the latter, but here we
try to be consistent with the terminology of the HoTT/UF community.)

\begin{code}

¬WLPO-gives-ℕ∞-extensions-is-prop
 : funext 𝓤₀ 𝓤₀
 → (g : ℕ → ℕ)
 → ¬ WLPO
 → is-prop (ℕ∞-extensions-of g)
¬WLPO-gives-ℕ∞-extensions-is-prop fe g nwlpo (f , e) (f' , e')
 = IV
 where
  I : (n : ℕ) → f (ι n) ＝ f' (ι n)
  I n = f (ι n)  ＝⟨ e n ⟩
        g n      ＝⟨ (e' n)⁻¹ ⟩
        f' (ι n) ∎

  II : f ∞ ＝ f' ∞
  II = agreement-cotaboo' ℕ-is-discrete nwlpo f f' I

  III : f ∼ f'
  III = ℕ∞-density fe ℕ-is-¬¬-separated I II

  IV : (f , e) ＝ (f' , e')
  IV = to-subtype-＝ (λ - → Π-is-prop fe (λ n → ℕ-is-set)) (dfunext fe III)

\end{code}

Therefore the non-propositionality of the type `ℕ∞-extensions-of g`
gives the classical principle ¬¬ WLPO.

\begin{code}

the-type-of-ℕ∞-extensions-is-not-prop-gives-¬¬WLPO
 : funext 𝓤₀ 𝓤₀
 → (g : ℕ → ℕ)
 → ¬ is-prop (ℕ∞-extensions-of g)
 → ¬¬ WLPO
the-type-of-ℕ∞-extensions-is-not-prop-gives-¬¬WLPO fe g
 = contrapositive (¬WLPO-gives-ℕ∞-extensions-is-prop fe g)

\end{code}

We are unable, at the time of writing (4th September 2024) to
establish the converse.  However, if we strengthen the classical
principle ¬¬ WLPO to LPO, we can. We begin with a classical extension
lemma, which is then applied to prove this claim.

If LPO holds, then for any g : ℕ → ℕ and y : ℕ there is an extension
f : ℕ∞ → ℕ of g that maps ∞ to y.

\begin{code}

LPO-gives-ℕ∞-extension
 : LPO
 → (g : ℕ → ℕ)
   (y : ℕ)
 → Σ (f , _) ꞉ ℕ∞-extensions-of g , (f ∞ ＝ y)
LPO-gives-ℕ∞-extension lpo g y
 = (f , e) , p
 where
  F : (x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , x ＝ ι n) → ℕ
  F x (inl (n , p)) = g n
  F x (inr ν)       = y

  f : ℕ∞ → ℕ
  f x = F x (lpo x)

  E : (k : ℕ) (d : is-decidable (Σ n ꞉ ℕ , ι k ＝ ι n)) → F (ι k) d ＝ g k
  E k (inl (n , p)) = ap g (ℕ-to-ℕ∞-lc (p ⁻¹))
  E k (inr ν)       = 𝟘-elim (ν (k , refl))

  e : restriction f ∼ g
  e k = E k (lpo (ι k))

  P : (d : is-decidable (Σ n ꞉ ℕ , ∞ ＝ ι n)) → F ∞ d ＝ y
  P (inl (n , p)) = 𝟘-elim (∞-is-not-finite n p)
  P (inr _)       = refl

  p : f ∞ ＝ y
  p = P (lpo ∞)

\end{code}

If LPO holds, a function g : ℕ → ℕ can have many extensions to ℕ∞.

\begin{code}

LPO-gives-that-the-type-of-ℕ∞-extension-is-not-prop
 : (g : ℕ → ℕ)
 → LPO
 → ¬ is-prop (ℕ∞-extensions-of g)
LPO-gives-that-the-type-of-ℕ∞-extension-is-not-prop g lpo ext-is-prop
  = I (LPO-gives-ℕ∞-extension lpo g 0) (LPO-gives-ℕ∞-extension lpo g 1)
 where
  I : (Σ (f , _) ꞉ ℕ∞-extensions-of g , (f ∞ ＝ 0))
    → (Σ (f , _) ꞉ ℕ∞-extensions-of g , (f ∞ ＝ 1))
    → 𝟘
  I ((f , e) , p) ((f' , e') , p') =
   zero-not-positive 0
    (0    ＝⟨ p ⁻¹ ⟩
     f  ∞ ＝⟨ ap ((λ (- , _) → - ∞)) (ext-is-prop (f , e) (f' , e')) ⟩
     f' ∞ ＝⟨ p' ⟩
     1    ∎)

\end{code}

It is direct that if there is at most one extension, then LPO can't
hold.

\begin{code}

type-of-ℕ∞-extensions-is-prop-gives-¬LPO
 : (g : ℕ → ℕ)
 → is-prop (ℕ∞-extensions-of g)
 → ¬ LPO
type-of-ℕ∞-extensions-is-prop-gives-¬LPO g i lpo
 = LPO-gives-that-the-type-of-ℕ∞-extension-is-not-prop g lpo i

\end{code}

So we have the chain of implications

    ¬ WLPO → is-prop (ℕ∞-extensions-of g) → ¬ LPO.

Recall that LPO → WLPO, and so ¬ WLPO → ¬ LPO in any case. We don't
know whether the implication ¬ WLPO → ¬ LPO can be reversed in general
(we would guess not).

We also have the chain of implications

    LPO → ¬ is-prop (ℕ∞-extensions-of g) → ¬¬ WLPO.

So the type ¬ is-prop (ℕ∞-extensions-of g) sits between two
constructive taboos and so is an inherently classical statement.

Added 4th September 2024.

Our next question is when the type `ℕ∞-extensions-of g` is pointed.

For this purpose, we consider the notion of eventually constant
function ℕ → ℕ.

\begin{code}

_is-modulus-of-constancy-of_ : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
m is-modulus-of-constancy-of g = (n : ℕ) → g (maxℕ m n) ＝ g m

being-modulus-of-constancy-is-prop
 : (g : ℕ → ℕ)
   (m : ℕ)
 → is-prop (m is-modulus-of-constancy-of g)
being-modulus-of-constancy-is-prop g m
 = Π-is-prop fe (λ n → ℕ-is-set)

eventually-constant : (ℕ → ℕ) → 𝓤₀ ̇
eventually-constant g = Σ m ꞉ ℕ , m is-modulus-of-constancy-of g

\end{code}

The above is not really property of g but actually data for g, and
sometimes it will be useful to emphasize the distinction in the code.

\begin{code}

eventual-constancy-data = eventually-constant

\end{code}

It will be convenient to give readable names for the projections.

\begin{code}

mod-const-of : (g : ℕ → ℕ) → eventually-constant g → ℕ
mod-const-of g = pr₁

modulus-of-constancy-property
 : {g : ℕ → ℕ}
   (c : eventually-constant g)
 → (mod-const-of g c) is-modulus-of-constancy-of g
modulus-of-constancy-property = pr₂

\end{code}

Any modulus of constancy of a function g : ℕ → ℕ is a modulus of
continuity of a continuous extension f : ℕ∞ → ℕ of g.

\begin{code}

eventual-constancy-data-gives-continuous-extension-data
 : (g : ℕ → ℕ)
   ((m , _) : eventually-constant g)
 → Σ (f , _) ꞉ ℕ∞-extensions-of g , m is-modulus-of-continuity-of f
eventual-constancy-data-gives-continuous-extension-data g (m , a)
 = h g m a
 where
  h : (g : ℕ → ℕ)
      (m : ℕ)
    → m is-modulus-of-constancy-of g
    → Σ (f , _) ꞉ ℕ∞-extensions-of g , m is-modulus-of-continuity-of f
  h g 0        a = ((λ _ → g 0) ,
                    (λ n →  g 0          ＝⟨ (a n)⁻¹ ⟩
                            g (maxℕ 0 n) ＝⟨refl⟩
                            g n          ∎)) ,
                   (λ n → refl)
  h g (succ m) a = I IH
   where
    IH : Σ (f , _) ꞉ ℕ∞-extensions-of (g ∘ succ) , m is-modulus-of-continuity-of f
    IH = h (g ∘ succ) m (a ∘ succ)

    I : type-of IH
      → Σ (f' , _) ꞉ ℕ∞-extensions-of g , (succ m) is-modulus-of-continuity-of f'
    I ((f , e) , m-is-modulus)
     = (f' , e') , succ-m-is-modulus
     where
      f' : ℕ∞ → ℕ
      f' = ℕ∞-cases fe (g 0) f

      e' : (n : ℕ) → f' (ι n) ＝ g n
      e' 0 = f' (ι 0) ＝⟨refl⟩
             f' Zero  ＝⟨ ℕ∞-cases-Zero fe (g 0) f ⟩
             g 0      ∎
      e' (succ n) = f' (ι (succ n)) ＝⟨refl⟩
                    f' (Succ (ι n)) ＝⟨ ℕ∞-cases-Succ fe (g 0) f (ι n) ⟩
                    f (ι n)         ＝⟨ e n ⟩
                    g (succ n)      ∎

      succ-m-is-modulus : (n : ℕ) → f' (max (ι (succ m)) (ι n)) ＝ f' ∞
      succ-m-is-modulus 0        = m-is-modulus 0
      succ-m-is-modulus (succ n) =
       f' (max (ι (succ m)) (ι (succ n))) ＝⟨ II ⟩
       f' (Succ (max (ι m) (ι n)))        ＝⟨ III ⟩
       f (max (ι m) (ι n))                ＝⟨ IV ⟩
       f ∞                                ＝⟨ V ⟩
       f' (Succ ∞)                        ＝⟨ VI ⟩
       f' ∞                               ∎
        where
         II  = ap f' ((max-Succ fe (ι m) (ι n))⁻¹)
         III = ℕ∞-cases-Succ fe (g 0) f (max (ι m) (ι n))
         IV  = m-is-modulus n
         V   = (ℕ∞-cases-Succ fe (g 0) f ∞)⁻¹
         VI  = ap f' (Succ-∞-is-∞ fe)

\end{code}

It will be convenient name various projections of the above
construction.

\begin{code}

evc-extension
 : (g : ℕ → ℕ)
 → eventually-constant g
 → ℕ∞ → ℕ
evc-extension g c
 = pr₁ (pr₁ (eventual-constancy-data-gives-continuous-extension-data g c))

evc-extension-property
 : (g : ℕ → ℕ)
   (c : eventually-constant g)
 → (evc-extension g c) extends g
evc-extension-property g c
 = pr₂ (pr₁ (eventual-constancy-data-gives-continuous-extension-data g c))

evc-extension-modulus-of-continuity
 : (g : ℕ → ℕ)
   (c@(m , _) : eventually-constant g)
 → m is-modulus-of-continuity-of (evc-extension g c)
evc-extension-modulus-of-continuity g c@(m , _)
 = pr₂ (eventual-constancy-data-gives-continuous-extension-data g c)

\end{code}

With this notation, we have that the above extension of any eventually
constant function ℕ → ℕ is continuous.

\begin{code}

evc-extension-continuity
 : (g : ℕ → ℕ)
   (c : eventually-constant g)
 → continuous (evc-extension g c)
evc-extension-continuity g c@(m , _)
 = m , evc-extension-modulus-of-continuity g c

\end{code}

Later we will need the fact that the value of the extension at ∞ is
g m, where m is the modulus of constancy of g.

\begin{code}

evc-extension-∞
 : (g : ℕ → ℕ)
   (c@(m , _) : eventually-constant g)
 → evc-extension g c ∞ ＝ g m
evc-extension-∞ g c@(m , a)
 = f ∞                 ＝⟨ (evc-extension-modulus-of-continuity g c m)⁻¹ ⟩
   f (max (ι m) (ι m)) ＝⟨ ap f (max-idemp fe (ι m)) ⟩
   f (ι m)             ＝⟨ evc-extension-property g c m ⟩
   g m                 ∎
 where
  f : ℕ∞ → ℕ
  f = evc-extension g c

\end{code}

The extension of the restriction of a function equipped with
continuity data is the original function.

Notice that, in the following, c can be derived from d, but, in uses
of this, it will be convenient to have them both given, as they are
obtained separately.

Notice also that this is not entirely trivial. It uses a density lemma
proved in another module.

\begin{code}

evc-extension-restriction
 : (f : ℕ∞ → ℕ)
   (d : continuity-data f)
   (c : eventual-constancy-data (restriction f))
 → evc-extension (restriction f) c ∼ f
evc-extension-restriction f
                          d@(n , n-is-modulus-of-continuity)
                          c@(m , m-is-modulus-of-constancy)
 = III
 where
  I : (n : ℕ) → evc-extension (restriction f) c (ι n) ＝ f (ι n)
  I = evc-extension-property (restriction f) c

  II = evc-extension (restriction f) c ∞ ＝⟨ evc-extension-∞ (restriction f) c ⟩
       f (ι m)                           ＝⟨ (m-is-modulus-of-constancy n)⁻¹ ⟩
       f (ι (maxℕ m n))                  ＝⟨ ap (f ∘ ι) (maxℕ-comm m n) ⟩
       f (ι (maxℕ n m))                  ＝⟨ ap f (max-fin fe n m) ⟩
       f (max (ι n) (ι m))               ＝⟨ n-is-modulus-of-continuity m ⟩
       f ∞                               ∎

  III : evc-extension (restriction f) c ∼ f
  III = ℕ∞-density fe ℕ-is-¬¬-separated I II

\end{code}

Conversely, a modulus of continuity of an extension is a modulus of
constancy of the orginal function.

\begin{code}

continuous-extension-gives-eventual-constancy'
 : (g : ℕ → ℕ)
   ((f , _) : ℕ∞-extensions-of g)
   (m : ℕ)
 → m is-modulus-of-continuity-of f
 → m is-modulus-of-constancy-of g
continuous-extension-gives-eventual-constancy' g (f , e) m  m-is-modulus
 = (λ n → g (maxℕ m n)        ＝⟨ (e (maxℕ m n))⁻¹ ⟩
          f (ι (maxℕ m n))    ＝⟨ ap f (max-fin fe m n) ⟩
          f (max (ι m) (ι n)) ＝⟨ m-is-modulus n ⟩
          f ∞                 ＝⟨ (m-is-modulus m)⁻¹ ⟩
          f (max (ι m) (ι m)) ＝⟨ ap f (max-idemp fe (ι m)) ⟩
          f (ι m)             ＝⟨ e m ⟩
          g m                 ∎)

\end{code}

In other words, any modulus of continuity of a function ℕ∞ → ℕ is a
modulus of constancy of its restriction ℕ → ℕ.

\begin{code}

restriction-modulus
 : (f : ℕ∞ → ℕ)
   (m : ℕ)
 → m is-modulus-of-continuity-of f
 → m is-modulus-of-constancy-of (restriction f)
restriction-modulus f
 = continuous-extension-gives-eventual-constancy'
    (restriction f)
    (f , (λ x → refl))

\end{code}

And so continuity data for the extension gives eventual constancy data
for the original function, which can be formulated in two ways.

\begin{code}

continuous-extension-gives-eventual-constancy
 : (g : ℕ → ℕ)
   ((f , _) : ℕ∞-extensions-of g)
 → continuous f
 → eventually-constant g
continuous-extension-gives-eventual-constancy g ext (m , m-is-modulus)
 = m , continuous-extension-gives-eventual-constancy' g ext m m-is-modulus

restriction-of-continuous-function-has-evc-data
 : (f : ℕ∞ → ℕ)
 → continuous f
 → eventually-constant (restriction f)
restriction-of-continuous-function-has-evc-data f
 = continuous-extension-gives-eventual-constancy
    (restriction f)
    (f , (λ x → refl))

\end{code}

Is there a nice necessary and sufficient condition for the
extendability of any such given g?

A sufficient condition is that LPO holds or g is eventually constant.

\begin{code}

ℕ∞-extension-explicit-existence-sufficient-condition
 : (g : ℕ → ℕ)
 → LPO + eventually-constant g
 → ℕ∞-extensions-of g
ℕ∞-extension-explicit-existence-sufficient-condition g (inl lpo)
 = pr₁ (LPO-gives-ℕ∞-extension lpo g 0)
ℕ∞-extension-explicit-existence-sufficient-condition g (inr ec)
 = pr₁ (eventual-constancy-data-gives-continuous-extension-data g ec)

\end{code}

Its contrapositive says that if g doesn't have an extension, then
neither LPO holds nor g is eventually constant.

\begin{code}

ℕ∞-extension-nonexistence-gives-¬LPO-and-not-eventual-constancy
 : (g : ℕ → ℕ)
 → ¬ ℕ∞-extensions-of g
 → ¬ LPO × ¬ eventually-constant g
ℕ∞-extension-nonexistence-gives-¬LPO-and-not-eventual-constancy g ν
 = I ∘ inl , I ∘ inr
 where
  I : ¬ (LPO + eventually-constant g)
  I = contrapositive (ℕ∞-extension-explicit-existence-sufficient-condition g) ν

\end{code}

A necessary condition is that WLPO holds or that g is not-not
eventually constant.

\begin{code}

ℕ∞-extension-explicit-existence-first-necessary-condition
 : (g : ℕ → ℕ)
 → ℕ∞-extensions-of g
 → WLPO + ¬¬ eventually-constant g
ℕ∞-extension-explicit-existence-first-necessary-condition
 g (f , e) = III
 where
  II : is-decidable (¬ continuous f) → WLPO + ¬¬ eventually-constant g
  II (inl l) = inl (noncontinuous-map-gives-WLPO (f , l))
  II (inr r) = inr (¬¬-functor
                     (continuous-extension-gives-eventual-constancy g (f , e)) r)

  III : WLPO + ¬¬ eventually-constant g
  III = II (the-negation-of-continuity-is-decidable f)

\end{code}

Its contrapositive says that if WLPO fails and g is not eventually
constant, then there isn't any extension.

\begin{code}

¬WLPO-gives-that-non-eventually-constant-functions-have-no-extensions
 : (g : ℕ → ℕ)
 → ¬ WLPO
 → ¬ eventually-constant g
 → ¬ ℕ∞-extensions-of g
¬WLPO-gives-that-non-eventually-constant-functions-have-no-extensions g nwlpo nec
 = contrapositive
    (ℕ∞-extension-explicit-existence-first-necessary-condition g)
    (cases nwlpo (¬¬-intro nec))

\end{code}

Because LPO implies WLPO and A implies ¬¬ A for any mathematical
statement A, we have that

  (LPO + eventually-constant g) implies (WLPO + ¬¬ eventually-constant g).

TODO. Is there a nice necessary and sufficient condition for the
      explicit existence of an extension, between the respectively
      necessary and sufficient conditions

        WLPO + ¬¬ eventually-constant g

      and

        LPO + eventually-constant g?

      We leave this open. However, we show below that, under Markov's
      Principle, the latter is a necessary and sufficient for g to
      have an extension.

\end{code}

Added 9th September 2023. A second necessary condition for the
explicit existence of an extension.

Notice that, because the condition

  (n : ℕ) → g (maxℕ m n) ＝ g m

is not a priori decidable, as this implies WLPO if it holds for all m
and g, the type of eventual constancy data doesn't in general have
split support.

However, if a particular g has an extension to ℕ∞, then this condition
becomes decidable, and so in this case this type does have split
support.

Notice that this doesn't require the eventual constancy of g. It just
requires that g has some (not necessarily continuous) extension.

\begin{code}

being-modulus-of-constancy-is-decidable-for-all-functions-gives-WLPO
 : ((g : ℕ → ℕ) (m : ℕ)
       → is-decidable (m is-modulus-of-constancy-of g))
 → WLPO
being-modulus-of-constancy-is-decidable-for-all-functions-gives-WLPO ϕ
 = WLPO-traditional-gives-WLPO fe (WLPO-variation₁-gives-WLPO-traditional I)
 where
  I : WLPO-variation₁
  I α = I₂
   where
    g : ℕ → ℕ
    g = ι ∘ α

    I₀ : ((n : ℕ) → ι (α (maxℕ 0 n)) ＝ ι (α 0))
       → (n : ℕ) → α n ＝ α 0
    I₀ a n = 𝟚-to-ℕ-is-lc (a n)

    I₁ : ((n : ℕ) → α n ＝ α 0)
       → (n : ℕ) → ι (α (maxℕ 0 n)) ＝ ι (α 0)
    I₁ b n = ι (α (maxℕ 0 n)) ＝⟨refl⟩
             ι (α n)          ＝⟨ ap ι (b n) ⟩
             ι (α 0)          ∎

    I₂ : is-decidable ((n : ℕ) → α n ＝ α 0)
    I₂ = map-decidable I₀ I₁ (ϕ g 0)

\end{code}

Although it is not decidable in general whether a given m : ℕ is a
modulus of (eventual) constancy of g, this is decidable if g has some
given extension (regardless of whether this extension is continuous or
not)

\begin{code}

second-necessary-condition-for-the-explicit-existence-of-an-extension
 : (g : ℕ → ℕ)
 → ℕ∞-extensions-of g
 → (m : ℕ) → is-decidable (m is-modulus-of-constancy-of g)
second-necessary-condition-for-the-explicit-existence-of-an-extension g (f , e) m
 = IV
 where
  I : is-decidable ((n : ℕ) → f (max (ι m) (ι n)) ＝ f (ι m))
  I = Theorem-8·2'
       (λ x → f (max (ι m) x) ＝ f (ι m))
       (λ x → ℕ-is-discrete (f (max (ι m) x)) (f (ι m)))

  II : ((n : ℕ) → f (max (ι m) (ι n)) ＝ f (ι m))
     → m is-modulus-of-constancy-of g
  II a n = g (maxℕ m n)        ＝⟨ e (maxℕ m n) ⁻¹ ⟩
           f (ι (maxℕ m n))    ＝⟨ ap f (max-fin fe m n) ⟩
           f (max (ι m) (ι n)) ＝⟨ a n ⟩
           f (ι m)             ＝⟨ e m ⟩
           g m                 ∎

  III : m is-modulus-of-constancy-of g
      → (n : ℕ) → f (max (ι m) (ι n)) ＝ f (ι m)
  III b n = f (max (ι m) (ι n)) ＝⟨ ap f ((max-fin fe m n)⁻¹) ⟩
            f (ι (maxℕ m n))    ＝⟨ e (maxℕ m n) ⟩
            g (maxℕ m n)        ＝⟨ b n ⟩
            g m                 ＝⟨ e m ⁻¹ ⟩
            f (ι m)             ∎

  IV : is-decidable (m is-modulus-of-constancy-of g)
  IV = map-decidable II III I

\end{code}

So, although a function g that has an extension doesn't need to be
eventually constant, because classical logic may (or may not) hold, it
is decidable whether any given m is a modulus of eventual constancy of g
if g has a given extension.

We now discuss extendability as property rather than data.

\begin{code}

module eventual-constancy-under-propositional-truncations
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt
 open exit-truncations pt

 is-extendable-to-ℕ∞
  : (ℕ → ℕ) → 𝓤₀ ̇
 is-extendable-to-ℕ∞ g
  = ∃ f ꞉ (ℕ∞ → ℕ) , f extends g

 is-eventually-constant
  : (ℕ → ℕ) → 𝓤₀ ̇
 is-eventually-constant g
  = ∃ m ꞉ ℕ , m is-modulus-of-constancy-of g

\end{code}

As promised, any extension of g gives that the type of eventual
constancy data has split support if g has at least one explicitly
given extension.

\begin{code}

 eventual-constancy-data-for-extendable-functions-has-split-support
  : (g : ℕ → ℕ)
  → ℕ∞-extensions-of g
  → is-eventually-constant g
  → eventual-constancy-data g
 eventual-constancy-data-for-extendable-functions-has-split-support g extension
  = exit-truncation
     (λ m → (n : ℕ) → g (maxℕ m n) ＝ g m)
     (second-necessary-condition-for-the-explicit-existence-of-an-extension
       g
       extension)

\end{code}

A more general result is proved below, which doesn't assume that g has
an extension.

The second necessary condition for the explicit existence of an
extension is also necessary for the anonymous existence.

\begin{code}

 necessary-condition-for-the-anonymous-existence-of-an-extension
  : (g : ℕ → ℕ)
  → is-extendable-to-ℕ∞ g
  → (m : ℕ) → is-decidable (m is-modulus-of-constancy-of g)
 necessary-condition-for-the-anonymous-existence-of-an-extension g
  = ∥∥-rec
     (Π-is-prop fe
       (λ n → decidability-of-prop-is-prop fe
               (being-modulus-of-constancy-is-prop g n)))
     (second-necessary-condition-for-the-explicit-existence-of-an-extension g)

\end{code}

The following is immediate, and we need its reformulation given after
it.

\begin{code}

 open continuity-criteria pt

 is-continuous-extension-gives-is-eventually-constant
  : (g : ℕ → ℕ)
    ((f , _) : ℕ∞-extensions-of g)
  → is-continuous f
  → is-eventually-constant g
 is-continuous-extension-gives-is-eventually-constant  g e
  = ∥∥-functor (continuous-extension-gives-eventual-constancy g e)

 restriction-of-continuous-function-is-eventually-constant
  : (f : ℕ∞ → ℕ)
  → is-continuous f
  → is-eventually-constant (restriction f)
 restriction-of-continuous-function-is-eventually-constant f
  = ∥∥-functor (restriction-of-continuous-function-has-evc-data f)

\end{code}

Added 10th September 2024. We should have added this immediate
consequence earlier. If all maps ℕ → ℕ can be extended to ℕ∞, then
WLPO holds. Just consider the identity function, which can't have any
continuous extension, and so deduce WLPO.

\begin{code}

all-maps-have-extensions-gives-WLPO
 : ((g : ℕ → ℕ) → ℕ∞-extensions-of g)
 → WLPO
all-maps-have-extensions-gives-WLPO a
 = I (a id)
 where
  I : ℕ∞-extensions-of id → WLPO
  I (f , e) = noncontinuous-map-gives-WLPO (f , ν)
   where
    ν : ¬ continuous f
    ν (m , m-is-modulus) =
     succ-no-fp m
      (m                          ＝⟨refl⟩
       id m                       ＝⟨ (e m)⁻¹ ⟩
       f (ι m)                    ＝⟨ ap f ((max-idemp fe (ι m))⁻¹) ⟩
       f (max (ι m) (ι m))        ＝⟨ m-is-modulus m ⟩
       f ∞                        ＝⟨ (m-is-modulus (succ m))⁻¹ ⟩
       f (max (ι m) (ι (succ m))) ＝⟨ ap f (max-succ fe m) ⟩
       f (ι (succ m))             ＝⟨ e (succ m) ⟩
       id (succ m)                ＝⟨refl⟩
       succ m                     ∎)

\end{code}

Added 11th September 2024. Another immediate consequence of the above
is that, under Markov's Principle, a map ℕ → ℕ has an extension ℕ∞ → ℕ
if and only if LPO holds or g is eventually constant.

\begin{code}

decidability-of-modulus-of-constancy-gives-eventual-constancy-¬¬-stable
 : MP 𝓤₀
 → (g : ℕ → ℕ)
 → ((m : ℕ) → is-decidable (m is-modulus-of-constancy-of g))
 → ¬¬ eventually-constant g
 → eventually-constant g
decidability-of-modulus-of-constancy-gives-eventual-constancy-¬¬-stable mp g
 =  mp (_is-modulus-of-constancy-of g)

sufficient-condition-is-necessary-under-MP
 : MP 𝓤₀
 → (g : ℕ → ℕ)
 → ℕ∞-extensions-of g
 → LPO + eventually-constant g
sufficient-condition-is-necessary-under-MP mp g ext
 = II
 where
  I : WLPO + ¬¬ eventually-constant g → LPO + eventually-constant g
  I = +functor
       (MP-and-WLPO-give-LPO fe mp)
       (decidability-of-modulus-of-constancy-gives-eventual-constancy-¬¬-stable
         mp
         g
         (second-necessary-condition-for-the-explicit-existence-of-an-extension
           g
           ext))

  II : LPO + eventually-constant g
  II = I (ℕ∞-extension-explicit-existence-first-necessary-condition g ext)

necessary-and-sufficient-condition-for-explicit-extension-under-MP
 : MP 𝓤₀
 → (g : ℕ → ℕ)
 → ℕ∞-extensions-of g ↔ LPO + eventually-constant g
necessary-and-sufficient-condition-for-explicit-extension-under-MP mp g
 = sufficient-condition-is-necessary-under-MP mp g ,
   ℕ∞-extension-explicit-existence-sufficient-condition g

\end{code}

TODO. Find a necessary and sufficient condition without assuming
Markov's Principle. We leave this as an open problem.

Added 18th September 2024. There is another way of looking at the
above development, which gives rise to a further question.

We have the restriction map (ℕ∞ → ℕ) → (ℕ → ℕ) defined above
as restriction f ＝ f ∘ ι.

For any map f : X → Y we have that

 X ≃ Σ y ꞉ Y , Σ x ꞉ X , f x ＝ y
   ＝ Σ y ꞉ Y , fiber f y.

With X = (ℕ∞ → ℕ) and Y = (ℕ → ℕ) and f = restriction, the definition
of _extends_, together with the fact that _∼_ coincides with _＝_
under function extensionality, the above specializes to

 (ℕ∞ → ℕ) ≃ Σ g ꞉ (ℕ → ℕ) , Σ f ꞉ (ℕ∞ → ℕ) , f ∘ ι ＝ g
          ≃ Σ g ꞉ (ℕ → ℕ) , Σ f ꞉ (ℕ∞ → ℕ) , restriction f ∼ g
          ≃ Σ g ꞉ (ℕ → ℕ) , Σ f ꞉ (ℕ∞ → ℕ) , f extends g
          ≃ Σ g ꞉ (ℕ → ℕ) , ℕ-extension g

The above characterizes the type "ℕ-extension g" up to logical
equivalence, under the assumption of Markov's Principle.

TODO. Is there a nice characterization "Nice g" of the type
"ℕ-extension g", preferably without assuming MP, up to type
equivalence, rather than just logical equivalence, such that

 (ℕ∞ → ℕ) ≃ Σ g ꞉ (ℕ → ℕ) , Nice g?

The idea is that such a nice characterization should not mention ℕ∞,
and in some sense should be an "intrinsic" property of / data for g.

Added 25th September 2024. We now record the fact that

          (Σ f ꞉ (ℕ∞ → ℕ) , continuous f)
        ≃ (Σ g ꞉ (ℕ → ℕ)  , eventually-constant g).

\begin{code}

open import UF.EquivalenceExamples

characterization-of-type-of-untruncated-continuous-functions-≃
  : (Σ f ꞉ (ℕ∞ → ℕ) , continuous f)
  ≃ (Σ g ꞉ (ℕ → ℕ)  , eventually-constant g)
characterization-of-type-of-untruncated-continuous-functions-≃
  = II
  where
    I : (m : ℕ)
      → (Σ f ꞉ (ℕ∞ → ℕ) , m is-modulus-of-continuity-of f)
      ≃ (Σ g ꞉ (ℕ → ℕ)  , m is-modulus-of-constancy-of  g)
    I m = ϕ , ϕ-is-equiv
     where
      ϕ : (Σ f ꞉ (ℕ∞ → ℕ) , m is-modulus-of-continuity-of f)
        → (Σ g ꞉ (ℕ → ℕ)  , m is-modulus-of-constancy-of  g)
      ϕ (f , mod-cty) = restriction f ,
                        restriction-modulus f m mod-cty

      γ : (Σ g ꞉ (ℕ → ℕ)  , m is-modulus-of-constancy-of  g)
        → (Σ f ꞉ (ℕ∞ → ℕ) , m is-modulus-of-continuity-of f)
      γ (g , mod-const) = evc-extension g (m , mod-const) ,
                          evc-extension-modulus-of-continuity g (m , mod-const)

      γϕ : γ ∘ ϕ ∼ id
      γϕ (f , mod-cty) = to-subtype-＝
                          (λ (- : ℕ∞ → ℕ) → being-modulus-of-continuity-is-prop - m)
                         (dfunext fe (evc-extension-restriction f d c))
       where
        c : eventual-constancy-data (restriction f)
        c = m , restriction-modulus f m mod-cty

        d : continuity-data f
        d = m , mod-cty

      ϕγ : ϕ ∘ γ ∼ id
      ϕγ (g , mod-const) = to-subtype-＝
                            (λ (- : ℕ → ℕ) → being-modulus-of-constancy-is-prop - m)
                            (dfunext fe (evc-extension-property g (m , mod-const)))

      ϕ-is-equiv : is-equiv ϕ
      ϕ-is-equiv = qinvs-are-equivs ϕ (γ , γϕ , ϕγ)

    II =
     (Σ f ꞉ (ℕ∞ → ℕ) , continuous f)                              ≃⟨by-definition⟩
     (Σ f ꞉ (ℕ∞ → ℕ) , Σ m ꞉ ℕ , m is-modulus-of-continuity-of f) ≃⟨ Σ-flip ⟩
     (Σ m ꞉ ℕ , Σ f ꞉ (ℕ∞ → ℕ) , m is-modulus-of-continuity-of f) ≃⟨ Σ-cong I ⟩
     (Σ m ꞉ ℕ , Σ g ꞉ (ℕ → ℕ) , m is-modulus-of-constancy-of g)   ≃⟨ Σ-flip ⟩
     (Σ g ꞉ (ℕ → ℕ) , Σ m ꞉ ℕ , m is-modulus-of-constancy-of g)   ≃⟨by-definition⟩
     (Σ g ꞉ (ℕ → ℕ), eventually-constant g)                       ■

\end{code}

Added 19th September 2024. We improve part of the above development
following a discussion and contributions at mathstodon by various
people

https://mathstodon.xyz/deck/@MartinEscardo/113024154634637479

\begin{code}

module eventual-constancy-under-propositional-truncations⁺
        (pt : propositional-truncations-exist)
       where

 open eventual-constancy-under-propositional-truncations pt
 open PropositionalTruncation pt
 open exit-truncations pt

\end{code}

Notice that the proofs below of modulus-down and modulus-up are not by
induction.

\begin{code}

 modulus-down
  : (g : ℕ → ℕ)
    (n : ℕ)
  → (succ n) is-modulus-of-constancy-of g
  → is-decidable (n is-modulus-of-constancy-of g)
 modulus-down g n μ = III
  where
   I : g (succ n) ＝ g n → n is-modulus-of-constancy-of g
   I e m =
    Cases (order-split n m)
     (λ (l : n < m)
     → g (maxℕ n m)        ＝⟨ ap g (max-ord→ n m (≤-trans _ _ _ (≤-succ n) l)) ⟩
       g m                 ＝⟨ ap g ((max-ord→ (succ n) m l)⁻¹) ⟩
       g (maxℕ (succ n) m) ＝⟨ μ m ⟩
       g (succ n)          ＝⟨ e ⟩
       g n                 ∎)
     (λ (l : m ≤ n)
     → g (maxℕ n m) ＝⟨ ap g (maxℕ-comm n m) ⟩
       g (maxℕ m n) ＝⟨ ap g (max-ord→ m n l) ⟩
       g n          ∎)

   II : n is-modulus-of-constancy-of g → g (succ n) ＝ g n
   II a = g (succ n)          ＝⟨ ap g ((max-ord→ n (succ n) (≤-succ n))⁻¹) ⟩
          g (maxℕ n (succ n)) ＝⟨ a (succ n) ⟩
          g n                 ∎

   III : is-decidable (n is-modulus-of-constancy-of g)
   III = map-decidable I II (ℕ-is-discrete (g (succ n)) (g n))

 modulus-up
   : (g : ℕ → ℕ)
     (n : ℕ)
   → n is-modulus-of-constancy-of g
   → (succ n) is-modulus-of-constancy-of g
 modulus-up g n μ m =
  g (maxℕ (succ n) m)          ＝⟨ ap g I ⟩
  g (maxℕ n (maxℕ (succ n) m)) ＝⟨ μ (maxℕ (succ n) m) ⟩
  g n                          ＝⟨ (μ (succ n))⁻¹ ⟩
  g (maxℕ n (succ n))          ＝⟨ ap g (max-ord→ n (succ n) (≤-succ n)) ⟩
  g (succ n)                   ∎
  where
   I : maxℕ (succ n) m ＝ maxℕ n (maxℕ (succ n) m)
   I = (max-ord→ n _
         (≤-trans _ _ _
           (≤-succ n)
           (max-ord← _ _
             (maxℕ (succ n) (maxℕ (succ n) m) ＝⟨ II ⟩
              maxℕ (maxℕ (succ n) (succ n)) m ＝⟨ III ⟩
              maxℕ (succ n) m                 ∎))))⁻¹
               where
                II  = (max-assoc (succ n) (succ n) m)⁻¹
                III = ap (λ - → maxℕ - m) (maxℕ-idemp (succ n))

\end{code}

Using this, although, as proved above, it is not decidable in general
whether a given n is a modulus of constancy of an arbitrary function
g : ℕ → ℕ, if we know that n is a modulus of continuity of g, then for
any k < n we have that it is decidable whether k is a modulus of
constancy of g.

\begin{code}

 conditional-decidability-of-being-modulus-of-constancy
  : (g : ℕ → ℕ)
    (n : ℕ)
  → n is-modulus-of-constancy-of g
  → (k : ℕ)
  → k < n
  → is-decidable (k is-modulus-of-constancy-of g)
 conditional-decidability-of-being-modulus-of-constancy g
  = regression-lemma
     (_is-modulus-of-constancy-of g)
     (modulus-down g)
     (modulus-up g)

\end{code}

A corollary of this is that the eventual constancy property gives
eventual constancy data.

\begin{code}

 eventual-constancy-property-gives-eventual-constancy-data
  : (g : ℕ → ℕ)
  → is-eventually-constant g
  → eventual-constancy-data g
 eventual-constancy-property-gives-eventual-constancy-data g
  = exit-truncation⁺
    (_is-modulus-of-constancy-of g)
    (being-modulus-of-constancy-is-prop g)
    (conditional-decidability-of-being-modulus-of-constancy g)

\end{code}

Abbreviation.

\begin{code}

 evc-data = eventual-constancy-property-gives-eventual-constancy-data

\end{code}

Moreover, the eventual constancy data calculated above gives the
minimal modulus of (eventual) constancy.

\begin{code}

 eventual-constancy-data-minimality
  : (g : ℕ → ℕ)
    (s : is-eventually-constant g)
    (m : ℕ)
  → m is-modulus-of-constancy-of g
  → mod-const-of g (evc-data g s) ≤ m
 eventual-constancy-data-minimality g
  = exit-truncation⁺-minimality
     (_is-modulus-of-constancy-of g)
     (being-modulus-of-constancy-is-prop g)
     (conditional-decidability-of-being-modulus-of-constancy g)

\end{code}

We now record the fact that the type of continuous functions ℕ∞ → ℕ is
equivalent to the type of eventually constant functions ℕ → ℕ, where
continuity and eventual constancy are formulated as property, rather
than data, as above.

We have shown above that

          (Σ f ꞉ (ℕ∞ → ℕ) , continuous f)
        ≃ (Σ g ꞉ (ℕ → ℕ)  , eventually-constant g).

It doesn't follow from general reasons that

          (Σ f ꞉ (ℕ∞ → ℕ) , ∥ continuous f ∥ )
        ≃ (Σ g ꞉ (ℕ → ℕ)  , ∥ eventually-constant g ∥).

In fact, for example, we have that 𝟚 × 𝟛 ≃ 𝟛 × 𝟚, but we don't have
that 𝟚 × ∥ 𝟛 ∥ ≃ 𝟛 × ∥ 𝟚 ∥, because ∥ 𝟛 ∥ ≃ 𝟙 ≃ ∥ 𝟚 ∥ and certainly it
isn't the case that 𝟚 × 𝟙 ≃ 𝟛 × 𝟙.

Nevertheless, although the above doesn't follow from the previous
result from general reasons, it does hold:

\begin{code}

 open continuity-criteria pt

 characterization-of-type-of-continuous-functions-≃'
  : (Σ f ꞉ (ℕ∞ → ℕ) , is-continuous f)
  ≃ (Σ g ꞉ (ℕ → ℕ)  , is-eventually-constant g)
 characterization-of-type-of-continuous-functions-≃'
  = ϕ , ϕ-is-equiv
  where
   ϕ : (Σ f ꞉ (ℕ∞ → ℕ) , is-continuous f)
     → (Σ g ꞉ (ℕ → ℕ), is-eventually-constant g)
   ϕ (f , f-cts) =
    restriction f ,
    restriction-of-continuous-function-is-eventually-constant f f-cts

   γ : (Σ g ꞉ (ℕ → ℕ), is-eventually-constant g)
     → (Σ f ꞉ (ℕ∞ → ℕ) , is-continuous f)
   γ (g , g-evc) = evc-extension g c , ∣ evc-extension-continuity g c ∣
    where
     c : eventual-constancy-data g
     c = evc-data g g-evc

   γϕ : γ ∘ ϕ ∼ id
   γϕ (f , f-cts) = to-subtype-＝
                     (λ _ → ∃-is-prop)
                     (dfunext fe I)
    where
     c : eventual-constancy-data (restriction f)
     c = evc-data
          (restriction f)
          (restriction-of-continuous-function-is-eventually-constant f f-cts)

     d : continuity-data f
     d = cty-data f f-cts

     I : evc-extension (restriction f) c ∼ f
     I = evc-extension-restriction f d c

   ϕγ : ϕ ∘ γ ∼ id
   ϕγ (g , g-evc) = to-subtype-＝
                     (λ _ → ∃-is-prop)
                     (dfunext fe I)
    where
     c : eventual-constancy-data g
     c = evc-data g g-evc

     I : restriction (evc-extension g c) ∼ g
     I = evc-extension-property g c

   ϕ-is-equiv : is-equiv ϕ
   ϕ-is-equiv = qinvs-are-equivs ϕ (γ , γϕ , ϕγ)

\end{code}

Added 20th September 2024.

I think that, in retrospect, it would have been a better idea to work
with minimal moduli of continuity and eventual constancy. In this way,
we never need to use propositional truncations, because the explicit
existence of minimal moduli, of continuity or eventual constancy, is
property rather than data (or property-like data, if you wish).

One possible idea is to do both, but instead take the primary
definitions of `is-continuous` and of `is-eventually-constant` using
minimality rather than propositional truncation, and then show that the
definitions using minimality are (logically and typally) equivalent.
