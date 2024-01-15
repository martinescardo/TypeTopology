The Cantor-Schröder-Bernstein Theorem for ∞-groupoids
-----------------------------------------------------

    Martín Hötzel Escardó
    6th February 2020
    School of Computer Science
    Birmingham Theory Group
    Lab Lunch Talk

    This talk has embedded Agda code.

    In the end I gave the talk in a whiteboard (without showing any
    Agda code). But it followed the script outlined in these "slides".

    I have also written a blog post that gives the proof in
    mathematical vernacular:
    https://homotopytypetheory.org/2020/01/26/the-cantor-schroder-bernstein-theorem-for-∞-groupoids/

Abstract
--------

 (1) CSB in constructive set theory implies excluded middle
     (Pradic & Brown 2019, https://arxiv.org/abs/1904.09193).

       If for all sets X and Y, the existence of injections X → Y and
       Y → X implies X ≃ Y,

       then P ∨ ¬ P for any proposition P.

 (2) In homotopy type theory / univalent foundations (HoTT/UF),
     excluded middle implies CSB, not only for sets, but also for
     arbitrary homotopy types, or ∞-groupoids.

     Assuming excluded middle, for all homotopy types X and Y, if
     there are embeddings X → Y and Y → X, then X ≃ Y.

     This seems to be a new result.

HoTT/UF
-------

An intensional Martin-Löf type theory (MLTT) in which types are
understood as homotopy types, or ∞-groupoids, rather than as sets as
in the original Martin-Löf conception.

We work with a Spartan MLTT:

  1. Empty type 𝟘.

  2. One-point type 𝟙.

  3. A type ℕ of natural numbers.

  4. Type formers

       Π  (product),
       +  (binary sum),
       Σ  (sum),
       Id (identity type).

  5. Universes (types of types), ranged over by 𝓤,𝓥,𝓦.

(Here are lecture notes for HoTT/UF in Agda:
https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes)


Possible axioms for HoTT/UF
---------------------------

  1. Function extensionality.                    \ Given constructive content
  2. Propositional extensionality.               | by cubical type theory.
  3. Univalence.                                 |
  4. Existence of propositional truncations.     | (Implemented in Cubical Agda).
  5. Existence of (some) higher inductive types. /

  6. Propositional resizing and impredicativity. ⟩ Constructive status open.

  7. Excluded middle.                            \ Non constructive.
  8. Choice.                                     /

  * We will not postulate them. Instead we will use them as explicit
    assumptions in theorems and constructions, when needed.

  * For this talk we need only function extensionality and excluded
    middle.

  * Univalence implies function extensionality and propositional
    extensionality.

  * Unique choice just holds.

  * Choice implies excluded middle, as usual.

  * Excluded middle implies propositional resizing and
    impredicativity.

  * Function extensionality and propositional resizing imply the
    existence of propositional truncations, and hence so do function
    extensionality and excluded middle.

  * Univalence and propositional truncations imply the existence of
    some higher inductive types, such as the homotopical circle and
    set quotients.

  * HoTT/UF has a model in Kan simplicial sets after Voevodsky.

  * It validates the above axioms, assuming classical logic and
    Grothendieck universes in the meta-theory.

  * Types are interpreted as homotopy types.

Main differences between HoTT/UF and MLTT
-----------------------------------------

  1. The treatment of identity types.

     * For a type X and points x , y : X, the identity type

         Id X x y,

       also written

         x ＝ y

       here, collects all the ways in which x and y are identified.

     * The type x ＝ y has (provably) multiple elements in general.

     * In the homotopical understanding, the identifications are paths.

     * Example. In the type of groups, one can prove that the
       identifications are in bijection with group isomorphisms,
       assuming univalence.

       Similarly for the types of rings, metric spaces, topological
       spaces, graphs, posets, categories, functor algebras etc.

       (https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/)

  2. The treatment of propositions.

     * There isn't a a built-in type of propositions as in the
       Calculus of Constructions (CoC).

     * The constructed type of propositions, in a type universe 𝓤, is

         Ω 𝓤 := Σ P ꞉ 𝓤 ̇ , is-prop P.

     * A proposition, or truth value, is defined to be a type with at
       most one element, or a subsingleton.

       This e.g. makes unique choice automatic, while in CoC unique
       choice fails.

Part 1
------

The Pradic-Brown argument rendered in HoTT/UF
---------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.CSB-TheoryLabLunch where

open import CoNaturals.GenericConvergentSequence
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import NotionsOfDecidability.Decidable
open import TypeTopology.CompactTypes
open import TypeTopology.GenericConvergentSequenceCompactness
open import UF.Embeddings
open import UF.Equiv
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

Our formulation of Cantor-Schröder-Bernstein:

\begin{code}

CSB : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
CSB X Y = (X ↪ Y) → (Y ↪ X) → X ≃ Y

CantorSchröderBernstein : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
CantorSchröderBernstein 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → CSB X Y

\end{code}

We begin by recalling some definitions.

\begin{code}

recall-decidable : {A : 𝓤 ̇ } → is-decidable A ＝ (A + ¬ A)
recall-decidable = by-definition


recall-Compact : {X : 𝓤 ̇ }
               → is-Compact X {𝓥} ＝ ((A : X → 𝓥 ̇ )
                                         → ((x : X) → is-decidable (A x))
                                         → is-decidable (Σ x ꞉ X , A x))
recall-Compact = by-definition


recall-ℕ∞ : ℕ∞ ＝ (Σ α ꞉ (ℕ → 𝟚) , is-decreasing α)
recall-ℕ∞ = by-definition


recall-ℕ∞-Compact : funext 𝓤₀ 𝓤₀ → is-Compact ℕ∞ {𝓤}
recall-ℕ∞-Compact fe = ℕ∞-Compact fe

\end{code}

The following is Lemma 7 of the above reference, using retractions
rather than surjections, for simplicity:

\begin{code}

Pradic-Brown-lemma : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                   → retract (A + X) of X
                   → is-Compact X
                   → is-decidable A
Pradic-Brown-lemma {𝓤} {𝓥} {X} {A} (r , s , η) c = γ e
 where
  P : X → 𝓤 ⊔ 𝓥 ̇
  P x = Σ a ꞉ A , r x ＝ inl a

  d : (x : X) → is-decidable (P x)
  d x = equality-cases (r x)
         (λ (a : A) (u : r x ＝ inl a) → inl (a , u))
         (λ (y : X) (v : r x ＝ inr y) → inr (λ (a , u) → +disjoint (inl a ＝⟨ u ⁻¹ ⟩
                                                                    r x   ＝⟨ v ⟩
                                                                    inr y ∎)))

  e : is-decidable (Σ x ꞉ X , P x)
  e = c P d

  f : A → Σ x ꞉ X , P x
  f a = s (inl a) , a , η (inl a)

  γ : is-decidable (Σ x ꞉ X , P x) → is-decidable A
  γ (inl (x , a , u)) = inl a
  γ (inr φ)           = inr (contrapositive f φ)

\end{code}

Function extensionality is used twice in the following, once to know
that ℕ∞ is a set, and once to know that it is compact.

\begin{code}

recall-EM : EM 𝓤 ＝ ((P : 𝓤 ̇ ) → is-prop P → P + ¬ P)
recall-EM = by-definition

\end{code}

Function extensionality says that any two pointwise equal functions
are equal.

\begin{code}

CSB-gives-EM : funext 𝓤₀ 𝓤₀
             → (P : 𝓤 ̇ )
             → is-prop P
             → CSB ℕ∞ (P + ℕ∞)
             → P + ¬ P
CSB-gives-EM fe P i csb = γ
 where
  f : ℕ∞ → P + ℕ∞
  f = inr

  j : is-embedding f
  j = inr-is-embedding P ℕ∞

  z : P → ℕ∞
  z _ = Zero

  g : P + ℕ∞ → ℕ∞
  g = cases z Succ

  a : is-embedding z
  a = maps-of-props-into-sets-are-embeddings z i (ℕ∞-is-set fe)

  b : is-embedding Succ
  b = lc-maps-into-sets-are-embeddings Succ Succ-lc (ℕ∞-is-set fe)

  c : disjoint-images z Succ
  c = λ (p : P) (x : ℕ∞) (q : Zero ＝ Succ x) → Zero-not-Succ q

  k : is-embedding g
  k = disjoint-cases-embedding z Succ a b c

  e : ℕ∞ ≃ P + ℕ∞
  e = csb (f , j) (g , k)

  ρ : retract (P + ℕ∞) of ℕ∞
  ρ = ≃-gives-▷ e

  γ : P + ¬ P
  γ = Pradic-Brown-lemma ρ (ℕ∞-Compact fe)

\end{code}

Hence if we assume Cantor-Schröder-Bernstein for the first universe 𝓤₀
and an arbitrary universe 𝓥, as formulated above, then we get excluded
middle for propositions in the universe 𝓥:

\begin{code}

CantorSchröderBernstein-gives-EM : funext 𝓤₀ 𝓤₀
                                 → CantorSchröderBernstein 𝓤₀ 𝓥
                                 → EM 𝓥
CantorSchröderBernstein-gives-EM fe csb P i = CSB-gives-EM fe P i (csb ℕ∞ (P + ℕ∞))

\end{code}


Part 2
------

Can the Cantor-Schröder-Bernstein Theorem be generalized from sets to
arbitrary homotopy types, or ∞-groupoids, in the presence of excluded
middle?

This seems rather unlikely at first sight:

  1. CSB fails for 1-categories.

     In fact, it already fails for posets.
     For example, the intervals (0,1) and [0,1] are order-embedded
     into each other, but they are not order isomorphic.

  2. The known proofs of CSB for sets rely on deciding equality of
     elements of sets.

     But, in the presence of excluded middle, the types that have
     decidable equality are precisely the sets, by Hedberg’s Theorem.

Now:

  * In set theory, a map f : X → Y is an injection if and only if it
    is left-cancellable:

      f x = f x' implies x = x'.

  * But, for (homotopy) types X and Y that are not sets, this notion
    is too weak.

  * Moreover, is not a proposition as the identity type x ＝ x' has
    multiple elements in general.

The appropriate notion of embedding for a function f of arbitrary
types X and Y is given by any of the following two equivalent
conditions:

  1. The map ap f x x' : x ＝ x' → f x ＝ f x' is an equivalence for any x , x' : X.

  2. The fibers of f are all subsingletons.

We have:

    * A map of sets is an embedding if and only if it is left-cancellable.

    * However, for example, any map 𝟙 → Y that picks a point y : Y is
      left-cancellable.

      But it is an embedding if and only if the point y is homotopy isolated.

      This amounts to saying that the identity type y = y is a singleton.

      This fails, for instance, when the type Y is the homotopical
      circle S¹, for any point y, or when Y is a univalent universe
      and y : Y is the two-point type, or any type with more than one
      automorphism.

    * Example (Pradic). There are injections both ways between the
      types ℕ × S¹ and 𝟙 + ℕ × S¹, but they aren't equivalent as one
      of them has an isolated point but the other doesn't.

      No injection 𝟙 + ℕ × S¹ → ℕ × S¹ is an embedding.

    * It is the second characterization of embedding given above that
      we exploit here.

Theorem
-------

The Cantor-Schröder-Bernstein Theorem holds for all homotopy types, or
∞-gropoids, in the presence of excluded middle.

Our proof adapts Halmos' proof in his book Naive Set Theory to our
more general situation.

The fiber of a point y : Y over a map f : X → Y collects all the
points x : X that are mapped by f to a point identified with y,
together with the identification datum:

\begin{code}

recall-fiber : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (y : Y)
             → fiber f y ＝ (Σ x ꞉ X , f x ＝ y)
recall-fiber f x = by-definition


recall-is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-embedding f ＝ ((y : Y) → is-prop (fiber f y))
recall-is-embedding f = by-definition

\end{code}

The type (X ↪ Y) collects all embeddings of the type X into the type Y:

\begin{code}

recall-type-of-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → (X ↪ Y) ＝ (Σ f ꞉ (X → Y) , is-embedding f)
recall-type-of-embeddings = by-definition

\end{code}

We are now ready to formulate and prove the theorem.

\begin{code}

EM-gives-CantorSchröderBernstein : Fun-Ext
                                 → EM (𝓤 ⊔ 𝓥)
                                 → CantorSchröderBernstein 𝓤 𝓥
EM-gives-CantorSchröderBernstein {𝓤} {𝓥} fe excluded-middle
                                 X Y (f , f-is-emb) (g , g-is-emb) =

  need X ≃ Y which-is-given-by 𝒽

 where

  remark-f : type-of (f , f-is-emb) ＝ (X ↪ Y)
  remark-f = by-assumption

  remark-g : type-of (g , g-is-emb) ＝ (Y ↪ X)
  remark-g = by-assumption

\end{code}

In order to define 𝒽 : X ≃ Y, we use a notion of g-point.

\begin{code}

  is-g-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  is-g-point x = (x₀ : X) (n : ℕ) → ((g ∘ f) ^ n) x₀ ＝ x → fiber g x₀

\end{code}

What is important for our purposes is that this is property rather
than data, using the fact that g is an embedding.

We use the fact that propositions are closed under products, which
requires function extensionality:

\begin{code}

  being-g-point-is-prop : (x : X) → is-prop (is-g-point x)
  being-g-point-is-prop x =
   Π-is-prop fe (λ (x₀ : X                   ) →
   Π-is-prop fe (λ (n  : ℕ                   ) →
   Π-is-prop fe (λ (p  : ((g ∘ f) ^ n) x₀ ＝ x) → need is-prop (fiber g x₀)
                                                 which-is-given-by (g-is-emb x₀))))
\end{code}

By construction, considering x₀ = x and n = 0, we have that g is
invertible at g-points, because, by definition, we have that
((g ∘ f) ^ 0) x ＝ x).

\begin{code}

  g-is-invertible-at-g-points : (x : X) → is-g-point x → fiber g x
  g-is-invertible-at-g-points x γ = γ x 0 (by-definition ∶ ((g ∘ f) ^ 0) x ＝ x)

\end{code}

The fiber point is given by the first projection of the fiber:

\begin{code}

  g⁻¹ : (x : X) → is-g-point x → Y
  g⁻¹ x γ = fiber-point (g-is-invertible-at-g-points x γ)

\end{code}

Because being a g-point is property, we can apply excluded middle to
it:

\begin{code}

  δ : (x : X) → is-decidable (is-g-point x)
  δ x = excluded-middle (is-g-point x) (being-g-point-is-prop x)

\end{code}

The rest of the proof shows that the following function is an
equivalence:

\begin{code}

  h : X → Y
  h x = Cases (δ x)
         (γ ꞉   is-g-point x ↦ g⁻¹ x γ)
         (ν ꞉ ¬ is-g-point x ↦ f x)

\end{code}

For that purpose, it is enough to show that it is left-cancellable and
split-surjective.

To show that it is left-cancellable, we first show that g⁻¹ is a
two-sided inverse in its domain of definition.

That it is a right inverse follows from the definition of fiber, by
taking the fiber path, which is given by the second projection:

\begin{code}

  g⁻¹-is-rinv : (x : X) (γ : is-g-point x) → g (g⁻¹ x γ) ＝ x
  g⁻¹-is-rinv x γ = fiber-identification (g-is-invertible-at-g-points x γ)

\end{code}

That it is a left inverse follows from the above and the fact that g,
being an embedding, is left-cancellable:

\begin{code}

  g⁻¹-is-linv : (y : Y) (γ : is-g-point (g y)) → g⁻¹ (g y) γ ＝ y
  g⁻¹-is-linv y γ = have (g (g⁻¹ (g y) γ) ＝⟨ g⁻¹-is-rinv (g y) γ ⟩
                          g y             ∎)
                    so-apply embeddings-are-lc g g-is-emb

\end{code}

We also need the following two facts to establish the
left-cancellability of h:

\begin{code}

  α : (x : X) → is-g-point (g (f x)) → is-g-point x
  α x γ = need is-g-point x
          which-is-given-by
           assume x₀ ∶ X                    and
           assume n  ∶ ℕ                    and
           assume p  ∶ ((g ∘ f) ^ n) x₀ ＝ x then
            (need fiber g x₀
             which-is-given-by
              have ap (g ∘ f) p ∶ ((g ∘ f) ^ (succ n)) x₀ ＝ g (f x)
              so-apply γ x₀ (succ n))

  f-g⁻¹-disjoint-images : (x x' : X)
                        → ¬ is-g-point x
                        → (γ : is-g-point x')
                        → f x ≠ g⁻¹ x' γ
  f-g⁻¹-disjoint-images x x' ν γ p = have p ∶ f x ＝ g⁻¹ x' γ
                                     so need contradiction
                                        which-is-given-by
                                         have γ ∶ is-g-point x'
                                         which-is-impossible-by (v ∶ ¬ is-g-point x')
   where
    q : g (f x) ＝ x'
    q = have p ∶ f x ＝ g⁻¹ x' γ
        so-use (g (f x)      ＝⟨ ap g p ⟩
                g (g⁻¹ x' γ) ＝⟨ g⁻¹-is-rinv x' γ ⟩
                x'           ∎)
    u : ¬ is-g-point (g (f x))
    u = have ν ∶ ¬ is-g-point x
        so-apply contrapositive (α x)
    v : ¬ is-g-point x'
    v = transport (- ↦ ¬ is-g-point -) q u

\end{code}

It is convenient to work with the following auxiliary function H and
prove properties of H and then specialize them to h:

\begin{code}

  H : (x : X) → is-decidable (is-g-point x) → Y
  H x d = Cases d
           (γ ꞉   is-g-point x ↦ g⁻¹ x γ)
           (ν ꞉ ¬ is-g-point x ↦ f x)

  notice-that : h ＝ x ↦ H x (δ x)
  notice-that = by-definition

  h-lc : left-cancellable h
  h-lc {x} {x'} = l (δ x) (δ x')
   where
    l : (d : is-decidable (is-g-point x)) (d' : is-decidable (is-g-point x'))
      → H x d ＝ H x' d'
      → x ＝ x'

    l (inl γ) (inl γ') p = have p ∶ g⁻¹ x γ  ＝ g⁻¹ x'  γ'
                           so (x             ＝⟨ (g⁻¹-is-rinv x γ)⁻¹ ⟩
                               g (g⁻¹ x  γ ) ＝⟨ ap g p ⟩
                               g (g⁻¹ x' γ') ＝⟨ g⁻¹-is-rinv x' γ' ⟩
                               x'            ∎)

    l (inl γ) (inr ν') p = have p ∶ g⁻¹ x γ ＝ f x'
                           which-is-impossible-by (- ↦ f-g⁻¹-disjoint-images x' x ν' γ (- ⁻¹))

    l (inr ν) (inl γ') p = have p ∶ f x ＝ g⁻¹ x' γ'
                           which-is-impossible-by f-g⁻¹-disjoint-images x x' ν γ'

    l (inr ν) (inr ν') p = have p ∶ f x ＝ f x'
                           so-apply embeddings-are-lc f f-is-emb

\end{code}

Next we want to show that h is split surjective. For that purpose, we
define the notion of f-point, which is data rather than property (as
several x₀ and n are possible answers in general).

(In particular, excluded middle can't be applied to the type
f-point x, because excluded middle applies only to truth values.)

\begin{code}

  f-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  f-point x = Σ x₀ ꞉ X , (Σ n ꞉ ℕ , ((g ∘ f) ^ n) x₀ ＝ x) × ¬ fiber g x₀

\end{code}

What is important for our argument is that non-f-points are g-points:

\begin{code}

  non-f-point-is-g-point : (x : X) → ¬ f-point x → is-g-point x
  non-f-point-is-g-point x ν x₀ n p = need fiber g x₀ which-is-given-by
    (Cases (excluded-middle (fiber g x₀) (g-is-emb x₀))
      (σ ꞉   fiber g x₀ ↦ σ)
      (u ꞉ ¬ fiber g x₀ ↦ have (x₀ , (n , p) , u) ∶ f-point x
                          which-is-impossible-by (ν ∶ ¬ f-point x)))

\end{code}

We use the notion of f-point to prove the following, whose statement
doesn't refer to the notion of f-point.

\begin{code}

  claim : (y : Y) → ¬ is-g-point (g y) → Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
  claim y ν = v
   where
    i : ¬¬ f-point (g y)
    i = have ν ∶ ¬ is-g-point (g y)
        so-apply contrapositive (non-f-point-is-g-point (g y))

    ii : f-point (g y) → Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
    ii (x₀ , (0 , p) , u) = have p ∶ x₀ ＝ g y
                            so have (y , (p ⁻¹)) ∶ fiber g x₀
                               which-is-impossible-by (u ∶ ¬ fiber g x₀)
    ii (x₀ , (succ n , p) , u) = a , b
     where
      q : f (((g ∘ f) ^ n) x₀) ＝ y
      q = have p ∶ ((g ∘ f) ^ (succ n)) x₀  ＝ g y
                 ∶ g (f (((g ∘ f) ^ n) x₀)) ＝ g y
          so-apply embeddings-are-lc g g-is-emb
      a : fiber f y
      a = ((g ∘ f) ^ n) x₀ , q
      b : ¬ is-g-point (((g ∘ f) ^ n) x₀)
      b = assume γ ∶ is-g-point (((g ∘ f) ^ n) x₀)
          then (have γ x₀ n refl ∶ fiber g x₀
                which-is-impossible-by (u ∶ ¬ fiber g x₀))

    iii : ¬¬ (Σ (x , p) ꞉ fiber f y , ¬ is-g-point x)
    iii = double-contrapositive ii i

    iv : is-prop (Σ (x , p) ꞉ fiber f y , ¬ is-g-point x)
    iv = have f-is-emb y ∶ is-prop (fiber f y)
         so-apply subtypes-of-props-are-props' pr₁ (pr₁-lc (λ {σ} → negations-are-props fe))

    v : Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
    v = double-negation-elim excluded-middle _ iv iii

\end{code}

With this we are ready to show that h is a split surjection. The idea
is that, given y : Y, we check whether g y is a g-point or not, and if
it is we map it to g y, and otherwise we map y to the point x : X
given by the above claim. But then, of course, we also need to argue
that this works. As above, we use the auxiliary function H for that
purpose.

\begin{code}
  h-split-surjection : (y : Y) → Σ x ꞉ X , h x ＝ y
  h-split-surjection y = x , p
   where
    a : is-decidable (is-g-point (g y))
      → Σ x ꞉ X , ((d : is-decidable (is-g-point x)) → H x d ＝ y)
    a (inl γ) = g y , ψ
     where
      ψ : (d : is-decidable (is-g-point (g y))) → H (g y) d ＝ y
      ψ (inl γ') = H (g y) (inl γ') ＝⟨ by-definition ⟩
                   g⁻¹ (g y) γ'     ＝⟨ g⁻¹-is-linv y γ' ⟩
                   y                ∎
      ψ (inr ν)  = have ν ∶ ¬ is-g-point (g y)
                   which-contradicts (γ ∶ is-g-point (g y))
    a (inr ν) = x , ψ
     where
      w : Σ (x , p) ꞉ fiber f y , ¬ is-g-point x
      w = have ν ∶ ¬ is-g-point (g y)
          so-apply claim y
      x : X
      x = fiber-point (pr₁ w)
      p : f x ＝ y
      p = fiber-identification (pr₁ w)
      ψ : (d : is-decidable (is-g-point x)) → H x d ＝ y
      ψ (inl γ) = have γ ∶ is-g-point x
                  which-is-impossible-by (pr₂ w ∶ ¬ is-g-point x)
      ψ (inr ν) = H x (inr ν) ＝⟨ by-definition ⟩
                  f x         ＝⟨ p ⟩
                  y           ∎
    b : Σ x ꞉ X ,((d : is-decidable (is-g-point x)) → H x d ＝ y)
    b = a (δ (g y))
    x : X
    x = pr₁ b
    p : h x ＝ y
    p = h x       ＝⟨ by-construction ⟩
        H x (δ x) ＝⟨ pr₂ b (δ x) ⟩
        y         ∎

\end{code}

And because left-cancellable split surjections are equivalences, we
are done:

\begin{code}

  𝒽 : X ≃ Y
  𝒽 = h , lc-split-surjections-are-equivs h h-lc h-split-surjection

\end{code}

Q.E.D.
