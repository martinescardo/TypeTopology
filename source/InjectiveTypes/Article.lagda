Martin Escardo, 19th Feb 2019.

Injective types in univalent mathematics, in Agda
-------------------------------------------------

An unformalized version of this file was published in Mathematical
Structures in Computer Science, Cambridge University Press, 5th
January 2021.  https://doi.org/10.1017/S0960129520000225

Remark about the contents and organization of this Agda file.

       This file InjectiveTypes-article is an article-style version of
       the blackboard-style version InjectiveTypes.lagda, to be
       submitted for publication. The blackboard presents the ideas as
       they have been developed, rather than the way they should be
       presented in an article submitted for publication, but still in
       a fully verified way.

       Here we tell the story, referring to the blackboard file for
       the routine proofs (which can be followed as links by clicking
       at them). We have included the non-routine proofs here, and
       some routine proofs that we feel should be added for the sake
       of flow of the text. We repeat the definitions of the notions
       studied here, in a definitionally equal way so that we can
       invoke the blackboard.

       The blackboard file likely has more information than that
       reported here. In particular, it keeps track better of what
       univalent foundations assumptions are used in each construction
       (univalence, function extensionality, propositional
       extensionality, existence of propositional truncations). We do
       keep track of resizing in this article version explicitly: it
       is not a global assumption.

       1st Mar 2019: By now this file has things that are not in the
       blackboard.


Introduction
------------

We investigate the injective types and the algebraically injective
types in univalent mathematics, both in the absence and the presence
of propositional resizing. Injectivity is defined by the surjectivity
of the restriction map along any embedding. Algebraic injectivity is
defined by a given section of the restriction map along any embedding
[John Bourke, 2017, https://arxiv.org/abs/1712.02523].

For the sake of generality, we work without assuming (or rejecting)
the principle of excluded middle, and hence without assuming the axiom
of choice either. Moreover, we show that the principle of excluded
middle holds if and only if all pointed types are algebraically
injective, if and only if all inhabited types are injective, so that
there is nothing interesting to say about injectivity in its presence.

Under propositional resizing principles, the main results
are easy to state:

   (1) Injectivity is equivalent to the propositional truncation of
       algebraic injectivity.

       (This can be seen as a form of choice that just holds, as its
       moves a propositional truncation inside a \m{\Pi}-type to
       outside the \m{\Pi}-type, and may be related to [Toby Kenney,
       2011,
       https://www.sciencedirect.com/science/article/pii/S0022404910000782]).

   (2) The algebraically injective types are precisely the retracts of
       exponential powers of type universes. In particular,

         (a) The algebraically injective sets are precisely the
             retracts of powersets.

         (b) The algebraically injective (n+1)-types are precisely
             retracts of exponential powers of the universes of
             n-types.

       Another consequence is that any universe is embedded as a
       retract of any larger universe.

   (3) The algebraically injective types are also precisely the
       underlying objects of the algebras of the partial map
       classifier monad.


In the absence of propositional resizing, we have similar results
which have subtler statements and proofs that need to keep track of
universe levels rather explicitly.

Most constructions developed here are in the absence of propositional
resizing. We apply them, with the aid of a notion of algebraic
flabbiness, to derive the results that rely on resizing mentioned
above.

Acknowledgements. Mike Shulman acted as a sounding board over the
years, with many helpful remarks, including in particular the
terminology 'algebraic injectivity' for the notion we consider here.

Our type theory
---------------

Because the way we handle universes is different from that of the HoTT
Book [https://homotopytypetheory.org/book/] and Coq, and probably
unfamiliar to readers not acquainted with Agda, we explicitly state it
here.

Our underlying formal system can be considered as a subsystem
of that used in UniMath [https://github.com/UniMath/UniMath].

* We work within a Martin-Löf type theory with types 𝟘 (empty type), 𝟙
  (one-element type), ℕ (natural numbers), and type formers _+_
  (binary sum), Π (product) and Σ (sum), and a hierarchy of type
  universes closed under them in a suitable sense discussed below.

  We take these as required closure properties of our formal system,
  rather than as an inductive definition.

* We assume a universe 𝓤₀, and for each universe 𝓤 we assume a
  successor universe 𝓤⁺ with 𝓤 : 𝓤⁺, and for any two universes 𝓤,𝓥 a
  least upper bound 𝓤 ⊔ 𝓥. We stipulate that we have 𝓤₀ ⊔ 𝓤 = 𝓤 and
  𝓤 ⊔ 𝓤⁺ = 𝓤⁺ definitionally, and that the operation _⊔_ is
  definitionally idempotent, commutative, and associative, and that
  the successor operation _⁺ distributes over _⊔_ definitionally.

  (In Agda here we write X : 𝓤 ̇ (with an almost invisible
  superscript dot), rather than X:𝓤 (without the dot).)

* We stipulate that we have copies 𝟘 {𝓤} and 𝟙 {𝓤} of the empty and
  singleton types in each universe 𝓤.

* We don't assume that the universes are cumulative, in the sense that
  from X : 𝓤 we would be able to deduce that X : 𝓤 ⊔ 𝓥 for any 𝓥, but
  we also don't assume that they are not. However, from the
  assumptions formulated below, it follows that for any two universes
  𝓤,𝓥 there is a map lift {𝓤} 𝓥 : 𝓤 → 𝓤 ⊔ 𝓥, for instance X ↦ X + 𝟘 {𝓥},
  which is an embedding with lift 𝓥 X ≃ X if univalence holds (we
  cannot write the identity type lift 𝓥 X = X, as the lhs and rhs
  live in the different types 𝓤 and 𝓤 ⊔ 𝓥, which are not
  (definitionally) the same in general).

* We stipulate that if X : 𝓤 and Y : 𝓥, then X + Y : 𝓤 ⊔ 𝓥.

* We stipulate that if X : 𝓤 and A : X → 𝓥 then Π {X} A : 𝓤 ⊔ 𝓥. We
  abbreviate this product type as Π A when X can be inferred from A,
  and sometimes we write it verbosely as Π (x:X), A x. (Which in Agda
  is written Π x ꞉ X , A x or (x : X) → A x.)

  In particular, for types X : 𝓤 and Y : 𝓥, we have the function
  type X → Y : 𝓤 ⊔ 𝓥.

* The same type stipulations as for Π, and the same syntactical
  conventions apply to the sum type former Σ.

  In particular, for types X : 𝓤 and Y : 𝓥, we have the cartesian
  product X × Y : 𝓤 ⊔ 𝓥.

* We assume the η conversion rules for Π and Σ.

* For a type X : 𝓤 and points x,y:X, the identity type Id {𝓤} {X} x y
  of type 𝓤 is abbreviated as Id x y and often written x =_X y or x =   y.
  (In Agda: x ＝ y.)

  The elements of the identity type x = y are called identifications or
  paths from x to y.

* We tacitly assume univalence as in the HoTT Book.

* We work with the existence of propositional truncations as an
  assumption, also tacit. The HoTT Book, instead, defines *rules* for
  propositional truncation as a syntactical construct of the formal
  system. Here we take propositional truncation as a principle for a
  pair of universes 𝓤,𝓥:

  Π (X:𝓤),  Σ (∥ X ∥ : 𝓤), ∥ X ∥ is a proposition × (X → ∥ X ∥)
          × Π (P : 𝓥), P is a proposition → (X → P) → ∥ X ∥ → P.

  The universe 𝓤 is that of types we truncate, and 𝓥 is the universe
  where the propositions we eliminate into live.  Because the
  existence of propositional truncations is an assumption rather than
  a type formation rule, its so-called ``computation'' rule doesn't
  hold definitionally, of course.

Assumptions
-----------

We don't assume the K axiom (all types would be sets), we work with a
Spartan MLTT as described above, and we assume univalence and
existence of propositional truncations.

The K axiom is disabled by an Agda option, and the assumptions of
univalence and existence of propositional truncations are parameters for
this module.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.Univalence

module InjectiveTypes.Article
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

\end{code}

We use auxiliary definitions and results from the following modules
(and modules referred to from these modules), and other modules
imported later.

\begin{code}

open import MLTT.Plus-Properties
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.IdEmbedding
open import UF.PairFun
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.UniverseEmbedding
open import UF.Sets
open import UF.SubtypeClassifier

\end{code}

From univalence we get function extensionality and propositional
extensionality:

\begin{code}

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 pe : PropExt
 pe 𝓤 = univalence-gives-propext (ua 𝓤)

import InjectiveTypes.Blackboard
module blackboard = InjectiveTypes.Blackboard fe

\end{code}

The notions of injectivity and algebraic injectivity
----------------------------------------------------

As discussed in the introduction, we study the notions of
algebraically injective type (data), injective type (property) and
their relationships.

Algebraic injectivity stipulates a given section f ↦ f' of the
restriction map _∘ j:

\begin{code}

ainjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ̇
ainjective-type D 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                      → is-embedding j
                      → (f : X → D) → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f

\end{code}

Recall that _∼_ denotes pointwise equality of functions (the reader
can click at a symbol or name in the Agda code to navigate to its
definition).

This defines the algebraic injectivity of a type D in a universe 𝓦
with respect to embeddings with domain in the universe 𝓤 and codomain
in the universe 𝓥. As discussed in the introduction, such tracking of
universes is crucial in the absence of propositional resizing.

Injectivity stipulates that the restriction map is a surjection:

\begin{code}

injective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
injective-type D 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                     → is-embedding j
                     → (f : X → D) → ∃ g ꞉ (Y → D), g ∘ j ∼ f
\end{code}

The algebraic injectivity of universes
--------------------------------------

Universes are algebraically injective, in at least two ways, defined
by the following two extension operators:

\begin{code}

_↓_ _↑_ :  {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → 𝓦 ̇ ) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ )
(f ↓ j) y = Σ w ꞉ fiber j y , f(pr₁ w)
(f ↑ j) y = Π w ꞉ fiber j y , f(pr₁ w)

\end{code}

We are mostly interested in the case when j is an embedding, which in
univalent mathematics amounts to saying that its fibers are all
propositions, but here we also investigate what happens in the absence
of this assumption.

The crucial idea behind the above definitions, under the assumption
that j is an embedding, is that a sum indexed by a proposition (the
fiber) is (equivalent, and hence) equal to any of its summands, and a
product indexed by a proposition is equal to any of its factors.

\begin{code}

↓-is-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
               → is-embedding j
               → (f : X → 𝓤 ⊔ 𝓥 ̇ )
               → f ↓ j ∘ j ∼ f
↓-is-extension {𝓤} {𝓥} j i f x = eqtoid (ua (𝓤 ⊔ 𝓥)) ((f ↓ j ∘ j) x) (f x)
                                   (prop-indexed-sum (x , refl) (i (j x)))

↑-is-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
               → is-embedding j
               → (f : X → 𝓤 ⊔ 𝓥 ̇ )
               → f ↑ j ∘ j ∼ f
↑-is-extension {𝓤} {𝓥} j i f x = eqtoid (ua (𝓤 ⊔ 𝓥)) ((f ↑ j ∘ j) x) (f x)
                                   (prop-indexed-product
                                     (x , refl)
                                     (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
                                     (i (j x)))

universes-are-ainjective-Σ : ainjective-type (𝓤 ⊔ 𝓥 ̇ ) 𝓤 𝓥
universes-are-ainjective-Σ j e f = (f ↓ j , ↓-is-extension j e f)

universes-are-ainjective-Π : ainjective-type (𝓤 ⊔ 𝓥 ̇ ) 𝓤 𝓥
universes-are-ainjective-Π j e f = (f ↑ j , ↑-is-extension j e f)

universes-are-ainjective-particular : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
universes-are-ainjective-particular = universes-are-ainjective-Π

\end{code}

The last statement says that the universe 𝓤 is algebraically injective
with respect to embeddings with domain and codomain in 𝓤. But, of
course, 𝓤 itself doesn't live in 𝓤 and doesn't even have a copy in 𝓤
(see the module LawvereFTP).

For y:Y not in the image of j, it is easy to see that the extensions
give 𝟘 and 𝟙 respectively:

\begin{code}

Σ-extension-out-of-range : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
                         → (y : Y)
                         → ((x : X) → j x ≠ y)
                         → (f ↓ j) y ≃ 𝟘 {𝓣}
Σ-extension-out-of-range f j y φ = empty-indexed-sum-is-𝟘 (uncurry φ)


Π-extension-out-of-range : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
                         → (y : Y)
                         → ((x : X) → j x ≠ y)
                         → (f ↑ j) y ≃ 𝟙 {𝓣}
Π-extension-out-of-range {𝓤} {𝓥} {𝓦} f j y φ =
 empty-indexed-product-is-𝟙 (fe (𝓤 ⊔ 𝓥) 𝓦) (uncurry φ)

\end{code}

With excluded middle, this would give that the Σ and Π extensions have
the same sum and product as the non-extended maps, respectively, but
excluded middle is not needed, as it is not hard to see:

\begin{code}

same-Σ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
       → Σ f ≃ Σ (f ↓ j)
same-Σ = blackboard.same-Σ

same-Π : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
       → Π f ≃ Π (f ↑ j)
same-Π = blackboard.same-Π

\end{code}

The two extensions are left and right Kan extensions in the following
sense, without the need to assume that j is an embedding. First, a map
X → 𝓤, when X is viewed as an ∞-groupoid and hence an ∞-category, and
when 𝓤 is viewed as the ∞-generalization of the category of sets, can
be considered as a sort of ∞-presheaf, because its functoriality is
automatic. Then we can consider natural transformations between such
∞-presheaves. But again the naturality condition is automatic.  We
denote by _≼_ the type of natural transformations between such
∞-presheaves.

We record the following known constructions and facts mentioned above:

\begin{code}

_[_] : {X : 𝓤 ̇ } (f : X → 𝓥 ̇ ) {x y : X} → Id x y → f x → f y
f [ p ] = transport f p

\end{code}

We append the symbol "─" for a variant of a definition with some of the
implicit arguments made explicit:

\begin{code}

automatic-functoriality-id : {X : 𝓤 ̇ } (f : X → 𝓥 ̇ ) {x : X}
                           → f [ 𝓻𝓮𝒻𝓵 x ] ＝ 𝑖𝑑 (f x)
automatic-functoriality-id f = refl

automatic-functoriality-∘ : {X : 𝓤 ̇ }
                            (f : X → 𝓥 ̇ )
                            {x y z : X}
                            (p : Id x y)
                            (q : Id y z)
                          → f [ p ∙ q ] ＝ f [ q ] ∘ f [ p ]
automatic-functoriality-∘ f refl refl = refl

_≼_ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
f ≼ g = (x : domain f) → f x → g x

automatic-naturality : {X : 𝓤 ̇ }
                       (f : X → 𝓥 ̇ )
                       (f' : X → 𝓦' ̇ )
                       (τ : f ≼ f')
                       {x y : X}
                       (p : Id x y)
                     → τ y ∘ f [ p ] ＝ f' [ p ] ∘ τ x
automatic-naturality f f' τ refl = refl

\end{code}

With this notation, we have:

\begin{code}

ηΣ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
   → f ≼ f ↓ j ∘ j
ηΣ f j x B = (x , refl) , B

ηΠ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ ) (j : X → Y)
   → f ↑ j ∘ j ≼ f
ηΠ f j x A = A (x , refl)

\end{code}

These are particular cases of the following facts, which say that the
extension operators are left and right adjoint to the restriction map
g ↦ g ∘ j.

\begin{code}

↓-extension-left-Kan : {X : 𝓤 ̇ }
                       {Y : 𝓥 ̇ }
                       (f : X → 𝓦 ̇ )
                       (j : X → Y)
                       (g : Y → 𝓣 ̇ )
                     → (f ↓ j ≼ g) ≃ (f ≼ g ∘ j)
↓-extension-left-Kan f j g = blackboard.Σ-extension-left-Kan f j g

↑-extension-right-Kan : {X : 𝓤 ̇ }
                        {Y : 𝓥 ̇ } (f : X → 𝓦 ̇ )
                        (j : X → Y)
                        (g : Y → 𝓣 ̇ )
                      → (g ≼ f ↑ j) ≃ (g ∘ j ≼ f)
↑-extension-right-Kan f j g = blackboard.Π-extension-right-Kan f j g

\end{code}

The proofs of the above are routine.

We also have that the left and right Kan extension operators along an
embedding are themselves embeddings.

\begin{code}

↓-extension-is-embedding : (X : 𝓤 ̇ )
                           (Y : 𝓥 ̇ )
                           (j : X → Y)
                         → is-embedding j
                         → is-embedding (_↓ j)
↓-extension-is-embedding {𝓤} {𝓥} X Y j i = s-is-embedding
 where
  s : (X → 𝓤 ⊔ 𝓥 ̇ ) → (Y → 𝓤 ⊔ 𝓥 ̇ )
  s f = f ↓ j

  r : (Y → 𝓤 ⊔ 𝓥 ̇ ) → (X → 𝓤 ⊔ 𝓥 ̇ )
  r g = g ∘ j

  rs : ∀ f → r (s f) ＝ f
  rs f = dfunext (fe 𝓤 ((𝓤 ⊔ 𝓥)⁺)) (↓-is-extension j i f)

  sr : ∀ g → s (r g) ＝ (g ∘ j) ↓ j
  sr g = refl

  κ : (g : Y → 𝓤 ⊔ 𝓥 ̇ ) → s (r g) ≼ g
  κ g y ((x , p) , C) = transport g p C

  M : (𝓤 ⊔ 𝓥)⁺ ̇
  M = Σ g ꞉ (Y → 𝓤 ⊔ 𝓥 ̇ ), ((y : Y) → is-equiv (κ g y))

  φ : (X → 𝓤 ⊔ 𝓥 ̇ ) → M
  φ f = s f , e
   where
    e : (y : Y) → is-equiv (κ (s f) y)
    e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
     where
      δ : (Σ (x , _) ꞉ fiber j y , f x)
        → Σ (x' , _) ꞉ fiber j y , Σ (x , _) ꞉ fiber j (j x') , f x
      δ ((x , p) , C) = (x , p) , (x , refl) , C
      η : (σ : s f y) → κ (s f) y (δ σ) ＝ σ
      η ((x , refl) , C) = refl
      ε : (τ : Σ (λ w → r (s f) (pr₁ w))) → δ (κ (s f) y τ) ＝ τ
      ε ((x , refl) , (x' , p') , C) = t x x' (pa x' x p') p' C (appa x x' p')
       where
         t : (x x' : X) (u : x' ＝ x) (p : j x' ＝ j x) (C : f x') → ap j u ＝ p
           →  ((x' , p)    , (x' , refl) , C)
           ＝ (((x  , refl) ,
                (x' , p) , C) ∶ (Σ (x , _) ꞉ fiber j (j x) , r (s f) x))
         t x x refl p C refl = refl
         q : ∀ x x' → qinv (ap j {x} {x'})
         q x x' = equivs-are-qinvs (ap j) (embedding-gives-embedding' j i x x')
         pa : ∀ x x' → j x ＝ j x' → x ＝ x'
         pa x x' = pr₁ (q x x')
         appa : ∀ x x' p' → ap j (pa x' x p') ＝ p'
         appa x x' = pr₂ (pr₂ (q x' x))

  γ : M → (X → 𝓤 ⊔ 𝓥 ̇ )
  γ (g , e) = r g

  φγ : ∀ m → φ (γ m) ＝ m
  φγ (g , e) =
   to-Σ-＝
    (dfunext (fe 𝓥 ((𝓤 ⊔ 𝓥)⁺))
      (λ y → eqtoid (ua (𝓤 ⊔ 𝓥)) (s (r g) y) (g y) (κ g y , e y)) ,
     Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥))
      (λ y → being-equiv-is-prop'' (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (κ g y)) _ e)

  γφ : ∀ f → γ (φ f) ＝ f
  γφ = rs

  φ-is-equiv : is-equiv φ
  φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

  φ-is-embedding : is-embedding φ
  φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

  ψ : M → (Y → 𝓤 ⊔ 𝓥 ̇ )
  ψ = pr₁

  ψ-is-embedding : is-embedding ψ
  ψ-is-embedding = pr₁-is-embedding
                    (λ g → Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥))
                            (λ y → being-equiv-is-prop'' (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
                                    (κ g y)))

  s-is-comp : s ＝ ψ ∘ φ
  s-is-comp = refl

  s-is-embedding : is-embedding s
  s-is-embedding = ∘-is-embedding φ-is-embedding ψ-is-embedding


↑-extension-is-embedding : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (j : X → Y)
                         → is-embedding j
                         → is-embedding (_↑ j)
↑-extension-is-embedding {𝓤} {𝓥} X Y j i = s-is-embedding
 where
  s : (X → 𝓤 ⊔ 𝓥 ̇ ) → (Y → 𝓤 ⊔ 𝓥 ̇ )
  s f = f ↑ j

  r : (Y → 𝓤 ⊔ 𝓥 ̇ ) → (X → 𝓤 ⊔ 𝓥 ̇ )
  r g = g ∘ j

  rs : ∀ f → r (s f) ＝ f
  rs f = dfunext (fe 𝓤 ((𝓤 ⊔ 𝓥)⁺)) (↑-is-extension j i f)

  sr : ∀ g → s (r g) ＝ (g ∘ j) ↑ j
  sr g = refl

  κ : (g : Y → 𝓤 ⊔ 𝓥 ̇ ) → g ≼ s (r g)
  κ g y C (x , p) = transport⁻¹ g p C

  M : (𝓤 ⊔ 𝓥)⁺ ̇
  M = Σ g ꞉ (Y → 𝓤 ⊔ 𝓥 ̇ ), ((y : Y) → is-equiv (κ g y))

  φ : (X → 𝓤 ⊔ 𝓥 ̇ ) → M
  φ f = s f , e
   where
    e : (y : Y) → is-equiv (κ (s f) y)
    e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
     where
      δ : (((f ↑ j) ∘ j) ↑ j) y → (f ↑ j) y
      δ C (x , p) = C (x , p) (x , refl)
      η : (C : ((f ↑ j ∘ j) ↑ j) y) → κ (s f) y (δ C) ＝ C
      η C = dfunext (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) g
       where
        g : (w : fiber j y) → κ (s f) y (δ C) w ＝ C w
        g (x , refl) = dfunext (fe (𝓥 ⊔ 𝓤) (𝓥 ⊔ 𝓤)) h
         where
          h : (t : fiber j (j x)) → C t (pr₁ t , refl) ＝ C (x , refl) t
          h (x' , p') = transport
                         (λ - → C - (pr₁ - , refl) ＝ C (x , refl) -)
                         q
                         refl
           where
            q : (x , refl) ＝ (x' , p')
            q = i (j x) (x , refl) (x' , p')
      ε : (a : (f ↑ j) y) → δ (κ (s f) y a) ＝ a
      ε a = dfunext (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) g
       where
        g : (w : fiber j y) → δ (κ (s f) y a) w ＝ a w
        g (x , refl) = refl

  γ : M → (X → 𝓤 ⊔ 𝓥 ̇ )
  γ (g , e) = r g

  φγ : ∀ m → φ (γ m) ＝ m
  φγ (g , e) =
   to-Σ-＝
    (dfunext (fe 𝓥 ((𝓤 ⊔ 𝓥)⁺))
      (λ y → eqtoid (ua (𝓤 ⊔ 𝓥)) (s (r g) y) (g y) (≃-sym (κ g y , e y))) ,
     Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥))
      (λ y → being-equiv-is-prop'' (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (κ g y)) _ e)

  γφ : ∀ f → γ (φ f) ＝ f
  γφ = rs

  φ-is-equiv : is-equiv φ
  φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

  φ-is-embedding : is-embedding φ
  φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

  ψ : M → (Y → 𝓤 ⊔ 𝓥 ̇ )
  ψ = pr₁

  ψ-is-embedding : is-embedding ψ
  ψ-is-embedding = pr₁-is-embedding
                    (λ g → Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥))
                    (λ y → being-equiv-is-prop'' (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (κ g y)))

  s-is-comp : s ＝ ψ ∘ φ
  s-is-comp = refl

  s-is-embedding : is-embedding s
  s-is-embedding = ∘-is-embedding φ-is-embedding ψ-is-embedding

\end{code}

We need the following in applications of injectivity to work on
compact ordinals (reported in this repository but not in this
article). Their proofs are routine.

\begin{code}

iterated-↑ : {𝓤 𝓥 𝓦 : Universe}
             {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
             (f : X → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ )
             (j : X → Y) (k : Y → Z)
           → (f ↑ j) ↑ k ∼ f ↑ (k ∘ j)
iterated-↑ {𝓤} {𝓥} {𝓦} f j k z = eqtoid (ua (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                   (((f ↑ j) ↑ k) z) ((f ↑ (k ∘ j)) z)
                                   (blackboard.iterated-extension j k z)

retract-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    (f : X → 𝓦 ̇ ) (f' : X → 𝓦' ̇ )
                    (j : X → Y)
                  → ((x : X) → retract (f x) of (f' x))
                  → ((y : Y) → retract ((f ↑ j) y) of ((f' ↑ j) y))
retract-extension = blackboard.retract-extension

\end{code}

Presumably such constructions can be performed for left Kan extensions
too, but we haven't paused to check this.

This completes our discussion of extensions of maps into universes.

Constructions with algebraically injective types
------------------------------------------------

Algebraicaly injectives are closed under retracts and hence
equivalences:

\begin{code}

retract-of-ainjective : (D' : 𝓦' ̇ ) (D : 𝓦 ̇ )
                      → ainjective-type D 𝓤 𝓥
                      → retract D' of D
                      → ainjective-type D' 𝓤 𝓥
retract-of-ainjective D' D i (r , (s , rs)) {X} {Y} j e f = φ a
 where
  a : Σ f' ꞉ (Y → D), f' ∘ j ∼ s ∘ f
  a = i j e (s ∘ f)

  φ : (Σ f' ꞉ (Y → D), f' ∘ j ∼ s ∘ f) → Σ f'' ꞉ (Y → D'), f'' ∘ j ∼ f
  φ (f' , h) = r ∘ f' , (λ x → r (f' (j x)) ＝⟨ ap r (h x) ⟩
                               r (s (f x))  ＝⟨ rs (f x) ⟩
                               f x          ∎)

equiv-to-ainjective : (D' : 𝓦' ̇ ) (D : 𝓦 ̇ )
                    → ainjective-type D 𝓤 𝓥
                    → D' ≃ D
                    → ainjective-type D' 𝓤 𝓥
equiv-to-ainjective D' D i e = retract-of-ainjective D' D i (≃-gives-◁ e)

\end{code}

And under products, where we perform the extension pointwise:

\begin{code}

Π-ainjective : {A : 𝓣 ̇ } {D : A → 𝓦 ̇ }
             → ((a : A) → ainjective-type (D a) 𝓤 𝓥)
             → ainjective-type (Π D) 𝓤 𝓥
Π-ainjective {𝓣} {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = f' , g
 where
  l : (a : A) → Σ h ꞉ (Y → D a) , h ∘ j ∼ (λ x → f x a)
  l a = (i a) j e (λ x → f x a)

  f' : Y → (a : A) → D a
  f' y a = pr₁ (l a) y

  g : f' ∘ j ∼ f
  g x = dfunext (fe 𝓣 𝓦) (λ a → pr₂ (l a) x)

\end{code}

And hence under exponential powers:

\begin{code}

power-of-ainjective : {A : 𝓣 ̇ } {D : 𝓦 ̇ }
                    → ainjective-type D       𝓤 𝓥
                    → ainjective-type (A → D) 𝓤 𝓥
power-of-ainjective i = Π-ainjective (λ a → i)

\end{code}

An algebraically injective type is a retract of every type it is
embedded into, where we use _↪_ for the type of embeddings. We simply
extend the identity function to get the retraction:

\begin{code}

ainjective-retract-of-subtype : (D : 𝓦 ̇ )
                              → ainjective-type D 𝓦 𝓥
                              → (Y : 𝓥 ̇ ) → D ↪ Y → retract D of Y
ainjective-retract-of-subtype D i Y (j , e) = pr₁ a , j , pr₂ a
 where
  a : Σ f' ꞉ (Y → D) , f' ∘ j ∼ id
  a = i j e id

\end{code}

The identity-type former Id is an embedding X → (X → 𝓤). The proof
requires some insight and can be found in another module by following
the link.

\begin{code}

Id-is-embedding : {X : 𝓤 ̇ } → is-embedding(Id {𝓤} {X})
Id-is-embedding {𝓤} = UA-Id-embedding (ua 𝓤) fe

\end{code}

The proof explained in the published article is implemented at

https://www.cs.bham.ac.uk/~mhe/HoTT-UF.in-Agda-Lecture-Notes/HoTT-UF-Agda.html#yoneda

From this we conclude that algebraically injective types are retracts
of powers of universes:

\begin{code}

ainjective-is-retract-of-power-of-universe : (D : 𝓤 ̇ )
                                           → ainjective-type D 𝓤 (𝓤 ⁺)
                                           → retract D of (D → 𝓤 ̇ )
ainjective-is-retract-of-power-of-universe {𝓤} D i =
 ainjective-retract-of-subtype D i
  (D → 𝓤 ̇ )
  (Id , Id-is-embedding)

\end{code}

Algebraic flabbiness and resizing constructions
-----------------------------------------------

We now discuss resizing constructions that don't assume resizing
axioms. The above results, when combined together in the obvious way,
almost give directly that the algebraically injective types are
precisely the retracts of exponential powers of universes, but there
is a universe mismatch. Keeping track of the universes to avoid the
mismatch, what we get instead is a resizing construction without the
need to resizing axioms:

\begin{code}

ainjective-resizing₀ : (D : 𝓤 ̇ )
                     → ainjective-type D 𝓤 (𝓤 ⁺)
                     → ainjective-type D 𝓤 𝓤
ainjective-resizing₀ {𝓤} D i = c d
 where
  a : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
  a = universes-are-ainjective-Π

  b : ainjective-type (D → 𝓤 ̇ ) 𝓤 𝓤
  b = power-of-ainjective a

  c : retract D of (D → 𝓤 ̇ ) → ainjective-type D 𝓤 𝓤
  c = retract-of-ainjective D (D → 𝓤 ̇ ) b

  d : retract D of (D → 𝓤 ̇ )
  d = ainjective-is-retract-of-power-of-universe D i

\end{code}

This is resizing down and so is not surprising.

Of course, such a construction can be performed directly by
considering an embedding 𝓤 → 𝓤 ⁺, but the idea is to generalize it to
obtain further resizing-for-free constructions, and, later,
resizing-for-a-price constructions. We achieve this by considering a
notion of flabbiness as data, rather than as property as in the
1-topos literature (see e.g. [Ingo Blechschmidt, 2018,
https://arxiv.org/abs/1810.12708]). The notion of flabbiness
considered in topos theory is defined with truncated Σ, that is, the
existential quantifier ∃ with values in the subobject classifier Ω. We
refer to the notion defined with untruncated Σ as algebraic
flabbiness.  This terminology is more than a mere analogy: notice that
flabbiness and algebraic flabbiness amount to simply injectivity and
algebraic injectivity with respect to the class of embeddings P → 𝟙
with P ranging over propositions.

\begin{code}

aflabby : 𝓦 ̇ → (𝓤 : Universe) → 𝓦 ⊔ 𝓤 ⁺ ̇
aflabby D 𝓤 = (P : 𝓤 ̇ ) → is-prop P → (f : P → D) → Σ d ꞉ D , ((p : P) → d ＝ f p)

\end{code}

Algebraically flabby types are pointed by considering P=𝟘:

\begin{code}

aflabby-pointed : (D : 𝓦 ̇ ) → aflabby D 𝓤 → D
aflabby-pointed D φ = pr₁ (φ 𝟘 𝟘-is-prop unique-from-𝟘)

\end{code}

And algebraically injective types are algebraically flabby because
maps P → 𝟙 from propositions P are embeddings, as alluded above:

\begin{code}

ainjective-types-are-aflabby : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → aflabby D 𝓤
ainjective-types-are-aflabby {𝓦} {𝓤} {𝓥} D i P h f = pr₁ s ⋆ , pr₂ s
 where
  s : Σ f' ꞉ (𝟙 → D), f' ∘ unique-to-𝟙 ∼ f
  s = i unique-to-𝟙 (unique-to-𝟙-is-embedding P h 𝓥) f

\end{code}

The interesting thing about this is that the universe 𝓥 is forgotten,
and then we can put any other universe below 𝓤 back, as follows.

\begin{code}

aflabby-types-are-ainjective : (D : 𝓦 ̇ )
                             → aflabby D (𝓤 ⊔ 𝓥)
                             → ainjective-type D 𝓤 𝓥
aflabby-types-are-ainjective D φ {X} {Y} j e f = f' , p
 where
  g : (y : Y) → Σ d ꞉ D , ((w : fiber j y) → d ＝ (f ∘ pr₁) w)
  g y = φ (fiber j y) (e y) (f ∘ pr₁)

  f' : Y → D
  f' y = pr₁ (g y)

  p : (x : X) → f' (j x) ＝ f x
  p x = q (x , refl)
   where
    q : (w : fiber j (j x)) → f' (j x) ＝ f (pr₁ w)
    q = pr₂ (g (j x))

\end{code}

We then get the following resizing construction by composing the above
two conversions between algebraic flabbiness and injectivity:

\begin{code}

ainjective-resizing₁ : (D : 𝓦 ̇ )
                     → ainjective-type D (𝓤 ⊔ 𝓣) 𝓥
                     → ainjective-type D 𝓤 𝓣
ainjective-resizing₁ {𝓦} {𝓤} {𝓣} {𝓥} D i = b
 where
  a : aflabby D (𝓤 ⊔ 𝓣)
  a = ainjective-types-are-aflabby D i

  b : ainjective-type D 𝓤 𝓣
  b = aflabby-types-are-ainjective D a

\end{code}

We record the following particular cases as examples:

\begin{code}

module _ (D : 𝓦 ̇ ) where

 ainjective-resizing₂ :  ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤 𝓤
 ainjective-resizing₂ = ainjective-resizing₁ D

 ainjective-resizing₃ : ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤₀ 𝓤
 ainjective-resizing₃ = ainjective-resizing₁ D

 ainjective-resizing₄ : ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤 𝓤₀
 ainjective-resizing₄ = ainjective-resizing₁ D

 ainjective-resizing₅ : ainjective-type D 𝓤 𝓤₀ → ainjective-type D 𝓤 𝓤
 ainjective-resizing₅ = ainjective-resizing₁ D

 ainjective-resizing₆ : ainjective-type D 𝓤 𝓤₀ ↔ ainjective-type D 𝓤 𝓤
 ainjective-resizing₆ = (ainjective-resizing₁ D , ainjective-resizing₁ D)

\end{code}

In particular, algebraic 𝓤,𝓥-injectivity gives algebraic 𝓤,𝓤- and
𝓤₀,𝓤-injectivity.  So this is no longer necessarily resizing down, by
taking 𝓥 to be the e.g. first universe 𝓤₀.

We now apply algebraic flabbiness to show that any subuniverse closed
under subsingletons and under sums, or alternatively under products,
is also algebraically injective.


\begin{code}

subuniverse-aflabby-Σ
 : (A : 𝓤 ̇ → 𝓣 ̇ )
 → ((X : 𝓤 ̇ ) → is-prop (A X))
 → ((P : 𝓤 ̇ ) → is-prop P → A P)
 → ((X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → A X → ((x : X) → A (Y x)) → A (Σ Y))
 → aflabby (Σ A) 𝓤
subuniverse-aflabby-Σ {𝓤} {𝓣} A φ α κ P i f
 = (X , a) , c
 where
  g : P → 𝓤 ̇
  g = pr₁ ∘ f

  h : (p : P) → A (g p)
  h = pr₂ ∘ f

  X : 𝓤 ̇
  X = Σ p ꞉ P , g p

  a : A X
  a = κ P g (α P i) h

  c : (p : P) → (X , a) ＝ f p
  c p = to-Σ-＝ (q , r)
   where
     q : X ＝ g p
     q = eqtoid (ua 𝓤) X (g p) (prop-indexed-sum p i)

     r : transport A q a ＝ h p
     r = φ (g p) (transport A q a) (h p)

\end{code}

TODO. What this is really saying is that a subtype of an algebraically
flabby type closed under flabbiness is itself an algebraically flabby
type with the restriction of the algebraic structure. This would avoid
us reproving the following:

\begin{code}

subuniverse-aflabby-Π
 : (A : 𝓤 ̇ → 𝓣 ̇ )
 → ((X : 𝓤 ̇ ) → is-prop (A X))
 → ((P : 𝓤 ̇ ) → is-prop P → A P)
 → ((X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → A X → ((x : X) → A (Y x)) → A (Π Y))
 → aflabby (Σ A) 𝓤
subuniverse-aflabby-Π {𝓤} {𝓣} A φ α κ P i f
 = (X , a) , c
 where
  X : 𝓤 ̇
  X = Π (pr₁ ∘ f)

  a : A X
  a = κ P (pr₁ ∘ f) (α P i) (pr₂ ∘ f)

  c : (p : P) → (X , a) ＝ f p
  c p = to-Σ-＝ (q , r)
   where
     q : X ＝ pr₁ (f p)
     q = eqtoid (ua 𝓤) X (pr₁ (f p)) (prop-indexed-product p (fe 𝓤 𝓤) i)

     r : transport A q a ＝ pr₂ (f p)
     r = φ (pr₁ (f p)) (transport A q a) (pr₂ (f p))

\end{code}

Therefore:

\begin{code}

subuniverse-ainjective-Σ
 : (A : 𝓤 ̇ → 𝓣 ̇ )
 → ((X : 𝓤 ̇ ) → is-prop (A X))
 → ((P : 𝓤 ̇ ) → is-prop P → A P)
 → ((X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → A X → ((x : X) → A (Y x)) → A (Σ Y))
 → ainjective-type (Σ A) 𝓤 𝓤
subuniverse-ainjective-Σ {𝓤} {𝓣} A φ α κ
 = aflabby-types-are-ainjective (Σ A) (subuniverse-aflabby-Σ {𝓤} {𝓣} A φ α κ)

subuniverse-ainjective-Π
 : (A : 𝓤 ̇ → 𝓣 ̇ )
 → ((X : 𝓤 ̇ ) → is-prop (A X))
 → ((P : 𝓤 ̇ ) → is-prop P → A P)
 → ((X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → A X → ((x : X) → A (Y x)) → A (Π Y))
 → ainjective-type (Σ A) 𝓤 𝓤
subuniverse-ainjective-Π {𝓤} {𝓣} A φ α κ
 = aflabby-types-are-ainjective (Σ A) (subuniverse-aflabby-Π {𝓤} {𝓣} A φ α κ)

\end{code}

Therefore the subuniverse of n-types is flabby and hence injective.

NB. Our hlevels in this formalization unashamedly start from 0 with
propositions. We omit the singleton or contractible types from our
level indexing. We may change this in the future, but the current
choice is based on the fact that we get more uniform proofs.

\begin{code}

open import UF.HLevels ua

ℍ-aflabby : (n : ℕ) → aflabby (Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n) 𝓤
ℍ-aflabby n = subuniverse-aflabby-Π
               (_is-of-hlevel n)
               (hlevel-relation-is-prop n)
               (props-have-all-hlevels n)
               (λ X Y _ → hlevels-closed-under-Π n X Y)

ℍ-ainjective : (n : ℕ) → ainjective-type (Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n) 𝓤 𝓤
ℍ-ainjective {𝓤} n = aflabby-types-are-ainjective (ℍ n 𝓤) (ℍ-aflabby n)

\end{code}

In particular, the type Ω 𝓤 of propositions in the universe 𝓤 is
algebraically flabby and injective:

\begin{code}

Ω-aflabby : aflabby (Ω 𝓤) 𝓤
Ω-aflabby = ℍ-aflabby zero

Ω-ainjective : ainjective-type (Ω 𝓤) 𝓤 𝓤
Ω-ainjective = ℍ-ainjective zero

\end{code}

Another way to see this is that it is a retract of the universe by
propositional truncation (exercise, not included).

Algebraic injectivity and flabbiness in the presence of propositional resizing axioms
-------------------------------------------------------------------------------------

Returning to size issues, we now apply algebraic flabbiness to show
that propositional resizing gives unrestricted algebraic injective
resizing.

The propositional resizing principle, from 𝓤 to 𝓥, that we consider
here says that every proposition in the universe 𝓤 has an equivalent
copy in the universe 𝓥. This is consistent because it is implied by
excluded middle, but, as far as we are aware, there is no known
computational interpretation of this axiom. A model in which excluded
middle fails but propositional resizing holds is given by Shulman
[Univalence for inverse diagrams and homotopy canonicity. Mathematical
Structures in Computer Science, 25:05 (2015), p1203–1277,
https://arxiv.org/abs/1203.3253].

We begin with the following construction, which says that algebraic
flabbiness is universe independent in the presence of propositional
resizing:

\begin{code}

open import UF.Size

aflabbiness-resizing : (D : 𝓦 ̇ ) (𝓤 𝓥 : Universe)
                     → propositional-resizing 𝓤 𝓥
                     → aflabby D 𝓥
                     → aflabby D 𝓤
aflabbiness-resizing D 𝓤 𝓥 R φ P i f = d , h
 where
  Q : 𝓥 ̇
  Q = resize R P i

  j : is-prop Q
  j = resize-is-prop R P i

  α : P → Q
  α = to-resize R P i

  β : Q → P
  β = from-resize R P i

  d : D
  d = pr₁ (φ Q j (f ∘ β))

  k : (q : Q) → d ＝ f (β q)
  k = pr₂ (φ Q j (f ∘ β))

  h : (p : P) → d ＝ f p
  h p = d           ＝⟨ k (α p) ⟩
        f (β (α p)) ＝⟨ ap f (i (β (α p)) p) ⟩
        f p         ∎

\end{code}

And from this it follows that algebraic injectivity is also universe
independent in the presence of propositional resizing: we convert
back-and-forth between algebraic injectivity and algebraic flabbiness:

\begin{code}

ainjective-resizing : propositional-resizing (𝓤' ⊔ 𝓥') 𝓤
                    → (D : 𝓦 ̇ )
                    → ainjective-type D 𝓤 𝓥
                    → ainjective-type D 𝓤' 𝓥'
ainjective-resizing {𝓤'} {𝓥'} {𝓤} {𝓦} {𝓥} R D i = c
 where
  a : aflabby D 𝓤
  a = ainjective-types-are-aflabby D i

  b : aflabby D (𝓤' ⊔ 𝓥')
  b = aflabbiness-resizing D (𝓤' ⊔ 𝓥') 𝓤 R a

  c :  ainjective-type D 𝓤' 𝓥'
  c = aflabby-types-are-ainjective D b

\end{code}

As an application of this and of the algebraic injectivity of
universes, we get that any universe is a retract of any larger
universe.  We remark that for types that are not sets, sections are
not automatically embeddings [Shulman, Logical Methods in Computer
Science Vol 12 No. 3. (2017), https://arxiv.org/abs/1507.03634]. But
we can choose the retraction so that the section is an embedding in
our situation.

\begin{code}

universe-retract : Propositional-resizing
                 → (𝓤 𝓥 : Universe)
                 → Σ ρ ꞉ retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ ), is-embedding (section ρ)
universe-retract R 𝓤 𝓥 = ρ , Lift-is-embedding ua
 where
  a : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
  a = universes-are-ainjective-Π {𝓤} {𝓤}

  b : ainjective-type (𝓤 ̇ ) (𝓤 ⁺) ((𝓤 ⊔ 𝓥)⁺)
  b = ainjective-resizing R (𝓤 ̇ ) a

  c : ainjective-type (𝓤 ̇ ) (𝓤 ⁺) ((𝓤 ⊔ 𝓥 )⁺)
    → retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ )
  c i = ainjective-retract-of-subtype
         (𝓤 ̇ )
         i
         (𝓤 ⊔ 𝓥 ̇ )
         (Lift 𝓥 , Lift-is-embedding ua)

  ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ )
  ρ = c b

\end{code}

Here are are using the fact that every injective type is a retract of
any type in which it is embedded, in conjunction with resizing, and
that there is an embedding of any universe into any larger universe,
assuming univalence (the map Lift).

It may be of interest to unfold the above proof to see a direct
argument from first principles avoiding flabbiness and injectivity (we
will probably not include this in the paper submitted for
publication):

\begin{code}

universe-retract-unfolded
 : Propositional-resizing
 → (𝓤 𝓥 : Universe)
 → Σ ρ ꞉ retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ ), is-embedding (section ρ)
universe-retract-unfolded R 𝓤 𝓥
 = (r , Lift 𝓥 , rs) , Lift-is-embedding ua
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = Lift 𝓥

  e : is-embedding s
  e = Lift-is-embedding ua

  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)

  f : (Y : 𝓤 ⊔ 𝓥 ̇ ) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)

  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r Y = (p : F Y) → pr₁ (f Y p)

  rs : (X : 𝓤 ̇ ) → r (s X) ＝ X
  rs X = γ
   where
    g : (Y : 𝓤 ⊔ 𝓥 ̇ ) → fiber s Y → F Y
    g Y = to-resize R (fiber s Y) (e Y)

    u : F (s X)
    u = g (s X) (X , refl)

    v : fiber s (s X)
    v = f (s X) u

    i : (Y : 𝓤 ⊔ 𝓥 ̇ ) → is-prop (F Y)
    i Y = resize-is-prop R (fiber s Y) (e Y)

    X' : 𝓤 ̇
    X' = pr₁ v

    a : r (s X) ≃ X'
    a = prop-indexed-product u (fe 𝓤 𝓤) (i (s X))

    b : s X' ＝ s X
    b = pr₂ v

    c : X' ＝ X
    c = embeddings-are-lc s e b

    d : r (s X) ≃ X
    d = transport (λ - → r (s X) ≃ -) c a

    γ : r (s X) ＝ X
    γ = eqtoid (ua 𝓤) (r (s X)) X d

\end{code}

We also have that any subuniverse closed under propositions and Σ or Π
is a retract of 𝓤:

\begin{code}

reflective-subuniverse-Σ
 : Propositional-resizing
 → (A : 𝓤 ̇ → 𝓣 ̇ )
 → ((X : 𝓤 ̇ ) → is-prop (A X))
 → ((P : 𝓤 ̇ ) → is-prop P → A P)
 → ((X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → A X → ((x : X) → A (Y x)) → A (Σ Y))
 → retract (Σ A) of (𝓤 ̇ )
reflective-subuniverse-Σ {𝓤} {𝓣} R A φ α κ
 = ainjective-retract-of-subtype (Σ A) c (𝓤 ̇ ) (j , e)
 where
  c : ainjective-type (Σ A) (𝓤 ⁺ ⊔ 𝓣) (𝓤 ⁺)
  c = ainjective-resizing R (Σ A) (subuniverse-ainjective-Σ A φ α κ)

  j : Σ A → 𝓤 ̇
  j = pr₁

  e : is-embedding j
  e = pr₁-is-embedding φ

reflective-subuniverse-Π
 : Propositional-resizing
 → (A : 𝓤 ̇ → 𝓣 ̇ )
 → ((X : 𝓤 ̇ ) → is-prop (A X))
 → ((P : 𝓤 ̇ ) → is-prop P → A P)
 → ((X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ ) → A X → ((x : X) → A (Y x)) → A (Π Y))
 → retract (Σ A) of (𝓤 ̇ )
reflective-subuniverse-Π {𝓤} {𝓣} R A φ α κ
 = ainjective-retract-of-subtype (Σ A) c (𝓤 ̇ ) (j , e)
 where
  c : ainjective-type (Σ A) (𝓤 ⁺ ⊔ 𝓣) (𝓤 ⁺)
  c = ainjective-resizing R (Σ A) (subuniverse-ainjective-Π A φ α κ)

  j : Σ A → 𝓤 ̇
  j = pr₁

  e : is-embedding j
  e = pr₁-is-embedding φ

\end{code}

In particular (and maybe the Σ version gives n-truncations?):

\begin{code}

reflective-n-type-subuniverse-Σ
 : Propositional-resizing
 → (n : ℕ) → retract (Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n) of (𝓤 ̇ )
reflective-n-type-subuniverse-Σ R n = reflective-subuniverse-Σ R
                                       (_is-of-hlevel n)
                                       (hlevel-relation-is-prop n)
                                       (props-have-all-hlevels n)
                                       (hlevels-closed-under-Σ n)

reflective-n-type-subuniverse-Π
 : Propositional-resizing
 → (n : ℕ) → retract (Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n) of (𝓤 ̇ )
reflective-n-type-subuniverse-Π R n = reflective-subuniverse-Π R
                                       (_is-of-hlevel n)
                                       (hlevel-relation-is-prop n)
                                       (props-have-all-hlevels n)
                                       (λ X Y _ → hlevels-closed-under-Π n X Y)

reflective-Ω : Propositional-resizing
             → retract (Ω 𝓤) of (𝓤 ̇ )
reflective-Ω R = reflective-n-type-subuniverse-Σ R zero

\end{code}

As mentioned above, we almost have that the algebraically injective
types are precisely the retracts of exponential powers of universes,
up to a universe mismatch. This mismatch is side-stepped by
propositional resizing:

\begin{code}

ainjective-characterization : propositional-resizing (𝓤 ⁺) 𝓤
                            → (D : 𝓤 ̇ ) → ainjective-type D 𝓤 𝓤
                                        ↔ (Σ X ꞉ 𝓤 ̇ , retract D of (X → 𝓤 ̇ ))
ainjective-characterization {𝓤} R D = a , b
 where
  a : ainjective-type D 𝓤 𝓤 → Σ X ꞉ 𝓤 ̇ , retract D of (X → 𝓤 ̇ )
  a i = D , d
   where
    c : ainjective-type D 𝓤 (𝓤 ⁺)
    c = ainjective-resizing R D i

    d : retract D of (D → 𝓤 ̇ )
    d = ainjective-is-retract-of-power-of-universe D c

  b : (Σ X ꞉ 𝓤 ̇ , retract D of (X → 𝓤 ̇ )) → ainjective-type D 𝓤 𝓤
  b (X , r) = d
   where
    c : ainjective-type (X → 𝓤 ̇ ) 𝓤 𝓤
    c = power-of-ainjective universes-are-ainjective-Π

    d : ainjective-type D 𝓤 𝓤
    d = retract-of-ainjective D (X → 𝓤 ̇ ) c r

\end{code}

We emphasize that this is a logical equivalence ``if and only if''
rather than an ∞-groupoid equivalence ``≃''. So this characterizes the
types that ⋆can⋆ be equipped with algebraically injective structure.

We also have that an algebraically injective (n+1)-type is a retract
of an exponential power of the universe of n-types. We prove something
more general first.

\begin{code}

ainjective-retract-sub : Propositional-resizing
                       → (A : 𝓤 ̇ → 𝓣 ̇ )
                       → ((X : 𝓤 ̇ ) → is-prop (A X))
                       → (X : 𝓤 ̇ )
                       → ((x x' : X) → A (x ＝ x'))
                       → ainjective-type X 𝓤 𝓤
                       → retract X of (X → Σ A)
ainjective-retract-sub {𝓤} {𝓣} R A φ X β i =
 ainjective-retract-of-subtype X d (X → Σ A) (l , c)
 where
  j : Σ A → 𝓤 ̇
  j = pr₁

  a : is-embedding j
  a = pr₁-is-embedding φ

  k : (X → Σ A) → (X → 𝓤 ̇ )
  k = j ∘_

  b : is-embedding k
  b = postcomp-is-embedding fe j a

  l : X → (X → Σ A)
  l x x' = (x ＝ x') , β x x'

  p : k ∘ l ＝ Id
  p = refl

  c : is-embedding l
  c = factor-is-embedding l k Id-is-embedding b

  d : ainjective-type X 𝓤 (𝓤 ⁺ ⊔ 𝓣)
  d = ainjective-resizing R X i

\end{code}

Using this, we get that the algebraically injective (n+1)-types are the
retracts of exponential powers of the subuniverse of n-types.

\begin{code}

ainjective-ntype-characterization
 : Propositional-resizing
 → (D : 𝓤 ̇ )
 → (n : ℕ)
 → D is-of-hlevel (succ n)
 → ainjective-type D 𝓤 𝓤
 ↔ (Σ X ꞉ 𝓤 ̇ , retract D of
                (X → Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n))
ainjective-ntype-characterization {𝓤} R D n h = (a , b)
 where
  a : ainjective-type D 𝓤 𝓤 → Σ X ꞉ 𝓤 ̇ , retract D of (X → ℍ n 𝓤 )
  a i = D ,
        ainjective-retract-sub
         R
         (_is-of-hlevel n)
         (hlevel-relation-is-prop n)
         D
         h
         i

  b : (Σ X ꞉ 𝓤 ̇ , retract D of (X → ℍ n 𝓤)) → ainjective-type D 𝓤 𝓤
  b (X , r) = d
   where
    e : ainjective-type (ℍ n 𝓤) 𝓤 𝓤
    e = ℍ-ainjective n

    c : ainjective-type (X → ℍ n 𝓤) 𝓤 𝓤
    c = power-of-ainjective e

    d : ainjective-type D 𝓤 𝓤
    d = retract-of-ainjective D (X → ℍ n 𝓤) c r

\end{code}

In particular, the injective sets are the retracts of powersets.

\begin{code}

ainjective-set-characterization
 : Propositional-resizing
 → (D : 𝓤 ̇ )
 → is-set D
 → ainjective-type D 𝓤 𝓤 ↔ (Σ X ꞉ 𝓤 ̇ , retract D of (X → Ω 𝓤))
ainjective-set-characterization {𝓤} R D s =
 ainjective-ntype-characterization R D zero (λ x x' → s {x} {x'})

\end{code}

Injectivity versus algebraic injectivity in the absence of resizing
-------------------------------------------------------------------

We now compare injectivity with algebraic injectivity.

\begin{code}

ainjective-gives-injective : (D : 𝓦 ̇ )
                           → ainjective-type D 𝓤 𝓥
                           → injective-type D 𝓤 𝓥
ainjective-gives-injective D i j e f = ∣ i j e f ∣

\end{code}

The following is routine, using the fact that propositions are closed under products.

\begin{code}

injectivity-is-prop : (D : 𝓦 ̇ ) (𝓤 𝓥 : Universe)
                    → is-prop (injective-type D 𝓤 𝓥)
injectivity-is-prop = blackboard.injective.injectivity-is-prop pt

\end{code}

(But of course algebraic injectivity is not.)

From this we get the following.

\begin{code}

∥ainjective∥-gives-injective : (D : 𝓦 ̇ )
                             → ∥ ainjective-type D 𝓤 𝓥  ∥
                             → injective-type D 𝓤 𝓥
∥ainjective∥-gives-injective {𝓦} {𝓤} {𝓥} D = ∥∥-rec
                                               (injectivity-is-prop D 𝓤 𝓥)
                                               (ainjective-gives-injective D)

\end{code}

In order to relate injectivity to the propositional truncation of
algebraic injectivity in the other direction, we first establish some
facts about injectivity that we already proved for algebraic
injectivity. These facts cannot be obtained by reduction (in
particular products of injectives are not necessarily injective, in
the absence of choice, but exponential powers are).

\begin{code}

embedding-∥retract∥ : (D : 𝓦 ̇ )
                    → injective-type D 𝓦 𝓥
                    → (Y : 𝓥 ̇ ) (j : D → Y)
                    → is-embedding j
                    → ∥ retract D of Y ∥
embedding-∥retract∥ D i Y j e = ∥∥-functor φ a
  where
   a : ∃ r ꞉ (Y → D), r ∘ j ∼ id
   a = i j e id

   φ : (Σ r ꞉ (Y → D) , r ∘ j ∼ id) → Σ r ꞉ (Y → D) , Σ s ꞉ (D → Y) , r ∘ s ∼ id
   φ (r , p) = r , j , p

retract-of-injective : (D' : 𝓤' ̇ ) (D : 𝓤 ̇ )
                     → injective-type D 𝓦 𝓣
                     → retract D' of D
                     → injective-type D' 𝓦 𝓣
retract-of-injective D' D i (r , (s , rs)) {X} {Y} j e f = γ
  where
   i' : ∃ f' ꞉ (Y → D), f' ∘ j ∼ s ∘ f
   i' = i j e (s ∘ f)

   φ : (Σ f' ꞉ (Y → D) , f' ∘ j ∼ s ∘ f) → Σ f'' ꞉ (Y → D') , f'' ∘ j ∼ f
   φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))

   γ : ∃ f'' ꞉ (Y → D') , f'' ∘ j ∼ f
   γ = ∥∥-functor φ i'

power-of-injective : {A : 𝓣 ̇ } {D : 𝓦 ̇ }
                   → injective-type D       (𝓣 ⊔ 𝓤) (𝓣 ⊔ 𝓥)
                   → injective-type (A → D) 𝓤 𝓥
power-of-injective {𝓣} {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = γ
  where
   g : X × A → D
   g = uncurry f

   k : X × A → Y × A
   k (x , a) = j x , a

   c : is-embedding k
   c = pair-fun-is-embedding j (λ x a → a) e (λ x → id-is-embedding)

   ψ : ∃ g' ꞉ (Y × A → D), g' ∘ k ∼ g
   ψ = i k c g

   φ : (Σ g' ꞉ (Y × A → D) , g' ∘ k ∼ g) → (Σ f' ꞉ (Y → (A → D)), f' ∘ j ∼ f)
   φ (g' , h) = curry g' , (λ x → dfunext (fe 𝓣 𝓦) (λ a → h (x , a)))

   γ : ∃ f' ꞉ (Y → (A → D)), f' ∘ j ∼ f
   γ = ∥∥-functor φ ψ

injective-∥retract∥-of-power-of-universe : (D : 𝓤 ̇ )
                                        → injective-type D 𝓤 (𝓤 ⁺)
                                        → ∥ retract D of (D → 𝓤 ̇ ) ∥
injective-∥retract∥-of-power-of-universe {𝓤} D i =
 embedding-∥retract∥ D i (D → 𝓤 ̇ ) Id Id-is-embedding

\end{code}

With this we get an almost converse to the fact that truncated
algebraic injectivity implies injectivity: the universe levels are
different in the converse:

\begin{code}

injective-gives-∥ainjective∥ : (D : 𝓤 ̇ )
                             → injective-type D 𝓤 (𝓤 ⁺)
                             → ∥ ainjective-type D 𝓤 𝓤 ∥
injective-gives-∥ainjective∥ {𝓤} D i = γ
  where
   φ : retract D of (D → 𝓤 ̇ ) → ainjective-type D 𝓤 𝓤
   φ = retract-of-ainjective D (D → 𝓤 ̇ ) (power-of-ainjective universes-are-ainjective-Π)

   γ : ∥ ainjective-type D 𝓤 𝓤 ∥
   γ = ∥∥-functor φ (injective-∥retract∥-of-power-of-universe D i)

\end{code}

So, in summary, regarding the relationship between injectivity and
truncated algebraic injectivity, so far we know that

  ∥ ainjective-type D 𝓤 𝓥  ∥ → injective-type D 𝓤 𝓥

and

  injective-type D 𝓤 (𝓤 ⁺) → ∥ ainjective-type D 𝓤 𝓤 ∥,

and hence, using propositional resizing, we get the following
characterization of a particular case of injectivity in terms of
algebraic injectivity.

Injectivity in terms of algebraic injectivity in the presence of resizing I
---------------------------------------------------------------------------

\begin{code}

injectivity-in-terms-of-ainjectivity'
 : propositional-resizing (𝓤 ⁺) 𝓤
 → (D : 𝓤 ̇ ) → injective-type D 𝓤 (𝓤 ⁺)
              ↔ ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥
injectivity-in-terms-of-ainjectivity' {𝓤} R D = a , b
  where
   a : injective-type D 𝓤 (𝓤 ⁺) → ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥
   a = ∥∥-functor (ainjective-resizing R D) ∘ injective-gives-∥ainjective∥ D

   b : ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥ → injective-type D 𝓤 (𝓤 ⁺)
   b = ∥ainjective∥-gives-injective D

\end{code}


Algebraic flabbiness and injectivity via the lifting monad
----------------------------------------------------------

We would like to do better than this. For that purpose, we consider
the lifting monad in conjunction with resizing.

\begin{code}

import Lifting.Construction
open import Lifting.Algebras
import Lifting.EmbeddingViaSIP

𝓛 : {𝓣 𝓤 : Universe} → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓛 {𝓣} {𝓤} X = Σ P ꞉ 𝓣 ̇ , (P → X) × is-prop P

𝓛-unit : {𝓣 𝓤 : Universe} (X : 𝓤 ̇ ) → X → 𝓛 {𝓣} X
𝓛-unit X x = 𝟙 , (λ _ → x) , 𝟙-is-prop

𝓛-unit-is-embedding : (X : 𝓤 ̇ ) → is-embedding (𝓛-unit {𝓣} X)
𝓛-unit-is-embedding {𝓤} {𝓣} X = Lifting.EmbeddingViaSIP.η-is-embedding'
                                  𝓣
                                  𝓤
                                  X
                                  (ua 𝓣)
                                  (fe 𝓣 𝓤)

𝓛-alg-aflabby : {𝓣 𝓤 : Universe} {A : 𝓤 ̇ } → 𝓛-alg 𝓣 A → aflabby A 𝓣
𝓛-alg-aflabby {𝓣} {𝓤} (∐ , κ , ι) P i f = ∐ i f , γ
 where
  γ : (p : P) → ∐ i f ＝ f p
  γ p = Lifting.Algebras.𝓛-alg-Law₀-gives₀'
         𝓣
         (pe 𝓣)
         (fe 𝓣 𝓣)
         (fe 𝓣 𝓤)
         ∐
         κ
         P
         i
         f
         p

𝓛-alg-ainjective : (A : 𝓤 ̇ ) → 𝓛-alg 𝓣 A → ainjective-type A 𝓣 𝓣
𝓛-alg-ainjective A α = aflabby-types-are-ainjective A (𝓛-alg-aflabby α)

free-𝓛-algebra-ainjective : (X : 𝓣 ̇ ) → ainjective-type (𝓛 {𝓣} X) 𝓣 𝓣
free-𝓛-algebra-ainjective {𝓣} X = 𝓛-alg-ainjective (𝓛 X)
                                    (Lifting.Algebras.𝓛-algebra-gives-alg 𝓣
                                    (Lifting.Algebras.free-𝓛-algebra 𝓣 (ua 𝓣) X))
\end{code}

Because the unit of the lifting monad is an embedding, it follows that
algebraically injective types are retracts of underlying objects of
free algebras:

\begin{code}

ainjective-is-retract-of-free-𝓛-algebra : (D : 𝓣 ̇ )
                                        → ainjective-type D 𝓣 (𝓣 ⁺)
                                        → retract D of (𝓛 {𝓣} D)
ainjective-is-retract-of-free-𝓛-algebra D i =
 ainjective-retract-of-subtype D i (𝓛 D) (𝓛-unit D , 𝓛-unit-is-embedding D)
\end{code}

With propositional resizing, the algebraically injective types are
precisely the retracts of the underlying objects of free algebras of
the lifting monad:

\begin{code}

ainjectives-in-terms-of-free-𝓛-algebras : (D : 𝓣 ̇ )
                                        → propositional-resizing (𝓣 ⁺) 𝓣
                                        → ainjective-type D 𝓣 𝓣
                                        ↔ (Σ X ꞉ 𝓣 ̇ , retract D of (𝓛 {𝓣} X))
ainjectives-in-terms-of-free-𝓛-algebras {𝓣} D R = a , b
  where
   a : ainjective-type D 𝓣 𝓣 → Σ X ꞉ 𝓣 ̇ , retract D of (𝓛 X)
   a i = D , ainjective-is-retract-of-free-𝓛-algebra D (ainjective-resizing R D i)

   b : (Σ X ꞉ 𝓣 ̇ , retract D of (𝓛 X)) → ainjective-type D 𝓣 𝓣
   b (X , r) = retract-of-ainjective D (𝓛 X) (free-𝓛-algebra-ainjective X) r

\end{code}


Injectivity in terms of algebraic injectivity in the presence of resizing II
----------------------------------------------------------------------------

Now, instead of propositional resizing, we consider the propositional
impredicativity of the universe 𝓤, which says that the type of
propositions in 𝓤, which lives in the next universe 𝓤 ⁺, has an
equivalent copy in 𝓤 (for the relationship between propositional
resizing and propositional impredicativity, see the module
UF.Size). We refer to this kind of impredicativity as Ω-resizing.

\begin{code}

injectivity-in-terms-of-ainjectivity : Ω-resizing 𝓤
                                     → (D  : 𝓤 ̇ ) → injective-type D 𝓤 𝓤
                                                  ↔ ∥ ainjective-type D 𝓤 𝓤 ∥
injectivity-in-terms-of-ainjectivity {𝓤} ω D = γ , ∥ainjective∥-gives-injective D
 where
  open import Lifting.Size 𝓤
  L : 𝓤 ̇
  L = pr₁ (𝓛-resizing ω D)

  e : 𝓛 D ≃ L
  e = ≃-sym(pr₂ (𝓛-resizing ω D))

  down : 𝓛 D → L
  down = ⌜ e ⌝

  down-is-embedding : is-embedding down
  down-is-embedding = equivs-are-embeddings down (⌜⌝-is-equiv e)

  ε : D → L
  ε = down ∘ 𝓛-unit D

  ε-is-embedding : is-embedding ε
  ε-is-embedding = ∘-is-embedding (𝓛-unit-is-embedding D) down-is-embedding

  injective-retract-of-L : injective-type D 𝓤 𝓤 → ∥ retract D of L ∥
  injective-retract-of-L i = embedding-∥retract∥ D i L ε ε-is-embedding

  L-ainjective : ainjective-type L 𝓤 𝓤
  L-ainjective =
   equiv-to-ainjective L (𝓛 D) (free-𝓛-algebra-ainjective D) (≃-sym e)

  φ : retract D of L → ainjective-type D 𝓤 𝓤
  φ = retract-of-ainjective D L L-ainjective

  γ : injective-type D 𝓤 𝓤 → ∥ ainjective-type D 𝓤 𝓤 ∥
  γ j = ∥∥-functor φ (injective-retract-of-L j)

\end{code}

As a corollary, by reduction to the above results about algebraic
injectivity, we have the following.

\begin{code}

injective-resizing : Ω-resizing 𝓤
                   → (𝓥 𝓦 : Universe)
                   → propositional-resizing (𝓥 ⊔ 𝓦) 𝓤
                   → (D : 𝓤 ̇ )
                   → injective-type D 𝓤 𝓤
                   → injective-type D 𝓥 𝓦
injective-resizing {𝓤} ω₀ 𝓥 𝓦 R D i = c
  where
   a : ∥ ainjective-type D 𝓤 𝓤 ∥
   a = pr₁ (injectivity-in-terms-of-ainjectivity ω₀ D) i

   b : ∥ ainjective-type D 𝓥 𝓦 ∥
   b = ∥∥-functor (ainjective-resizing R D) a

   c : injective-type D 𝓥 𝓦
   c = ∥ainjective∥-gives-injective D b

\end{code}

The equivalence of excluded middle with the (algebraic) injectivity of pointed types
------------------------------------------------------------------------------------

Algebraic flabbiness can also be applied to show that all pointed
types are (algebraically) injective iff excluded middle holds.

\begin{code}

open import UF.ClassicalLogic

EM-gives-pointed-types-aflabby : (D : 𝓦 ̇ ) → EM 𝓤 → D → aflabby D 𝓤
EM-gives-pointed-types-aflabby {𝓦} {𝓤} D em d P i f = h (em P i)
 where
  h : P + ¬ P → Σ d ꞉ D , ((p : P) → d ＝ f p)
  h (inl p) = f p , (λ q → ap f (i p q))
  h (inr n) = d , (λ p → 𝟘-elim (n p))

\end{code}

For the converse, we consider, given a proposition P, the type P + ¬ P + 𝟙,
whose algebraic flabbiness gives the decidability of P.

\begin{code}

aflabby-decidability-lemma : (P : 𝓦 ̇ )
                           → is-prop P
                           → aflabby ((P + ¬ P) + 𝟙) 𝓦
                           → P + ¬ P
aflabby-decidability-lemma {𝓦} P i φ = γ
 where
  D = (P + ¬ P) + 𝟙 {𝓦}

  f : P + ¬ P → D
  f (inl p) = inl (inl p)
  f (inr n) = inl (inr n)

  l : Σ d ꞉ D , ((z : P + ¬ P) → d ＝ f z)
  l = φ (P + ¬ P) (decidability-of-prop-is-prop (fe 𝓦 𝓤₀) i) f

  d : D
  d = pr₁ l

  κ : (z : P + ¬ P) → d ＝ f z
  κ = pr₂ l

  a : (p : P) → d ＝ inl (inl p)
  a p = κ (inl p)

  b : (n : ¬ P) → d ＝ inl (inr n)
  b n = κ (inr n)

  δ : (d' : D) → d ＝ d' → P + ¬ P
  δ (inl (inl p)) r = inl p
  δ (inl (inr n)) r = inr n
  δ (inr ⋆)       r = 𝟘-elim (m n)
   where
    n : ¬ P
    n p = 𝟘-elim (+disjoint ((a p)⁻¹ ∙ r))
    m : ¬¬ P
    m n = 𝟘-elim (+disjoint ((b n)⁻¹ ∙ r))

  γ : P + ¬ P
  γ = δ d refl

\end{code}

From this we conclude that if all pointed types are algebraically flabby then
excluded middle holds:

\begin{code}

pointed-types-aflabby-gives-EM : ((D : 𝓦 ̇ ) → D → aflabby D 𝓦)
                               → EM 𝓦
pointed-types-aflabby-gives-EM {𝓦} α P i = aflabby-decidability-lemma
                                             P i
                                             (α ((P + ¬ P) + 𝟙) (inr ⋆))

\end{code}

And then we have the same situation for algebraically injective types,
by reduction to algebraic flabbiness:

\begin{code}

EM-gives-pointed-types-ainjective : EM (𝓤 ⊔ 𝓥)
                                  → ((D : 𝓦 ̇ ) → D → ainjective-type D 𝓤 𝓥)
EM-gives-pointed-types-ainjective em D d =
 aflabby-types-are-ainjective D (EM-gives-pointed-types-aflabby D em d)

pointed-types-ainjective-gives-EM : ((D : 𝓦 ̇ ) → D → ainjective-type D 𝓦 𝓤)
                                  → EM 𝓦
pointed-types-ainjective-gives-EM α =
 pointed-types-aflabby-gives-EM (λ D d → ainjective-types-are-aflabby D (α D d))

\end{code}

And with injective types:

\begin{code}

EM-gives-pointed-types-injective : EM (𝓤 ⊔ 𝓥)
                                 → ((D : 𝓦 ̇ ) → D → injective-type D 𝓤 𝓥)
EM-gives-pointed-types-injective {𝓦} {𝓤} {𝓥} em D d =
 ainjective-gives-injective D (EM-gives-pointed-types-ainjective em D d)

pointed-types-injective-gives-EM : ((D : 𝓦 ̇ ) → D → injective-type D 𝓦 (𝓦 ⁺))
                                 → EM 𝓦
pointed-types-injective-gives-EM {𝓦} β P i = e
  where
   a : injective-type ((P + ¬ P) + 𝟙 {𝓦}) 𝓦 (𝓦 ⁺)
   a = β ((P + ¬ P) + 𝟙) (inr ⋆)

   b : ∥ ainjective-type ((P + ¬ P) + 𝟙) 𝓦 𝓦 ∥
   b = injective-gives-∥ainjective∥ ((P + ¬ P) + 𝟙) a

   c : ∥ aflabby ((P + ¬ P) + 𝟙) 𝓦 ∥
   c = ∥∥-functor (ainjective-types-are-aflabby ((P + ¬ P) + 𝟙)) b

   d : ∥ P + ¬ P ∥
   d = ∥∥-functor (aflabby-decidability-lemma P i) c

   e : P + ¬ P
   e =  ∥∥-rec (decidability-of-prop-is-prop (fe 𝓦 𝓤₀) i) id d

pointed-types-injective-gives-EM' : ((𝓤 𝓥 : Universe)
                                  → (D : 𝓦 ̇ ) → D → injective-type D 𝓤 𝓥)
                                  → EM 𝓦
pointed-types-injective-gives-EM' {𝓦} β =
 pointed-types-injective-gives-EM (β 𝓦 (𝓦 ⁺))

\end{code}

Alternatively, assuming resizing, we can be more parsimonius with the
injectivity assumption:

\begin{code}

pointed-types-injective-gives-EM'' : Ω-resizing 𝓤
                                   → ((D : 𝓤 ̇ ) → D → injective-type D 𝓤 𝓤)
                                   → EM 𝓤
pointed-types-injective-gives-EM'' {𝓤} ω β P i = e
  where
   a : injective-type ((P + ¬ P) + 𝟙) 𝓤 𝓤
   a = β ((P + ¬ P) + 𝟙) (inr ⋆)

   b : ∥ ainjective-type ((P + ¬ P) + 𝟙) 𝓤 𝓤 ∥
   b = pr₁ (injectivity-in-terms-of-ainjectivity ω ((P + ¬ P) + 𝟙)) a

   c : ∥ aflabby ((P + ¬ P) + 𝟙) 𝓤 ∥
   c = ∥∥-functor (ainjective-types-are-aflabby ((P + ¬ P) + 𝟙)) b

   d : ∥ P + ¬ P ∥
   d = ∥∥-functor (aflabby-decidability-lemma P i) c

   e : P + ¬ P
   e =  ∥∥-rec (decidability-of-prop-is-prop (fe 𝓤 𝓤₀) i) id d

\end{code}

TODO. Replace pointed by inhabited in the last two facts (probably).

TODO. Connect the above results on injectivity of universes to the
fact that they are algebras of the lifting monad, in at least two
ways, with Σ and Π as structure maps (already formulated and proved
in the lifting files available in this development).

References (in the order they are cited above)
----------

John Bourke, 2017, Equipping weak equivalences with algebraic structure.
                   https://arxiv.org/abs/1712.02523.

Toby Kenney, 2011, Injective power objects and the axiom of choice.
                   Journal of Pure and Applied Algebra Volume 215,
                   Issue 2, February 2011, Pages 131-144
                   https://www.sciencedirect.com/science/article/pii/S0022404910000782

The Univalent Foundations Program, 2013,
                   Homotopy Type Theory: Univalent Foundations of Mathematics.
                   (HoTT Book)
                   Institute for Advanced Study,
                   https://homotopytypetheory.org/book/

Voevodsky, Vladimir and Ahrens, Benedikt and Grayson, Daniel and others.
                   2014--present--future,
                   UniMath --- a computer-checked library of univalent mathematics
                   https://github.com/UniMath/UniMath

Ingo Blechschmidt, 2018, Flabby and injective objects in toposes.
                   https://arxiv.org/abs/1810.12708

Michael Shulman, 2015, Univalence for inverse diagrams and homotopy canonicity.
                   Mathematical Structures in Computer Science, 25:05 (2015),
                   p1203–1277.
                   https://arxiv.org/abs/1203.3253
                   https://home.sandiego.edu/~shulman/papers/invdia-errata.pdf (errata)

Michael Shulman, 2017, Idempotents in intensional type theory,
                   Logical Methods in Computer Science Vol 12 No. 3. (2017).
                   https://arxiv.org/abs/1507.03634

Fixities:
---------

\begin{code}

infix  7 _↓_
infix  7 _↑_
infixr 4 _≼_

\end{code}
