Martin Escardo, 30 May - 3rd June 2020. Further additions 6th July.

We look at

  * Quasidecidable propositions (generalizing semidecidable propositions).

  * The initial σ-frame.

  * The free σ-sup-lattice on one generator.

Their definitions are given below verbally and in Agda.

We work in a spartan univalent type theory with Π, Σ, +, Id, 𝟘, 𝟙, ℕ,
perhaps W-types, universes, propositional-truncation, propositional
extensionality and function extensionality - univalence is not
needed. Most of the time full univalence is not needed - propositional
and functional extenstionality suffice. Sometimes we also consider
propositional resizing, as an explicit assumption each time it is
used.

The above notions don't seem to be definable in our spartan univalent
type theory (but they are definable with higher-inductive
types). Their specifications are as follows:

  * Quasidecidable propositions.

    They are the smallest set of propositions closed under 𝟘,𝟙, and
    countable existential quantification, or countable joins in the
    frame of propositions.

    They form a dominance.

  * The initial σ-frame.

    A σ-frame has finite meets ⊤ and ∧ and countable joins ⋁, such
    that ∧ distributes over ⋁, with homomorphisms that preserve them.

  * The free σ-sup-lattice on one generator.

    A σ-sup-lattice has an empty join ⊥ and countable joins ⋁ with
    homomorphisms that preserve them. It automatically has binary
    joins, which are automatically preserved by homomorphisms, and the
    generator is automatically the maximum element.

We have:

  * The type of quasidecidable propositions exists if and only if the
    free σ-sup-lattice on one generator exists.

    The quasidecidable propositions form a dominance.

  * The free σ-sup-lattice on one generator, if it exists, is also the
    initial σ-frame.

    We have that σ-sup-lattice homomorphisms from the free
    σ-sup-lattice on one generator into a σ-frame qua σ-sup-lattice
    automatically preserve finite meets and hence are σ-frame
    homomorphisms.

  * Assuming that the free σ-sup-lattice on one generator exists, we
    have that σ-sup-lattices (and hence σ-frames) have joins of
    families indexed by quasidecidable propositions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier renaming (⊥ to ⊥Ω ; ⊤ to ⊤Ω)
open import UF.SubtypeClassifier-Properties

\end{code}

We assume function extensionality, propositional extensionality and
the existence of propositional truncations, as explicit hypotheses for
this file.

\begin{code}

module NotionsOfDecidability.QuasiDecidable
        (fe  : Fun-Ext)
        (pe  : Prop-Ext)
        (pt  : propositional-truncations-exist)
       where

open import UF.Size

import OrderedTypes.Frame
import OrderedTypes.sigma-frame
import OrderedTypes.sigma-sup-lattice

open PropositionalTruncation pt

\end{code}

The following three definitions are parametrized by a universe 𝓣,
which we may wish to be the first universe 𝓤₀ in practice.

We adopt the following notational conventions:

  * 𝓣 is the universe where the quasidecidable truth values live.

    Typically 𝓣 will be 𝓤₀ or 𝓤₁.

  * 𝓚 is the universe where the knowledge they are quasidecidable lives.
    Typically 𝓚 will be 𝓣 or 𝓣 ⁺

Recall that 𝓤, 𝓥, 𝓦, 𝓣 range over universes. We add 𝓚 to this list.

\begin{code}

variable 𝓚 : Universe

\end{code}

The notion of existence of quasidecidable propositions, formulated as
a record:

\begin{code}

record quasidecidable-propositions-exist (𝓣 𝓚 : Universe) : 𝓤ω where
 constructor
  quasidecidable-propositions

 field
  is-quasidecidable : 𝓣 ̇ → 𝓚 ̇

  being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)

  𝟘-is-quasidecidable : is-quasidecidable 𝟘

  𝟙-is-quasidecidable : is-quasidecidable 𝟙

  quasidecidable-closed-under-ω-joins
   : (P : ℕ → 𝓣 ̇ )
   → ((n : ℕ) → is-quasidecidable (P n))
   → is-quasidecidable (∃ n ꞉ ℕ , P n)

  quasidecidable-induction
   : ∀ {𝓤}
     (F : 𝓣 ̇ → 𝓤 ̇ )
   → ((P : 𝓣 ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓣 ̇ ) → is-quasidecidable P → F P

\end{code}

(It follows automatically that quasidecidable types are propositions -
see below.)

We also formulate the existence of the initial σ-frame as a record.

\begin{code}

record initial-σ-frame-exists (𝓣 : Universe) : 𝓤ω where
 constructor
  initial-σ-frame

 open OrderedTypes.sigma-frame fe

 field
  𝓐 : σ-Frame 𝓣
  𝓐-is-initial : {𝓤 : Universe} (𝓑 : σ-Frame 𝓤)
               → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩), is-σ-frame-hom 𝓐 𝓑 f

\end{code}

And finally the existence of the free σ-sup-lattice on one generator,
called ⊤ (because it will be automatically the top element).

\begin{code}

record free-σ-SupLat-on-one-generator-exists (𝓣 𝓚 : Universe) : 𝓤ω where
 constructor
  free-σ-SupLat-on-one-generator

 open OrderedTypes.sigma-sup-lattice fe

 field
  𝓐 : σ-SupLat 𝓣 𝓚
  ⊤ : ⟨ 𝓐 ⟩
  𝓐-free : {𝓥 𝓦 : Universe} (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
         → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) , is-σ-suplat-hom 𝓐 𝓑 f
                                  × (f ⊤ ＝ t)

\end{code}

The main theorems are as follows, where the proofs are given after we
have developed enough material:

\begin{code}

theorem₁ : quasidecidable-propositions-exist 𝓣 𝓚
         → free-σ-SupLat-on-one-generator-exists (𝓣 ⁺ ⊔ 𝓚) 𝓣

theorem₂ : free-σ-SupLat-on-one-generator-exists 𝓣 𝓤
         → quasidecidable-propositions-exist 𝓣 𝓣

theorem₃ : free-σ-SupLat-on-one-generator-exists 𝓣 𝓚
         → initial-σ-frame-exists 𝓣

theorem₄ : Propositional-Resizing
         → quasidecidable-propositions-exist 𝓣 𝓚

\end{code}

  * We first work with a hypothetical collection of quasidecidable
    propositions and show that they form the initial σ-frame.

    This is in the submodule hypothetical-quasidecidability.

  * Then we construct it assuming propositional resizing.

    This is in the submodule quasidecidability-construction-from-resizing.

  * Assuming a hypothetical free σ-sup-lattice on one generator, it is
    automatically the initial σ-frame, and from it we can define the
    notion of quasidecidable proposition.

Can we construct them without resizing and without higher-inductive
types other than propositional truncation?

\begin{code}

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.Powerset
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Yoneda

open import Dominance.Definition

\end{code}

Digression. Before considering quasidecidable propositions, we review
semidecidable ones.

A proposition is semidecidable if it is a countable join of decidable
propositions. See the paper
https://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf
by Martin Escardo and Cory Knapp.

NB. Semidecidable propositions are called Rosolini propositions in the
above reference.

\begin{code}

is-semidecidable : 𝓤 ̇ → 𝓤 ̇
is-semidecidable X = ∃ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ＝ ₁)

\end{code}

Exercise. X is semidecidable iff it is a countable join of decidable
propositions:

\begin{code}

is-semidecidable' : 𝓤 ̇ → 𝓤 ⁺ ̇
is-semidecidable' {𝓤} X = ∃ A ꞉ (ℕ → 𝓤 ̇ )
                              , ((n : ℕ) → is-decidable (A n))
                              × (X ≃ (∃ n ꞉ ℕ , A n))

\end{code}

The following shows that we need to truncate, because the Cantor type
(ℕ → 𝟚) is certainly not the type of semidecidable propositions:

\begin{code}

semidecidability-data : 𝓤 ̇ → 𝓤 ̇
semidecidability-data X = Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ＝ ₁)

module only-use-of-univalence-in-this-file where

 open import UF.Univalence

 totality-of-semidecidability-data
  : is-univalent 𝓤₀
  → (Σ X ꞉ 𝓤₀ ̇ , semidecidability-data X) ≃ (ℕ → 𝟚)
 totality-of-semidecidability-data ua =

   (Σ X ꞉ 𝓤₀ ̇ , Σ α ꞉ (ℕ → 𝟚), X ≃ (∃ n ꞉ ℕ , α n ＝ ₁)) ≃⟨ i ⟩
   (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , X ≃ (∃ n ꞉ ℕ , α n ＝ ₁)) ≃⟨ ii ⟩
   (Σ α ꞉ (ℕ → 𝟚), Σ X ꞉ 𝓤₀ ̇ , (∃ n ꞉ ℕ , α n ＝ ₁) ≃ X) ≃⟨ iii ⟩
   (ℕ → 𝟚) × 𝟙 {𝓤₀}                                      ≃⟨ iv ⟩
   (ℕ → 𝟚)                                               ■
  where
   i   = Σ-flip
   ii  = Σ-cong (λ α → Σ-cong (λ X → ≃-Sym'' (univalence-gives-funext ua)))
   iii = Σ-cong (λ α → singleton-≃-𝟙
                        (univalence-via-singletons→
                          ua
                          (∃ n ꞉ ℕ , α n ＝ ₁)))
   iv  = 𝟙-rneutral

\end{code}

End of module only-use-of-univalence-in-this-file.

\begin{code}

𝓢 : 𝓤₁ ̇
𝓢 = Σ X ꞉ 𝓤₀ ̇ , is-semidecidable X

\end{code}

The type 𝓢 of semidecidable propositions is not a σ-frame unless we
have enough countable choice - see the Escardo-Knapp reference above.

End of digression.

The set of quasidecidable propositions, if it exists, is the smallest
collection of propositions containing 𝟘 and 𝟙 and closed under
countable joins.

Exercise. It exists under propositional resizing assumptions (just
take the intersection of all subsets with 𝟘 and 𝟙 as members and
closed under countable joins). This exercise is solved below in the
submodule quasidecidability-construction-from-resizing.

We now assume that there is a such a smallest collection of types,
called quasidecidable, satisfying the above closure property. The
types in this collection are automatically propositions. The
minimality condition of the collection amounts to an induction
principle.

We recall the above conventions:

  * 𝓣 is the universe where the quasidecidable truth values live.

    Typically 𝓣 will be 𝓤₀ or 𝓤₁.

  * 𝓚 is the universe where the knowledge they are quasidecidable lives.

    Typically 𝓚 will be 𝓣 or 𝓣⁺.

\begin{code}

module hypothetical-quasidecidability
        {𝓣 𝓚 : Universe}
        (qde : quasidecidable-propositions-exist 𝓣 𝓚)
       where

\end{code}

As promised, the quasidecidable types are automatically propositions,
with a proof by induction:

\begin{code}

 open quasidecidable-propositions-exist qde

 quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
 quasidecidable-types-are-props = quasidecidable-induction
                                   is-prop
                                   (λ _ → being-prop-is-prop fe)
                                   𝟘-is-prop
                                   𝟙-is-prop
                                   (λ P φ → ∃-is-prop)

\end{code}

We collect the quasidecidable propositions in the type 𝓠:

\begin{code}

 𝓠 : 𝓣 ⁺ ⊔ 𝓚 ̇
 𝓠 = Σ P ꞉ 𝓣 ̇ , is-quasidecidable P

 _is-true : 𝓠 → 𝓣 ̇
 _is-true (P , i) = P

 being-true-is-quasidecidable : (𝕡 : 𝓠) → is-quasidecidable (𝕡 is-true)
 being-true-is-quasidecidable (P , i) = i

 being-true-is-prop : (𝕡 : 𝓠) → is-prop (𝕡 is-true)
 being-true-is-prop (P , i) = quasidecidable-types-are-props P i

 𝓠-to-Ω : 𝓠 → Ω 𝓣
 𝓠-to-Ω (P , i) = P , quasidecidable-types-are-props P i

 𝓠-to-Ω-is-embedding : is-embedding 𝓠-to-Ω
 𝓠-to-Ω-is-embedding = NatΣ-is-embedding
                        is-quasidecidable
                        is-prop
                        ζ
                        ζ-is-embedding
  where
   ζ : (P : 𝓣 ̇ ) → is-quasidecidable P → is-prop P
   ζ = quasidecidable-types-are-props

   ζ-is-embedding : (P : 𝓣 ̇ ) → is-embedding (ζ P)
   ζ-is-embedding P = maps-of-props-are-embeddings (ζ P)
                       (being-quasidecidable-is-prop P)
                       (being-prop-is-prop fe)

 𝓠-is-set : is-set 𝓠
 𝓠-is-set = subtypes-of-sets-are-sets 𝓠-to-Ω
             𝓠-to-Ω-is-embedding
             (Ω-is-set fe pe)

 ⊥ : 𝓠
 ⊥ = 𝟘 , 𝟘-is-quasidecidable

 ⊤ : 𝓠
 ⊤ = 𝟙 , 𝟙-is-quasidecidable

 ⋁ : (ℕ → 𝓠) → 𝓠
 ⋁ 𝕡 = (∃ n ꞉ ℕ , 𝕡 n is-true) ,
       quasidecidable-closed-under-ω-joins
        (λ n → 𝕡 n is-true)
        (λ n → being-true-is-quasidecidable (𝕡 n))

\end{code}

We formulate and prove induction on 𝓠 in two different, equivalent
ways.

\begin{code}

 𝓠-induction : (G : 𝓠 → 𝓤 ̇ )
             → ((𝕡 : 𝓠) → is-prop (G 𝕡))
             → G ⊥
             → G ⊤
             → ((𝕡 : ℕ → 𝓠) → ((n : ℕ) → G (𝕡 n)) → G (⋁ 𝕡))
             → (𝕡 : 𝓠) → G 𝕡
 𝓠-induction {𝓤} G G-is-prop-valued g₀ g₁ gω (P , i) = γ
  where
   F :  𝓣 ̇ → 𝓚 ⊔ 𝓤 ̇
   F P = Σ j ꞉ is-quasidecidable P , G (P , j)

   F-is-prop-valued : ∀ P → is-prop (F P)
   F-is-prop-valued P = Σ-is-prop
                         (being-quasidecidable-is-prop P)
                         (λ j → G-is-prop-valued (P , j))

   F₀ : F 𝟘
   F₀ = 𝟘-is-quasidecidable , g₀

   F₁ : F 𝟙
   F₁ = 𝟙-is-quasidecidable , g₁

   Fω : (Q : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (Q n)) → F (∃ n ꞉ ℕ , Q n)
   Fω Q φ = quasidecidable-closed-under-ω-joins Q (λ n → pr₁ (φ n)) ,
            gω (λ n → (Q n , pr₁ (φ n))) (λ n → pr₂ (φ n))

   δ : Σ j ꞉ is-quasidecidable P , G (P , j)
   δ = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω P i

   j : is-quasidecidable P
   j = pr₁ δ

   g : G (P , j)
   g = pr₂ δ

   r : j ＝ i
   r = being-quasidecidable-is-prop P j i

   γ : G (P , i)
   γ = transport (λ - → G (P , -)) r g


 𝓠-induction' : (𝓖 : 𝓠 → Ω 𝓤)
              → ⊥ ∈ 𝓖
              → ⊤ ∈ 𝓖
              → ((𝕡 : ℕ → 𝓠) → ((n : ℕ) → 𝕡 n ∈ 𝓖) → ⋁ 𝕡 ∈ 𝓖)
              → (𝕡 : 𝓠) → 𝕡 ∈ 𝓖
 𝓠-induction' {𝓤} 𝓖 = 𝓠-induction (λ 𝕡 → pr₁ (𝓖 𝕡)) (λ 𝕡 → pr₂ (𝓖 𝕡))

\end{code}

The quasidecidable propositions form a dominance, with a proof by
quasidecidable-induction. The main dominance condition generalizes
closure under binary products (that is, conjunctions, or meets):

\begin{code}

 quasidecidable-types-form-a-dominance
  : (P : 𝓣 ̇ )
  → is-quasidecidable P
  → (Q : 𝓣 ̇ )
  → (P → is-quasidecidable Q)
  → is-quasidecidable (P × Q)
 quasidecidable-types-form-a-dominance
  = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω
  where
   F : 𝓣 ̇ → 𝓣 ⁺ ⊔ 𝓚 ̇
   F P = (Q : 𝓣 ̇ ) → (P → is-quasidecidable Q) → is-quasidecidable (P × Q)

   F-is-prop-valued : (P : 𝓣 ̇ ) → is-prop (F P)
   F-is-prop-valued P = Π₂-is-prop fe
                         (λ Q _ → being-quasidecidable-is-prop (P × Q))

   F₀ : F 𝟘
   F₀ Q φ = transport is-quasidecidable r 𝟘-is-quasidecidable
    where
     r : 𝟘 ＝ 𝟘 × Q
     r = pe 𝟘-is-prop (λ (z , q) → 𝟘-elim z) unique-from-𝟘 pr₁

   F₁ : F 𝟙
   F₁ Q φ = transport is-quasidecidable r (φ ⋆)
    where
     i : is-prop Q
     i = quasidecidable-types-are-props Q (φ ⋆)

     r : Q ＝ 𝟙 × Q
     r = pe i (×-is-prop 𝟙-is-prop i) (λ q → (⋆ , q)) pr₂

   Fω :  (P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n)
   Fω P f Q φ = γ
    where
     φ' : (n : ℕ) → P n → is-quasidecidable Q
     φ' n p = φ ∣ n , p ∣

     a : (n : ℕ) → is-quasidecidable (P n × Q)
     a n = f n Q (φ' n)

     b : is-quasidecidable (∃ n ꞉ ℕ , P n × Q)
     b = quasidecidable-closed-under-ω-joins (λ n → P n × Q) a

     c : (∃ n ꞉ ℕ , P n × Q) → ((∃ n ꞉ ℕ , P n) × Q)
     c s = (t , q)
      where
       t : ∃ n ꞉ ℕ , P n
       t = ∥∥-rec ∃-is-prop (λ (n , (p , q)) → ∣ n , p ∣) s

       i : is-prop Q
       i = quasidecidable-types-are-props Q (φ t)

       q : Q
       q = ∥∥-rec i (λ (n , (p , q)) → q) s

     d : ((∃ n ꞉ ℕ , P n) × Q) → (∃ n ꞉ ℕ , P n × Q)
     d (t , q) = ∥∥-functor (λ (n , p) → n , (p , q)) t

     r : (∃ n ꞉ ℕ , P n × Q) ＝ ((∃ n ꞉ ℕ , P n) × Q)
     r = pe ∃-is-prop
            (×-prop-criterion
              ((λ _ → ∃-is-prop) ,
              (λ e → quasidecidable-types-are-props Q (φ e))))
            c
            d

     γ : is-quasidecidable ((∃ n ꞉ ℕ , P n) × Q)
     γ = transport is-quasidecidable r b

\end{code}

This condition automatically implies closure under Σ, or joins indexed
by quasidecidable propositions:

\begin{code}

 quasidecidable-closed-under-Σ
  : (P : 𝓣 ̇ )
  → (Q : P → 𝓣 ̇ )
  → is-quasidecidable P
  → ((p : P) → is-quasidecidable (Q p))
  → is-quasidecidable (Σ Q)
 quasidecidable-closed-under-Σ
  = D3-and-D5'-give-D5 pe is-quasidecidable
     (quasidecidable-types-are-props)
     (λ P Q' i → quasidecidable-types-form-a-dominance P i Q')

\end{code}

Notice that Σ Q is equivalent to ∃ Q as quasidecidable types are
propositions, and propositions are closed under Σ:

\begin{code}

 NB : (P : 𝓣 ̇ )
    → (Q : P → 𝓣 ̇ )
    → is-quasidecidable P
    → ((p : P) → is-quasidecidable (Q p))
    → Σ Q ≃ ∃ Q
 NB P Q i j = logically-equivalent-props-are-equivalent
               k
               ∃-is-prop
               (λ (p , q) → ∣ p , q ∣)
               (∥∥-rec k id)
  where
   k : is-prop (Σ Q)
   k = quasidecidable-types-are-props
        (Σ Q)
        (quasidecidable-closed-under-Σ P Q i j)

\end{code}

The following summarizes the dominance conditions:

\begin{code}

 quasidecidability-is-dominance : is-dominance is-quasidecidable
 quasidecidability-is-dominance = being-quasidecidable-is-prop ,
                                  quasidecidable-types-are-props ,
                                  𝟙-is-quasidecidable ,
                                  quasidecidable-closed-under-Σ
\end{code}

We now give the quasidecidable propositions the structure of a
σ-sup-lattice. We have already defined ⊥, ⊤ and ⋁.

\begin{code}

 _≤_ : 𝓠 → 𝓠 → 𝓣 ̇
 𝕡 ≤ 𝕢 = 𝕡 is-true → 𝕢 is-true

 ≤-is-prop-valued : (𝕡 𝕢 : 𝓠) → is-prop (𝕡 ≤ 𝕢)
 ≤-is-prop-valued 𝕡 𝕢 = Π-is-prop fe (λ _ → being-true-is-prop 𝕢)

 ≤-refl : (𝕡 : 𝓠) → 𝕡 ≤ 𝕡
 ≤-refl 𝕡 = id

 ≤-trans : (𝕡 𝕢 𝕣 : 𝓠) → 𝕡 ≤ 𝕢 → 𝕢 ≤ 𝕣 → 𝕡 ≤ 𝕣
 ≤-trans 𝕡 𝕢 𝕣 l m = m ∘ l

 ≤-antisym : (𝕡 𝕢 : 𝓠) → 𝕡 ≤ 𝕢 → 𝕢 ≤ 𝕡 → 𝕡 ＝ 𝕢
 ≤-antisym 𝕡 𝕢 l m = to-subtype-＝
                      being-quasidecidable-is-prop
                      (pe (being-true-is-prop 𝕡) (being-true-is-prop 𝕢) l m)

 ⊥-is-minimum : (𝕡 : 𝓠) → ⊥ ≤ 𝕡
 ⊥-is-minimum 𝕡 = unique-from-𝟘

 ⊤-is-maximum : (𝕡 : 𝓠) → 𝕡 ≤ ⊤
 ⊤-is-maximum 𝕡 = unique-to-𝟙

 ⋁-is-ub : (𝕡 : ℕ → 𝓠) → (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
 ⋁-is-ub 𝕡 n = (λ p → ∣ n , p ∣)

 ⋁-is-lb-of-ubs : (𝕡 : ℕ → 𝓠) → (𝕦 : 𝓠) → ((n : ℕ) → 𝕡 n ≤ 𝕦) → ⋁ 𝕡 ≤ 𝕦
 ⋁-is-lb-of-ubs 𝕡 (U , i) φ = γ
  where
   δ : (Σ n ꞉ ℕ , 𝕡 n is-true) → U
   δ (n , p) = φ n p

   γ : (∃ n ꞉ ℕ , 𝕡 n is-true) → U
   γ = ∥∥-rec (quasidecidable-types-are-props U i) δ

\end{code}

Putting these axioms together we get the σ-sup-lattice of
quasidecidable propositions:

\begin{code}

 open import OrderedTypes.sigma-sup-lattice fe

 QD : σ-SupLat (𝓣 ⁺ ⊔ 𝓚) 𝓣
 QD = 𝓠 ,
     (⊥ , ⋁) ,
     _≤_ ,
     ≤-is-prop-valued ,
     ≤-refl ,
     ≤-trans ,
     ≤-antisym ,
     ⊥-is-minimum ,
     ⋁-is-ub ,
     ⋁-is-lb-of-ubs

\end{code}

We now show that QD is the free σ-sup-lattice on one generator. For
this purpose, we assume that we are give a σ-sup-lattice 𝓐 with a
distinguished element t.

\begin{code}

 module _ {𝓤 𝓥 : Universe}
          (𝓐 : σ-SupLat 𝓤 𝓥)
          (t : ⟨ 𝓐 ⟩)
        where

\end{code}

We introduce some abbreviations, private to this anonymous module, for
notational convenience:

\begin{code}

  private

    A = ⟨ 𝓐 ⟩
    ⊥' = ⊥⟨ 𝓐 ⟩
    ⋁' = ⋁⟨ 𝓐 ⟩
    _≤'_ : A → A → 𝓥 ̇
    a ≤' b = a ≤⟨ 𝓐 ⟩ b

\end{code}

And then, again by 𝓠-induction, there is at most one homomorphism from
𝓠 to 𝓐:

\begin{code}

  at-most-one-hom : (g h : 𝓠 → A)
                  → is-σ-suplat-hom QD 𝓐 g
                  → is-σ-suplat-hom QD 𝓐 h
                  → g ⊤ ＝ t
                  → h ⊤ ＝ t
                  → g ＝ h
  at-most-one-hom g h (g⊥ , g⋁) (h⊥ , h⋁) g⊤ h⊤ = dfunext fe r
   where
    i₀ = g ⊥ ＝⟨ g⊥ ⟩
         ⊥'  ＝⟨ h⊥ ⁻¹ ⟩
         h ⊥ ∎

    i₁ = g ⊤ ＝⟨ g⊤ ⟩
         t   ＝⟨ h⊤ ⁻¹ ⟩
         h ⊤ ∎

    iω : (𝕡 : ℕ → 𝓠) → ((n : ℕ) → g (𝕡 n) ＝ h (𝕡 n)) → g (⋁ 𝕡) ＝ h (⋁ 𝕡)
    iω 𝕡 φ = g (⋁ 𝕡)          ＝⟨ g⋁ 𝕡 ⟩
             ⋁' (n ↦ g (𝕡 n)) ＝⟨ ap ⋁' (dfunext fe φ) ⟩
             ⋁' (n ↦ h (𝕡 n)) ＝⟨ (h⋁ 𝕡)⁻¹ ⟩
             h (⋁ 𝕡)          ∎

    r : g ∼ h
    r = 𝓠-induction (λ 𝕡 → g 𝕡 ＝ h 𝕡) (λ 𝕡 → ⟨ 𝓐 ⟩-is-set {g 𝕡} {h 𝕡}) i₀ i₁ iω

\end{code}

The condition in the conclusion of the following lemma says that the
element a : A is the least upper bound of the (weakly) constant family
λ (p : P) → t.  Because least upper bounds are unique when they
exist, the type in the conclusion of the lemma is a proposition. This
is crucial because the induction principle can be applied to
proposition-valued predicates only.

\begin{code}

  freeness-lemma : (P : 𝓣 ̇ )
                 → is-quasidecidable P
                 → Σ a ꞉ A , (P → t ≤' a) × ((u : A) → (P → t ≤' u) → a ≤' u)
  freeness-lemma = quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω
   where
    F : 𝓣 ̇ → 𝓣 ⊔ 𝓤 ⊔ 𝓥 ̇
    F P = Σ a ꞉ A , (P → t ≤' a) × ((u : A) → (P → t ≤' u) → a ≤' u)

    F-is-prop-valued : (P : 𝓣 ̇ ) → is-prop (F P)
    F-is-prop-valued P (a , α , β) (a' , α' , β') = γ
     where
      j : (a : A) → is-prop ((P → t ≤' a) × ((u : A) → (P → t ≤' u) → a ≤' u))
      j a = ×-is-prop
             (Π-is-prop fe (λ _ → ⟨ 𝓐 ⟩-order-is-prop-valued t a))
             (Π₂-is-prop fe (λ u _ → ⟨ 𝓐 ⟩-order-is-prop-valued a u))

      r : a ＝ a'
      r = ⟨ 𝓐 ⟩-antisym a a' (β  a' α') (β' a α)

      γ : (a , α , β) ＝ (a' , α' , β')
      γ = to-subtype-＝ j r

    F₀ : F 𝟘
    F₀ = ⊥' , unique-from-𝟘 , (λ u ψ → ⟨ 𝓐 ⟩-⊥-is-minimum u)

    F₁ : F 𝟙
    F₁ = t , (λ _ → ⟨ 𝓐 ⟩-refl t) , (λ u ψ → ψ ⋆)

    Fω :  (P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n)
    Fω P φ = a∞ , α∞ , β∞
     where
      a : ℕ → A
      a n = pr₁ (φ n)

      α : (n : ℕ) → P n → t ≤' a n
      α n = pr₁ (pr₂ (φ n))

      β : (n : ℕ) (u : A) → (P n → t ≤' u) → a n ≤' u
      β n = pr₂ (pr₂ (φ n))

      a∞ : A
      a∞ = ⋁' a

      α∞ : (∃ n ꞉ ℕ , P n) → t ≤' a∞
      α∞ = ∥∥-rec (⟨ 𝓐 ⟩-order-is-prop-valued t a∞)  α∞'
       where
        α∞' : (Σ n ꞉ ℕ , P n) → t ≤' a∞
        α∞' (n , p) = ⟨ 𝓐 ⟩-trans t (a n) a∞ (α n p) (⟨ 𝓐 ⟩-⋁-is-ub a n)

      β∞ : (u : A) → ((∃ n ꞉ ℕ , P n) → t ≤' u) → a∞ ≤' u
      β∞ u ψ = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a u l
       where
        l : (n : ℕ) → a n ≤' u
        l n = β n u (λ p → ψ ∣ n , p ∣)

\end{code}

We now have enough constructions and lemmas to show that the type of
quasidecidable propositions is the free σ-sup-lattice on one
generator. It remains to show that the function 𝓠 → A induced by the
initiality lemma is a σ-sup-lattice homomorphism.

\begin{code}

  QD-is-free-σ-SupLat : ∃! f ꞉ (⟨ QD ⟩ → ⟨ 𝓐 ⟩) , is-σ-suplat-hom QD 𝓐 f
                                                × (f ⊤ ＝ t)
  QD-is-free-σ-SupLat = γ
   where
    f : 𝓠 → A
    f (P , i) = pr₁ (freeness-lemma P i)

    α : (𝕡 : 𝓠) → 𝕡 is-true → t ≤' f 𝕡
    α (P , i) = pr₁ (pr₂ (freeness-lemma P i))

    β : (𝕡 : 𝓠) → ((u : A) → (𝕡 is-true → t ≤' u) → f 𝕡 ≤' u)
    β (P , i) = pr₂ (pr₂ (freeness-lemma P i))

\end{code}

The conditions α and β on f are crucial to prove that f is indeed a
homomorphism, and are all we need for that purpose.

\begin{code}

    f⊤ : f ⊤ ＝ t
    f⊤ = ⟨ 𝓐 ⟩-antisym (f ⊤) t (β ⊤ t (λ _ → ⟨ 𝓐 ⟩-refl t)) (α ⊤ ⋆)

    f⊥ : f ⊥ ＝ ⊥'
    f⊥ = ⟨ 𝓐 ⟩-antisym (f ⊥) ⊥' (β ⊥ ⊥' unique-from-𝟘) (⟨ 𝓐 ⟩-⊥-is-minimum (f ⊥))

    f-is-monotone : (𝕡 𝕢 : 𝓠) → 𝕡 ≤ 𝕢 → f 𝕡 ≤' f 𝕢
    f-is-monotone 𝕡 𝕢 l = β 𝕡 (f 𝕢) (λ p → α 𝕢 (l p))

    f⋁ : (𝕡 : ℕ → 𝓠) → f (⋁ 𝕡) ＝ ⋁' (n ↦ f (𝕡 n))
    f⋁ 𝕡 = ⟨ 𝓐 ⟩-antisym (f (⋁ 𝕡)) (⋁' (n ↦ f (𝕡 n))) v w
      where
       φ' : (Σ n ꞉ ℕ , 𝕡 n is-true) → t ≤' ⋁' (n ↦ f (𝕡 n))
       φ' (n , p) = ⟨ 𝓐 ⟩-trans t (f (𝕡 n)) (⋁' (n ↦ f (𝕡 n))) r s
        where
         r : t ≤' f (𝕡 n)
         r = α (𝕡 n) p

         s : f (𝕡 n) ≤' ⋁' (n ↦ f (𝕡 n))
         s = ⟨ 𝓐 ⟩-⋁-is-ub (n ↦ f (𝕡 n)) n

       φ : (∃ n ꞉ ℕ , 𝕡 n is-true) → t ≤' ⋁' (n ↦ f (𝕡 n))
       φ = ∥∥-rec (⟨ 𝓐 ⟩-order-is-prop-valued _ _) φ'

       v : f (⋁ 𝕡) ≤' ⋁' (n ↦ f (𝕡 n))
       v = β (⋁ 𝕡) (⋁' (n ↦ f (𝕡 n))) φ

       l : (n : ℕ) → 𝕡 n ≤ ⋁ 𝕡
       l = ⋁-is-ub 𝕡

       m : (n : ℕ) → f (𝕡 n) ≤' f (⋁ 𝕡)
       m n = f-is-monotone (𝕡 n) (⋁ 𝕡) (l n)

       w : ⋁' (n ↦ f (𝕡 n)) ≤' f (⋁ 𝕡)
       w = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (n ↦ f (𝕡 n)) (f (⋁ 𝕡)) m

\end{code}

And then we are done:

\begin{code}

    f-is-hom : is-σ-suplat-hom QD 𝓐 f
    f-is-hom = f⊥ , f⋁

    γ : ∃! f ꞉ (⟨ QD ⟩ → A) , is-σ-suplat-hom QD 𝓐 f
                            × (f ⊤ ＝ t)
    γ = (f , f-is-hom , f⊤) ,
        (λ (g , g-is-hom , g⊤) → to-subtype-＝
                                  (λ f → ×-is-prop
                                          (being-σ-suplat-hom-is-prop QD 𝓐 f)
                                          ⟨ 𝓐 ⟩-is-set)
                                  (at-most-one-hom f g f-is-hom g-is-hom f⊤ g⊤))
\end{code}

This concludes the module hypothetical-quasidecidability.

We discussed above the specification of the notion of quasidecidable
proposition. But can we define or construct it? Yes if, for example,
propositional resizing is available:

\begin{code}

module quasidecidability-construction-from-resizing
        (𝓣 𝓚 : Universe)
        (ρ : Propositional-Resizing)
       where

 open import UF.Powerset-Resizing fe ρ

\end{code}

This assumption says that any proposition in the universe 𝓤 is
equivalent to some proposition in the universe 𝓥, for any two
universes 𝓤 and 𝓥.

The crucial fact exploited here is that intersections of collections
of subcollections 𝓐 : 𝓟 (𝓟 X) exist under propositional resizing.

To define the type of quasi-decidable propositions, we take the
intersection of the collections of types satisfying the following
closure condition:

\begin{code}

 QD-closed-types : (𝓤 ̇ → Ω 𝓥) → Ω (𝓤 ⁺ ⊔ 𝓥)
 QD-closed-types {𝓤} {𝓥} A = closure-condition , i
  where
   closure-condition : 𝓤 ⁺ ⊔ 𝓥 ̇
   closure-condition =
      (𝟘 ∈ A)
    × (𝟙 ∈ A)
    × ((P : ℕ → 𝓤 ̇ ) → ((n : ℕ) → P n ∈ A) → (∃ n ꞉ ℕ , P n) ∈ A)

   i : is-prop closure-condition
   i = ×₃-is-prop
        (∈-is-prop A 𝟘)
        (∈-is-prop A 𝟙)
        (Π₂-is-prop fe (λ P _ → ∈-is-prop A (∃ n ꞉ ℕ , P n)))

 is-quasidecidable : 𝓣 ̇ → 𝓚 ̇
 is-quasidecidable P = P ∈ ⋂ QD-closed-types

 being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)
 being-quasidecidable-is-prop = ∈-is-prop (⋂ QD-closed-types)

 𝟘-is-quasidecidable : is-quasidecidable 𝟘
 𝟘-is-quasidecidable = to-⋂ QD-closed-types 𝟘 (λ A (c₀ , c₁ , cω) → c₀)

 𝟙-is-quasidecidable : is-quasidecidable 𝟙
 𝟙-is-quasidecidable = to-⋂ QD-closed-types 𝟙 (λ A (c₀ , c₁ , cω) → c₁)

 quasidecidable-closed-under-ω-joins : (P : ℕ → 𝓣 ̇ )
                                     → ((n : ℕ) → is-quasidecidable (P n))
                                     → is-quasidecidable (∃ n ꞉ ℕ , P n)
 quasidecidable-closed-under-ω-joins P φ = to-⋂ QD-closed-types (∃ P) vi
  where
   i : (n : ℕ) → P n ∈ ⋂ QD-closed-types
   i = φ

   ii : (n : ℕ) (A : 𝓣 ̇ → Ω 𝓚) → A ∈ QD-closed-types → P n ∈ A
   ii n = from-⋂ QD-closed-types (P n) (i n)

   iii : (A : 𝓣 ̇ → Ω 𝓚) → A ∈ QD-closed-types → ∃ P ∈ A
   iii A (c₁ , c₂ , cω) = cω P (λ n → ii n A (c₁ , c₂ , cω))

   iv : ∃ P ∈ ⋂ QD-closed-types
   iv = to-⋂ QD-closed-types (∃ P) iii

   vi : (A : 𝓣 ̇ → Ω 𝓚) → A ∈ QD-closed-types → ∃ P ∈ A
   vi = from-⋂ QD-closed-types (∃ P) iv

\end{code}

The full induction principle requires a further application of
resizing. We first prove a particular case and then reduce the general
case to this particular case.

\begin{code}

 quasidecidable-induction₀
  : (F : 𝓣 ̇ → 𝓚 ̇ )
  → ((P : 𝓣 ̇ ) → is-prop (F P))
  → F 𝟘
  → F 𝟙
  → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
  → (P : 𝓣 ̇ ) →  is-quasidecidable P → F P
 quasidecidable-induction₀ F F-is-prop-valued F₀ F₁ Fω P P-is-quasidecidable
  = γ
  where
   A : (P : 𝓣 ̇ ) → Ω 𝓚
   A P = F P , F-is-prop-valued P

   A-is-QD-closed : A ∈ QD-closed-types
   A-is-QD-closed = F₀ , F₁ , Fω

   pqd : P ∈ ⋂ QD-closed-types
   pqd = P-is-quasidecidable

   δ : P ∈ A
   δ = from-⋂ QD-closed-types P pqd A A-is-QD-closed

   γ : F P
   γ = δ

\end{code}

To get the full induction principle we apply the above particular case
with back and forth resizing coercions. The point is that now F has
values in any universe 𝓤 rather than the universe 𝓚 as above.

\begin{code}

 quasidecidable-induction
  : {𝓤 : Universe}
    (F : 𝓣 ̇ → 𝓤 ̇ )
  → ((P : 𝓣 ̇ ) → is-prop (F P))
  → F 𝟘
  → F 𝟙
  → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
  → (P : 𝓣 ̇ ) → is-quasidecidable P → F P
 quasidecidable-induction {𝓤} F F-is-prop F₀ F₁ Fω P P-is-quasidecidable = γ
  where
   i = F-is-prop

   F' : 𝓣 ̇ → 𝓚 ̇
   F' P = resize ρ (F P) (i P)

   i' : (P : 𝓣 ̇ ) → is-prop (F' P)
   i' P = resize-is-prop ρ (F P) (i P)

   δ : F' P
   δ = quasidecidable-induction₀
        F'
        i'
        (to-resize ρ (F 𝟘) (i 𝟘) F₀)
        (to-resize ρ (F 𝟙) (i 𝟙) F₁)
        (λ P Q → to-resize ρ
                  (F (∃ P))
                  (i (∃ P))
                  (Fω P (λ n → from-resize ρ
                                (F (P n))
                                (i (P n))
                                (Q n))))
        P
        P-is-quasidecidable

   γ : F P
   γ = from-resize ρ (F P) (i P) δ

\end{code}

Hence the free σ-sup-lattice on one generator exists under
propositional resizing: we simply plug the construction of the
quasidecidable propositions to the above hypothetical development.

\begin{code}

 open OrderedTypes.sigma-sup-lattice fe

 free-σ-suplat-on-one-generator-exists
  : Σ 𝓐 ꞉ σ-SupLat (𝓣 ⁺ ⊔ 𝓚) 𝓣
  , Σ t ꞉ ⟨ 𝓐 ⟩
  , ((𝓑 : σ-SupLat 𝓤 𝓥) (u : ⟨ 𝓑 ⟩)
        → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) , is-σ-suplat-hom 𝓐 𝓑 f
                                  × (f t ＝ u))
 free-σ-suplat-on-one-generator-exists {𝓤} {𝓥}
  = QD , ⊤ , QD-is-free-σ-SupLat
  where
   open hypothetical-quasidecidability
         (quasidecidable-propositions
           is-quasidecidable
           being-quasidecidable-is-prop
           𝟘-is-quasidecidable
           𝟙-is-quasidecidable
           quasidecidable-closed-under-ω-joins
           quasidecidable-induction)

\end{code}

This concludes the module quasidecidability-construction-from-resizing.

The initial σ-frame can also be constructed as a higher-inductive
type, as is well known.

The σ-sup-lattice on one generator is automatically the initial
σ-frame. This is shown below.

TODO. Write in Agda some of the proofs of the above reference with
Cory Knapp, particularly regarding choice. E.g. the semidecidable
properties form a dominance if and only if a certain particular case
of countable choice holds.

TODO. This certain particular case of countable choice holds if and
only if the quasidecidable propositions are semidecidable. This is not
in the paper, but the methods of proof of the paper should apply more
or less directly.

Question. Can we construct the collection of quasidecidable
propositions without resizing and without higher-inductive types other
than propositional truncation?

We now explore the consequences of the hypothetical existence of a
free σ-sup-lattice on one generator ⊤.

\begin{code}

module hypothetical-free-σ-SupLat-on-one-generator where

 open import OrderedTypes.sigma-sup-lattice fe

 module assumptions
         {𝓣 𝓚 : Universe}
         (𝓐 : σ-SupLat 𝓣 𝓚)
         (⊤ : ⟨ 𝓐 ⟩)
         (𝓐-free : {𝓥 𝓦 : Universe} (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
                 → ∃! f ꞉ (⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩) , is-σ-suplat-hom 𝓐 𝓑 f
                                          × (f ⊤ ＝ t))
        where

\end{code}

We first introduce some abbreviations:

\begin{code}

  private
   A   = ⟨ 𝓐 ⟩
   ⊥   = ⊥⟨ 𝓐 ⟩
   ⋁  = ⋁⟨ 𝓐 ⟩

  _≤_ : A → A → 𝓚 ̇
  a ≤ b = a ≤⟨ 𝓐 ⟩ b

  σ-rec : (𝓑 : σ-SupLat 𝓥 𝓦) → ⟨ 𝓑 ⟩ → ⟨ 𝓐 ⟩ → ⟨ 𝓑 ⟩
  σ-rec 𝓑 t = pr₁ (center (𝓐-free 𝓑 t))

  σ-rec-is-hom : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
               → is-σ-suplat-hom 𝓐 𝓑 (σ-rec 𝓑 t)
  σ-rec-is-hom 𝓑 t = pr₁ (pr₂ (center (𝓐-free 𝓑 t)))

  σ-rec-⊥ : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
          → σ-rec 𝓑 t ⊥ ＝ ⊥⟨ 𝓑 ⟩
  σ-rec-⊥ 𝓑 t = σ-suplat-hom-⊥ 𝓐 𝓑 (σ-rec 𝓑 t) (σ-rec-is-hom 𝓑 t)

  σ-rec-⋁ : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩) (a : ℕ → A)
          → σ-rec 𝓑 t (⋁ a) ＝ ⋁⟨ 𝓑 ⟩ (n ↦ σ-rec 𝓑 t (a n))
  σ-rec-⋁ 𝓑 t = σ-suplat-hom-⋁ 𝓐 𝓑 (σ-rec 𝓑 t) (σ-rec-is-hom 𝓑 t)

  σ-rec-⊤ : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
          → σ-rec 𝓑 t ⊤ ＝ t
  σ-rec-⊤ 𝓑 t = pr₂ (pr₂ (center (𝓐-free 𝓑 t)))

  σ-rec-is-unique : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
                    (f : A → ⟨ 𝓑 ⟩)
                  → is-σ-suplat-hom 𝓐 𝓑 f
                  → f ⊤ ＝ t
                  → σ-rec 𝓑 t ＝ f
  σ-rec-is-unique 𝓑 t f i p = ap pr₁ (centrality (𝓐-free 𝓑 t) (f , i , p))

  at-most-one-hom : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩)
                    (f g : A → ⟨ 𝓑 ⟩)
                  → is-σ-suplat-hom 𝓐 𝓑 f
                  → is-σ-suplat-hom 𝓐 𝓑 g
                  → f ⊤ ＝ t
                  → g ⊤ ＝ t
                  → f ＝ g
  at-most-one-hom 𝓑 t f g i j p q = ap pr₁
                                       (singletons-are-props
                                         (𝓐-free 𝓑 t)
                                         (f , i , p)
                                         (g , j , q))
\end{code}

We now establish the induction principle for the free σ-sup-lattice on
one generator by constructing a σ-sup-lattice from the property we
want to prove.

\begin{code}

  σ-induction : (P : A → 𝓥 ̇ )
              → ((a : A) → is-prop (P a))
              → P ⊤
              → P ⊥
              → ((a : ℕ → A) → ((n : ℕ) → P (a n)) → P (⋁ a))
              → (a : A) → P a
  σ-induction {𝓥} P P-is-prop-valued ⊤-closure ⊥-closure ⋁-closure = γ
   where
    X = Σ a ꞉ A , P a

    ⊤' ⊥' : X
    ⊤' = (⊤ , ⊤-closure)
    ⊥' = (⊥ , ⊥-closure)

    ⋁' : (ℕ → X) → X
    ⋁' x = (⋁ (pr₁ ∘ x) , ⋁-closure (pr₁ ∘ x) (pr₂ ∘ x))

    _≤'_ : X → X → 𝓚 ̇
    (a , _) ≤' (b , _) = a ≤ b

    𝓑 : σ-SupLat (𝓣 ⊔ 𝓥) 𝓚
    𝓑 = X ,
        (⊥' , ⋁') ,
        _≤'_ ,
        (λ (a , _) (b , _) → ⟨ 𝓐 ⟩-order-is-prop-valued a b) ,
        (λ (a , _) → ⟨ 𝓐 ⟩-refl a) ,
        (λ (a , _) (b , _) (c , _) → ⟨ 𝓐 ⟩-trans a b c) ,
        (λ (a , _) (b , _) l m → to-subtype-＝
                                  P-is-prop-valued
                                  (⟨ 𝓐 ⟩-antisym a b l m)) ,
        (λ (a , _) → ⟨ 𝓐 ⟩-⊥-is-minimum a) ,
        (λ x n → ⟨ 𝓐 ⟩-⋁-is-ub (pr₁ ∘ x) n) ,
        (λ x (u , _) φ → ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs (pr₁ ∘ x) u φ)

    g : X → A
    g = pr₁

    g-is-hom : is-σ-suplat-hom 𝓑 𝓐 g
    g-is-hom = refl , (λ 𝕒 → refl)

    h : A → A
    h = g ∘ σ-rec 𝓑 ⊤'

    h⊤ : h ⊤ ＝ ⊤
    h⊤ = ap g (σ-rec-⊤ 𝓑 ⊤')

    h-is-hom : is-σ-suplat-hom 𝓐 𝓐 h
    h-is-hom = ∘-σ-suplat-hom 𝓐 𝓑 𝓐 (σ-rec 𝓑 ⊤') g (σ-rec-is-hom 𝓑 ⊤') g-is-hom

    H : h ＝ id
    H = at-most-one-hom 𝓐 ⊤ h id h-is-hom (id-is-σ-suplat-hom 𝓐) h⊤ refl

    δ : (a : A) → P (h a)
    δ a = pr₂ (σ-rec 𝓑 ⊤' a)

    γ : (a : A) → P a
    γ a = transport P (happly H a) (δ a)

\end{code}

For example, we see that the generator ⊤ is the maximum element by
σ-induction:

\begin{code}

  ⊤-is-maximum : (a : A) → a ≤ ⊤
  ⊤-is-maximum = σ-induction
                  (_≤ ⊤)
                  (λ a → ⟨ 𝓐 ⟩-order-is-prop-valued a ⊤)
                  (⟨ 𝓐 ⟩-refl ⊤)
                  (⟨ 𝓐 ⟩-⊥-is-minimum ⊤)
                  (λ a → ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a ⊤)
\end{code}

We use the following little lemma a couple of times:

\begin{code}

  ⋁-⊤ : (a : ℕ → A) (n : ℕ) → a n ＝ ⊤ → ⋁ a ＝ ⊤
  ⋁-⊤ a n p = ⟨ 𝓐 ⟩-antisym (⋁ a) ⊤
                   (⊤-is-maximum (⋁ a))
                   (⟨ 𝓐 ⟩-trans ⊤ (a n) (⋁ a)
                          (⟨ 𝓐 ⟩-＝-gives-≤ (p ⁻¹))
                          (⟨ 𝓐 ⟩-⋁-is-ub a n))
\end{code}

We now characterize σ-rec as a least upper bound, or join. We first
define joins and their basic properties:

\begin{code}

  join-of : (𝓑 : σ-SupLat 𝓥 𝓦) {I : 𝓦' ̇ } → (I → ⟨ 𝓑 ⟩) → ⟨ 𝓑 ⟩ → 𝓥 ⊔ 𝓦 ⊔ 𝓦' ̇
  join-of 𝓑 f x = (∀ i → f i ≤⟨ 𝓑 ⟩ x)
                × ((u : ⟨ 𝓑 ⟩) → (∀ i → f i ≤⟨ 𝓑 ⟩ u) → x ≤⟨ 𝓑 ⟩ u)

  syntax join-of 𝓑 f x = x is-the-join-of f on 𝓑

  being-join-is-prop : (𝓑 : σ-SupLat 𝓥 𝓦)
                       {I : 𝓦' ̇ }
                       (x : ⟨ 𝓑 ⟩)
                       (f : I → ⟨ 𝓑 ⟩)
                     → is-prop (x is-the-join-of f on 𝓑)
  being-join-is-prop 𝓑 x f = ×-is-prop
                              (Π-is-prop fe
                                (λ i → ⟨ 𝓑 ⟩-order-is-prop-valued (f i) x))
                              (Π₂-is-prop fe
                                (λ u _ → ⟨ 𝓑 ⟩-order-is-prop-valued x u))

  at-most-one-join : (𝓑 : σ-SupLat 𝓥 𝓦)
                     {I : 𝓦' ̇ }
                     (x x' : ⟨ 𝓑 ⟩)
                     (f : I → ⟨ 𝓑 ⟩)
                   → x  is-the-join-of f on 𝓑
                   → x' is-the-join-of f on 𝓑
                   → x ＝ x'
  at-most-one-join 𝓑 x x' f (α , β) (α' , β') =
   ⟨ 𝓑 ⟩-antisym x x' (β x' α') (β' x α)

\end{code}

We have that the following characterization of (σ-rec 𝓑 t a) as the
least upper bound of the weakly constant family λ (_ : a ＝ ⊤) → t:

\begin{code}

  σ-rec-is-join : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩) (a : A)
                → (σ-rec 𝓑 t a) is-the-join-of (λ (_ : a ＝ ⊤) → t) on 𝓑
  σ-rec-is-join 𝓑 t a = α , β
   where
    h : A → ⟨ 𝓑 ⟩
    h = σ-rec 𝓑 t

    α : a ＝ ⊤ → t ≤⟨ 𝓑 ⟩ h a
    α p = ⟨ 𝓑 ⟩-＝-gives-≤ (t    ＝⟨ (σ-rec-⊤ 𝓑 t)⁻¹ ⟩
                            h ⊤ ＝⟨ ap (h) (p ⁻¹) ⟩
                            h a ∎)

    β : (u : ⟨ 𝓑 ⟩) → (a ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → h a ≤⟨ 𝓑 ⟩ u
    β = σ-induction
         (λ a → (u : ⟨ 𝓑 ⟩) → (a ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → h a ≤⟨ 𝓑 ⟩ u)
         (λ a → Π₂-is-prop fe (λ u p → ⟨ 𝓑 ⟩-order-is-prop-valued (h a) u))
         β⊤
         β⊥
         β⋁
         a
     where
      β⊤ : (u : ⟨ 𝓑 ⟩) → (⊤ ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → h ⊤ ≤⟨ 𝓑 ⟩ u
      β⊤ u φ = transport
                (λ - → - ≤⟨ 𝓑 ⟩ u)
                ((σ-rec-⊤ 𝓑 t )⁻¹)
                (φ refl)

      β⊥ : (u : ⟨ 𝓑 ⟩) → (⊥ ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → h ⊥ ≤⟨ 𝓑 ⟩ u
      β⊥ u φ = transport
                (λ - → - ≤⟨ 𝓑 ⟩ u)
                ((σ-rec-⊥ 𝓑 t)⁻¹)
                (⟨ 𝓑 ⟩-⊥-is-minimum u)

      β⋁ : (c : ℕ → A)
         → ((n : ℕ) (u : ⟨ 𝓑 ⟩) → (c n ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → h (c n) ≤⟨ 𝓑 ⟩ u)
         → (u : ⟨ 𝓑 ⟩) → (⋁ c ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → h (⋁ c) ≤⟨ 𝓑 ⟩ u
      β⋁ c ψ u φ = transport (λ - → - ≤⟨ 𝓑 ⟩ u) ((σ-rec-⋁ 𝓑 t c)⁻¹) γ
       where
        γ : ⋁⟨ 𝓑 ⟩ (h ∘ c) ≤⟨ 𝓑 ⟩ u
        γ = ⟨ 𝓑 ⟩-⋁-is-lb-of-ubs
                 (h ∘ c)
                 u
                 (λ n → ψ n u (λ (p : c n ＝ ⊤) → φ (⋁-⊤ c n p)))

  σ-rec-is-ub : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩) (a : A)
              → a ＝ ⊤ → t ≤⟨ 𝓑 ⟩ σ-rec 𝓑 t a
  σ-rec-is-ub 𝓑 t a = pr₁ (σ-rec-is-join 𝓑 t a)

  σ-rec-is-lb-of-ubs : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩) (a : A)
                     → (u : ⟨ 𝓑 ⟩) → (a ＝ ⊤ → t ≤⟨ 𝓑 ⟩ u) → σ-rec 𝓑 t a ≤⟨ 𝓑 ⟩ u
  σ-rec-is-lb-of-ubs 𝓑 t a = pr₂ (σ-rec-is-join 𝓑 t a)

\end{code}

Such joins are absolute, in the sense that they are preserved by all
homomorphisms:

\begin{code}

  σ-suplat-homs-preserve-σ-rec : (𝓑 : σ-SupLat 𝓥 𝓦)
                                 (𝓒 : σ-SupLat 𝓣' 𝓥')
                                 (f : ⟨ 𝓑 ⟩ → ⟨ 𝓒 ⟩)
                               → is-σ-suplat-hom 𝓑 𝓒 f
                               → (t : ⟨ 𝓑 ⟩)
                                 (a : A)
                               → f (σ-rec 𝓑 t a) ＝ σ-rec 𝓒 (f t) a
  σ-suplat-homs-preserve-σ-rec 𝓑 𝓒 f i t = happly γ
   where
    composite-is-hom : is-σ-suplat-hom 𝓐 𝓒 (f ∘ σ-rec 𝓑 t)
    composite-is-hom = ∘-σ-suplat-hom 𝓐 𝓑 𝓒 (σ-rec 𝓑 t) f (σ-rec-is-hom 𝓑 t) i

    γ : f ∘ σ-rec 𝓑 t ＝ σ-rec 𝓒 (f t)
    γ = at-most-one-hom 𝓒 (f t)
         (f ∘ σ-rec 𝓑 t)
         (σ-rec 𝓒 (f t))
         composite-is-hom
         (σ-rec-is-hom 𝓒 (f t))
         (ap f (σ-rec-⊤ 𝓑 t))
         (σ-rec-⊤ 𝓒 (f t))

\end{code}

In particular, σ-rec preserves σ-rec:

\begin{code}

  σ-rec-preserves-σ-rec : (𝓑 : σ-SupLat 𝓥 𝓦) (t : ⟨ 𝓑 ⟩) (a b : A)
                        → σ-rec 𝓑 t (σ-rec 𝓐 a b) ＝ σ-rec 𝓑 (σ-rec 𝓑 t a) b
  σ-rec-preserves-σ-rec 𝓑 t = σ-suplat-homs-preserve-σ-rec 𝓐 𝓑
                               (σ-rec 𝓑 t)
                               (σ-rec-is-hom 𝓑 t)

\end{code}

We now derive the existence of binary meets in σ-sup-lattice 𝓐 on one
generator ⊤ from the above kind of joins.

\begin{code}

  _∧_ : A → A → A
  a ∧ b = σ-rec 𝓐 a b

  meet⊤ : (a : A) → a ∧ ⊤ ＝ a
  meet⊤ = σ-rec-⊤ 𝓐

  meet⊥ : (a : A) → a ∧ ⊥ ＝ ⊥
  meet⊥ = σ-rec-⊥ 𝓐

  meet⋁ : (a : A) (b : ℕ → A) → a ∧ ⋁ b ＝ ⋁ (n ↦ a ∧ b n)
  meet⋁ = σ-rec-⋁ 𝓐

  infix 100 _∧_

  ∧-associative : (a b c : A) → a ∧ (b ∧ c) ＝ (a ∧ b) ∧ c
  ∧-associative = σ-rec-preserves-σ-rec 𝓐

  ∧-is-lb-left : (a b : A) → a ∧ b ≤ a
  ∧-is-lb-left a b = σ-rec-is-lb-of-ubs 𝓐 a b a
                      (λ (_ : b ＝ ⊤) → ⟨ 𝓐 ⟩-refl a)

  ∧-is-lb-right : (a b : A) → a ∧ b ≤ b
  ∧-is-lb-right a b = σ-rec-is-lb-of-ubs 𝓐 a b b
                       (λ (r : b ＝ ⊤) → transport (a ≤_) (r ⁻¹) (⊤-is-maximum a))

\end{code}

Using this, we show that a ∧ b is the greatest lower bound of a and b.
One step needs σ-induction:

\begin{code}

  ∧-is-ub-of-lbs : (a b c : A) → c ≤ a → c ≤ b → c ≤ a ∧ b
  ∧-is-ub-of-lbs a b = σ-induction
                        (λ c → c ≤ a → c ≤ b → c ≤ a ∧ b)
                        (λ c → Π₂-is-prop fe
                                (λ _ _ → ⟨ 𝓐 ⟩-order-is-prop-valued c (a ∧ b)))
                        p⊤
                        p⊥
                        p⋁
   where
    p⊤ : ⊤ ≤ a → ⊤ ≤ b → ⊤ ≤ a ∧ b
    p⊤ l m = ⟨ 𝓐 ⟩-trans _ _ _ l ii
     where
      i : b ＝ ⊤
      i = ⟨ 𝓐 ⟩-antisym _ _ (⊤-is-maximum b) m

      ii : a ≤ a ∧ b
      ii = σ-rec-is-ub 𝓐 a b i

    p⊥ : ⊥ ≤ a → ⊥ ≤ b → ⊥ ≤ a ∧ b
    p⊥ _ _ = ⟨ 𝓐 ⟩-⊥-is-minimum (a ∧ b)

    p⋁ : (d : ℕ → A)
       → ((n : ℕ) → d n ≤ a → d n ≤ b → d n ≤ a ∧ b)
       → ⋁ d ≤ a
       → ⋁ d ≤ b
       → ⋁ d ≤ (a ∧ b)
    p⋁ d φ l m = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs d (a ∧ b)
                      (λ n → φ n (⟨ 𝓐 ⟩-trans (d n) _ a (⟨ 𝓐 ⟩-⋁-is-ub d n) l)
                                 (⟨ 𝓐 ⟩-trans (d n) _ b (⟨ 𝓐 ⟩-⋁-is-ub d n) m))

  ∧-idempotent : (a : A) → a ∧ a ＝ a
  ∧-idempotent a = ⟨ 𝓐 ⟩-antisym _ _ l m
   where
    l : a ∧ a ≤ a
    l = ∧-is-lb-left a a

    m : a ≤ a ∧ a
    m = ∧-is-ub-of-lbs a a a (⟨ 𝓐 ⟩-refl a) (⟨ 𝓐 ⟩-refl a)

  ∧-commutative : (a b : A) → a ∧ b ＝ b ∧ a
  ∧-commutative a b = ⟨ 𝓐 ⟩-antisym _ _ (l a b) (l b a)
   where
    l : (a b : A) → a ∧ b ≤ b ∧ a
    l a b = ∧-is-ub-of-lbs b a (a ∧ b) (∧-is-lb-right a b) (∧-is-lb-left a b)

\end{code}

The intrinsic order coincides with the ∧-semilattice order:

\begin{code}

  from-≤ : (a b : A) → a ≤ b → a ∧ b ＝ a
  from-≤ a b l = ⟨ 𝓐 ⟩-antisym _ _ (∧-is-lb-left a b) m
   where
    m : a ≤ a ∧ b
    m = ∧-is-ub-of-lbs _ _ _ (⟨ 𝓐 ⟩-refl a) l

  to-≤ : (a b : A) → a ∧ b ＝ a → a ≤ b
  to-≤ a b p = ⟨ 𝓐 ⟩-trans _ _ _ l (∧-is-lb-right a b)
   where
    l : a ≤ a ∧ b
    l = ⟨ 𝓐 ⟩-＝-gives-≤ (p ⁻¹)

\end{code}

We now show that the the σ-suplat on one generator is also the initial
σ-frame. The following renaming is annoying.

\begin{code}
  open OrderedTypes.sigma-frame fe
        hiding (order)
        renaming
         (⟨_⟩ to ⟨_⟩' ;
          ⊥⟨_⟩ to ⊥⟨_⟩' ;
          ⊤⟨_⟩ to ⊤⟨_⟩' ;
          meet to meet' ;
          ⋁⟨_⟩ to ⋁⟨_⟩' ;
          ⟨_⟩-is-set to ⟨_⟩'-is-set ;
          ⟨_⟩-refl to ⟨_⟩'-refl ;
          ⟨_⟩-trans to ⟨_⟩'-trans ;
          ⟨_⟩-antisym to ⟨_⟩'-antisym ;
          ⟨_⟩-⊤-maximum to ⟨_⟩'-⊤-maximum ;
          ⟨_⟩-⊥-minimum to ⟨_⟩'-⊥-minimum ;
          ⟨_⟩-⋁-is-ub to ⟨_⟩'-⋁-is-ub ;
          ⟨_⟩-⋁-is-lb-of-ubs to ⟨_⟩'-⋁-is-lb-of-ubs)

  A-qua-σ-frame : σ-Frame 𝓣
  A-qua-σ-frame = A ,
                  (⊤ , _∧_ , ⊥ , ⋁) ,
                  ⟨ 𝓐 ⟩-is-set ,
                  ∧-idempotent ,
                  ∧-commutative ,
                  ∧-associative ,
                  (λ a → ∧-commutative ⊥ a ∙ meet⊥ a) ,
                  meet⊤ ,
                  meet⋁ ,
                  (λ a n → from-≤ (a n) (⋁ a)
                            (⟨ 𝓐 ⟩-⋁-is-ub a n)) ,
                  (λ a u φ → from-≤ (⋁ a) u
                              (⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a u
                                    (λ n → to-≤ (a n) u (φ n))))

  A-qua-σ-frame-is-initial : (𝓑 : σ-Frame 𝓥)
                           → ∃! f ꞉ (A → ⟨ 𝓑 ⟩), is-σ-frame-hom A-qua-σ-frame 𝓑 f
  A-qua-σ-frame-is-initial {𝓥} 𝓑 = γ
   where
    B = ⟨ 𝓑 ⟩

    _∧'_ : B → B → B
    _∧'_ = meet' 𝓑

    𝓑-qua-σ-suplat : σ-SupLat 𝓥 𝓥
    𝓑-qua-σ-suplat = σ-frames-are-σ-suplats 𝓑

    ⊤' : B
    ⊤' = ⊤⟨ 𝓑 ⟩'

    f : A → B
    f = σ-rec 𝓑-qua-σ-suplat ⊤'

    f-is-hom : is-σ-suplat-hom 𝓐 𝓑-qua-σ-suplat f
    f-is-hom = σ-rec-is-hom 𝓑-qua-σ-suplat ⊤'

    f-preserves-∧ : (a b : A) → f (a ∧ b) ＝ f a ∧' f b
    f-preserves-∧ a = σ-induction
                       (λ b → f (a ∧ b) ＝ f a ∧' f b)
                       (λ b → ⟨ 𝓑 ⟩'-is-set)
                       f⊤
                       f⊥
                       f⋁
     where
      f⊤ = f (a ∧ ⊤)  ＝⟨ I ⟩
           f a        ＝⟨ II ⟩
           f a ∧' ⊤'  ＝⟨ III ⟩
           f a ∧' f ⊤ ∎
            where
             I   = ap f (meet⊤ a)
             II  = (⟨ 𝓑 ⟩'-⊤-maximum (f a))⁻¹
             III = ap (f a ∧'_) ((σ-rec-⊤ 𝓑-qua-σ-suplat ⊤')⁻¹)

      f⊥ = f (a ∧ ⊥)      ＝⟨ I ⟩
           f ⊥            ＝⟨ II ⟩
           ⊥⟨ 𝓑 ⟩'        ＝⟨ III ⟩
           ⊥⟨ 𝓑 ⟩' ∧' f a ＝⟨ IV ⟩
           f ⊥ ∧' f a     ＝⟨ V ⟩
           f a ∧' f ⊥     ∎
            where
             I   = ap f (meet⊥ a)
             II  = σ-suplat-hom-⊥ 𝓐 𝓑-qua-σ-suplat f f-is-hom
             III = (⟨ 𝓑 ⟩'-⊥-minimum (f a))⁻¹
             IV  = ap (λ - → - ∧' f a)
                      ((σ-suplat-hom-⊥ 𝓐 𝓑-qua-σ-suplat f f-is-hom)⁻¹)
             V   = ⟨ 𝓑 ⟩-commutativity (f ⊥) (f a)

      f⋁ = λ c p →
           f (a ∧ ⋁ c)                    ＝⟨ I c ⟩
           f (⋁ (n ↦ a ∧ c n))            ＝⟨ II c ⟩
           ⋁⟨ 𝓑 ⟩' (n ↦ f (a ∧ c n))      ＝⟨ III c p ⟩
           ⋁⟨ 𝓑 ⟩' (n ↦ f a ∧' f (c n))   ＝⟨ IV c ⟩
           f a ∧' ⋁⟨ 𝓑 ⟩' (λ n → f (c n)) ＝⟨ V c ⟩
           f a ∧' f (⋁ c)                 ∎
            where
             I   = λ (c : ℕ → ⟨ 𝓐 ⟩) → ap f (meet⋁ a c)
             II  = λ (c : ℕ → ⟨ 𝓐 ⟩) → σ-suplat-hom-⋁
                                        𝓐
                                        𝓑-qua-σ-suplat
                                        f
                                        f-is-hom
                                        (λ n → a ∧ c n)
             III = λ (c : ℕ → ⟨ 𝓐 ⟩)
                     (p : (n : ℕ) → _ ＝ meet' 𝓑 (f a) (f (c n)))
                        → ap ⋁⟨ 𝓑 ⟩' (dfunext fe p)
             IV  = λ (c : ℕ → ⟨ 𝓐 ⟩) → (⟨ 𝓑 ⟩-distributivity (f a) (λ n → f (c n)))⁻¹
             V   = λ (c : ℕ → ⟨ 𝓐 ⟩) → ap (f a ∧'_)
                                         ((σ-suplat-hom-⋁ 𝓐 𝓑-qua-σ-suplat f f-is-hom c)⁻¹)

    f-is-hom' : is-σ-frame-hom A-qua-σ-frame 𝓑 f
    f-is-hom' = σ-rec-⊤ 𝓑-qua-σ-suplat ⊤' ,
                f-preserves-∧ ,
                σ-suplat-hom-⊥ 𝓐 𝓑-qua-σ-suplat f f-is-hom ,
                σ-suplat-hom-⋁ 𝓐 𝓑-qua-σ-suplat f f-is-hom

    forget : (g : A → B)
           → is-σ-frame-hom  A-qua-σ-frame 𝓑              g
           → is-σ-suplat-hom 𝓐             𝓑-qua-σ-suplat g
    forget g (i , ii , iii , iv) = (iii , iv)

    f-uniqueness : (g : A → B) → is-σ-frame-hom A-qua-σ-frame 𝓑 g → f ＝ g
    f-uniqueness g g-is-hom' = at-most-one-hom 𝓑-qua-σ-suplat ⊤' f g
                                f-is-hom
                                (forget g g-is-hom')
                                (σ-rec-⊤ 𝓑-qua-σ-suplat ⊤')
                                (σ-frame-hom-⊤ A-qua-σ-frame 𝓑 g g-is-hom')

    γ : ∃! f ꞉ (A → B), is-σ-frame-hom A-qua-σ-frame 𝓑 f
    γ = (f , f-is-hom') ,
        (λ (g , g-is-hom') → to-subtype-＝
                              (being-σ-frame-hom-is-prop A-qua-σ-frame 𝓑)
                              (f-uniqueness g g-is-hom'))
\end{code}

We now regard the type of propositions as a σ-sup-lattice:

\begin{code}

  Ω-qua-σ-Frame : σ-Frame (𝓣 ⁺)
  Ω-qua-σ-Frame = OrderedTypes.sigma-frame.Ω-qua-σ-frame fe pe pt

  Ω-qua-σ-SupLat : σ-SupLat (𝓣 ⁺) (𝓣 ⁺)
  Ω-qua-σ-SupLat = OrderedTypes.sigma-frame.Ω-qua-σ-suplat fe pe pt

  private
   ⊥'   = ⊥⟨ Ω-qua-σ-SupLat ⟩
   ⊤'   = ⊤⟨ Ω-qua-σ-Frame ⟩'
   ⋁'  = ⋁⟨ Ω-qua-σ-SupLat ⟩
   _≤'_ : Ω 𝓣 → Ω 𝓣 → 𝓣 ⁺ ̇
   x ≤' y = x ≤⟨ Ω-qua-σ-SupLat ⟩ y

   ＝-gives-≤' : (p q : Ω 𝓣) → p ＝ q → p ≤' q
   ＝-gives-≤' p q r = ⟨ Ω-qua-σ-SupLat ⟩-＝-gives-≤ r

\end{code}

In a frame the bottom element is not taken explicitly as part of the
structure and is defined to be the join of the family indexed by the
empty set. In the particular case of the frame of propositions, this
is equal to the empty type 𝟘, but not definitionally:

\begin{code}

  ⊥-holds-is-𝟘 : ⊥' holds ＝ 𝟘
  ⊥-holds-is-𝟘 = p
   where
    p : (∃ x ꞉ 𝟘 , unique-from-𝟘 x holds) ＝ 𝟘
    p = pe ∃-is-prop
           𝟘-is-prop
           (∥∥-rec 𝟘-is-prop (unique-from-𝟘 ∘ pr₁))
           unique-from-𝟘

  Ω-non-trivial : ⊥' ≠ ⊤'
  Ω-non-trivial q = 𝟘-is-not-𝟙 r
   where
    r : 𝟘 ＝ 𝟙
    r = (⊥-holds-is-𝟘)⁻¹ ∙ ap _holds q

\end{code}

The following map τ will play an important role:

\begin{code}

  τ : A → Ω 𝓣
  τ = σ-rec Ω-qua-σ-SupLat ⊤'

  τ-is-hom : is-σ-suplat-hom 𝓐 Ω-qua-σ-SupLat τ
  τ-is-hom = σ-rec-is-hom Ω-qua-σ-SupLat ⊤'

\end{code}

Using τ we derive the non-triviality of 𝓐 from that of Ω:

\begin{code}

  𝓐-non-trivial : ⊥ ≠ ⊤
  𝓐-non-trivial p = Ω-non-trivial q
   where
    q = ⊥'  ＝⟨ (σ-suplat-hom-⊥ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom)⁻¹ ⟩
        τ ⊥ ＝⟨ ap τ p ⟩
        τ ⊤ ＝⟨ σ-rec-⊤ Ω-qua-σ-SupLat ⊤' ⟩
        ⊤'  ∎

\end{code}

A crucial property of the map τ is that it reflects top elements (in
point-free topological terms, this says that τ is dense):

\begin{code}

  τ-reflects-⊤ : (a : A) → τ a ＝ ⊤' → a ＝ ⊤
  τ-reflects-⊤ = σ-induction
                  (λ a → τ a ＝ ⊤' → a ＝ ⊤)
                  (λ a → Π-is-prop fe (λ _ → ⟨ 𝓐 ⟩-is-set))
                  i⊤
                  i⊥
                  i⋁
   where
    i⊤ : τ ⊤ ＝ ⊤' → ⊤ ＝ ⊤
    i⊤ _ = refl

    i⊥ : τ ⊥ ＝ ⊤' → ⊥ ＝ ⊤
    i⊥ p = 𝟘-elim (Ω-non-trivial q)
     where
      q : ⊥' ＝ ⊤'
      q = (σ-suplat-hom-⊥ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom)⁻¹ ∙ p

    i⋁ : (a : ℕ → A)
       → ((n : ℕ) → τ (a n) ＝ ⊤' → a n ＝ ⊤)
       → τ (⋁ a) ＝ ⊤'
       → ⋁ a ＝ ⊤
    i⋁ a φ p = ∥∥-rec ⟨ 𝓐 ⟩-is-set iii ii
     where
      i : ⋁' (τ ∘ a) ＝ ⊤'
      i = (σ-suplat-hom-⋁ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom a)⁻¹ ∙ p

      ii : ∃ n ꞉ ℕ , τ (a n) holds
      ii = equal-⊤-gives-holds (⋁' (τ ∘ a)) i

      iii : (Σ n ꞉ ℕ , τ (a n) holds) → ⋁ a ＝ ⊤
      iii (n , h) = vi
       where
        iv : τ (a n) ＝ ⊤'
        iv = holds-gives-equal-⊤ pe fe (τ (a n)) h

        v : a n ＝ ⊤
        v = φ n iv

        vi : ⋁ a ＝ ⊤
        vi = ⋁-⊤ a n v

\end{code}

A frame is called compact if every cover of its top element has a
finite subcover. It is supercompact (I think the terminology is due to
John Isbell) if every cover of the top element has a singleton
subcover. This motivates the name of the following theorem, whose
crucial ingredient is the homomorphism τ and the fact that it reflects
top elements.

\begin{code}

  𝓐-is-σ-supercompact : (a : ℕ → A) → ⋁ a ＝ ⊤ → ∃ n ꞉ ℕ , a n ＝ ⊤
  𝓐-is-σ-supercompact a p = vi
   where
    i = ⋁' (τ ∘ a) ＝⟨ (σ-suplat-hom-⋁ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom a)⁻¹ ⟩
        τ (⋁ a)    ＝⟨ ap τ p ⟩
        τ ⊤        ＝⟨ σ-rec-⊤ Ω-qua-σ-SupLat ⊤' ⟩
        ⊤'         ∎

    ii : (∃ n ꞉ ℕ , τ (a n) holds) ＝ 𝟙
    ii = ap _holds i

    iii : (Σ n ꞉ ℕ , τ (a n) holds) → (Σ n ꞉ ℕ , a n ＝ ⊤)
    iii (n , h) = n , v
     where
      iv : τ (a n) ＝ ⊤'
      iv = holds-gives-equal-⊤ pe fe (τ (a n)) h

      v : a n ＝ ⊤
      v = τ-reflects-⊤ (a n) iv

    vi : ∃ n ꞉ ℕ , a n ＝ ⊤
    vi = ∥∥-functor iii (equal-𝟙-gives-holds (∃ n ꞉ ℕ , τ (a n) holds) ii)

\end{code}

We have that τ a holds precisely when a ＝ ⊤ (hence the name τ for the
function):

\begin{code}

  τ-charac→ : (a : A) → τ a holds → a ＝ ⊤
  τ-charac→ a h = τ-reflects-⊤ a (holds-gives-equal-⊤ pe fe (τ a) h)

  τ-charac← : (a : A) → a ＝ ⊤ → τ a holds
  τ-charac← a p = equal-⊤-gives-holds (τ a)
                   (τ a ＝⟨ ap τ p ⟩
                    τ ⊤ ＝⟨ σ-rec-⊤ Ω-qua-σ-SupLat ⊤' ⟩
                    ⊤'  ∎)

  τ-charac' : (a : A) → τ a holds ＝ (a ＝ ⊤)
  τ-charac' a = pe (holds-is-prop (τ a)) ⟨ 𝓐 ⟩-is-set (τ-charac→ a) (τ-charac← a)

  τ-charac : (a : A) → τ a ＝ ((a ＝ ⊤) , ⟨ 𝓐 ⟩-is-set)
  τ-charac a = to-subtype-＝ (λ a → being-prop-is-prop fe) (τ-charac' a)

\end{code}

The following criterion for a ≤ b will be useful:

\begin{code}

  ≤-criterion : (a b : A) → (a ＝ ⊤ → b ＝ ⊤) → a ≤ b
  ≤-criterion = σ-induction
                  (λ a → (b : A) → (a ＝ ⊤ → b ＝ ⊤) → a ≤ b)
                  (λ a → Π₂-is-prop fe (λ b _ → ⟨ 𝓐 ⟩-order-is-prop-valued a b))
                  i⊤
                  i⊥
                  i⋁
   where
    i⊤ : (b : A) → (⊤ ＝ ⊤ → b ＝ ⊤) → ⊤ ≤ b
    i⊤ b f = ⟨ 𝓐 ⟩-＝-gives-≤ ((f refl)⁻¹)

    i⊥ : (b : A) → (⊥ ＝ ⊤ → b ＝ ⊤) → ⊥ ≤ b
    i⊥ b _ = ⟨ 𝓐 ⟩-⊥-is-minimum b

    i⋁ : (a : ℕ → A)
       → ((n : ℕ) (b : A) → (a n ＝ ⊤ → b ＝ ⊤) → a n ≤ b)
       → (b : A)
       → (⋁ a ＝ ⊤ → b ＝ ⊤)
       → ⋁ a ≤ b
    i⋁ a φ b ψ = ⟨ 𝓐 ⟩-⋁-is-lb-of-ubs a b
                      (λ n → φ n b (λ (p : a n ＝ ⊤) → ψ (⋁-⊤ a n p)))

  ≤-criterion-converse : (a b : A) → a ≤ b → (a ＝ ⊤ → b ＝ ⊤)
  ≤-criterion-converse a b l p =
   ⟨ 𝓐 ⟩-antisym _ _
        (⊤-is-maximum b)
        (⟨ 𝓐 ⟩-trans _ _ _ (⟨ 𝓐 ⟩-＝-gives-≤ (p ⁻¹)) l)

\end{code}

The map τ reflects order and hence is left-cancellable, and therefore
is an embedding (its fibers are propositions) because it is a map into
a set:

\begin{code}

  τ-order-lc : (a b : A) → τ a ≤' τ b → a ≤ b
  τ-order-lc a b l = iv
   where
    i : τ a holds → τ b holds
    i = OrderedTypes.Frame.from-≤Ω fe pe pt {𝓣} {τ a} {τ b} l

    ii : τ a ＝ ⊤' → τ b ＝ ⊤'
    ii p = holds-gives-equal-⊤ pe fe (τ b) (i (equal-⊤-gives-holds (τ a) p))

    iii : a ＝ ⊤ → b ＝ ⊤
    iii q = τ-reflects-⊤ b (ii r)
     where
      r = τ a ＝⟨ ap τ q ⟩
          τ ⊤ ＝⟨ σ-rec-⊤ Ω-qua-σ-SupLat ⊤' ⟩
          ⊤'  ∎

    iv : a ≤ b
    iv = ≤-criterion a b iii

  τ-lc : left-cancellable τ
  τ-lc {a} {b} p = ⟨ 𝓐 ⟩-antisym a b l r
   where
    l : a ≤ b
    l = τ-order-lc a b (＝-gives-≤' (τ a) (τ b) p)

    r : b ≤ a
    r = τ-order-lc b a (＝-gives-≤' (τ b) (τ a) (p ⁻¹))

  τ-is-embedding : is-embedding τ
  τ-is-embedding = lc-maps-into-sets-are-embeddings τ τ-lc (Ω-is-set fe pe)

  holds-is-embedding : is-embedding (_holds {𝓣})
  holds-is-embedding = pr₁-is-embedding (λ _ → being-prop-is-prop fe)

\end{code}

Hence the composite τ-holds is an embedding of A into the universe 𝓣:

\begin{code}

  τ-holds : A → 𝓣 ̇
  τ-holds a = τ a holds

  τ-holds-is-embedding : is-embedding τ-holds
  τ-holds-is-embedding = ∘-is-embedding τ-is-embedding holds-is-embedding

\end{code}

Using this we define the notion of quasidecidability and its required
properties. We define the quasidecidability of the type P to be the
type

  fiber τ-holds P,

which amounts to the type

  Σ a ꞉ A , (τ a holds ＝ P)

by construction:

\begin{code}

  is-quasidecidable : 𝓣 ̇ → 𝓣 ⁺ ̇
  is-quasidecidable P = Σ a ꞉ A , (τ a holds ＝ P)

  being-quasidecidable-is-prop : ∀ P → is-prop (is-quasidecidable P)
  being-quasidecidable-is-prop = τ-holds-is-embedding

  quasidecidable-types-are-props : ∀ P → is-quasidecidable P → is-prop P
  quasidecidable-types-are-props P (a , p) =
   transport is-prop p (holds-is-prop (τ a))

  𝟘-is-quasidecidable : is-quasidecidable 𝟘
  𝟘-is-quasidecidable = ⊥ ,
                        (τ ⊥ holds ＝⟨ I ⟩
                         ⊥' holds  ＝⟨ II ⟩
                         𝟘         ∎)
                          where
                           I  = ap _holds
                                   (σ-suplat-hom-⊥ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom)
                           II = ⊥-holds-is-𝟘

  𝟙-is-quasidecidable : is-quasidecidable 𝟙
  𝟙-is-quasidecidable = ⊤ , ap _holds (σ-rec-⊤ Ω-qua-σ-SupLat ⊤')

  quasidecidable-closed-under-ω-joins
   : (P : ℕ → 𝓣 ̇ )
   → ((n : ℕ) → is-quasidecidable (P n))
   → is-quasidecidable (∃ n ꞉ ℕ , P n)
  quasidecidable-closed-under-ω-joins P φ = vii
   where
    i : (n : ℕ) → τ-holds (fiber-point (φ n)) ＝ P n
    i n = fiber-identification (φ n)

    ii : (n : ℕ)
       → τ (fiber-point (φ n))
       ＝ (P n , quasidecidable-types-are-props (P n) (φ n))
    ii n = to-subtype-＝ (λ _ → being-prop-is-prop fe) (i n)

    iii : τ (⋁ (n ↦ fiber-point (φ n)))
        ＝ ⋁' (λ n → P n , quasidecidable-types-are-props (P n) (φ n))
    iii = τ (⋁ (n ↦ fiber-point (φ n)))                               ＝⟨ iv ⟩
          ⋁' (n ↦ τ (fiber-point (φ n)))                              ＝⟨ v ⟩
          ⋁' (n ↦ (P n , quasidecidable-types-are-props (P n) (φ n))) ∎
     where
      iv = σ-suplat-hom-⋁ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom (λ n → fiber-point (φ n))
      v  = ap ⋁' (dfunext fe ii)

    vi : τ-holds (⋁ (n ↦ fiber-point (φ n))) ＝ (∃ n ꞉ ℕ , P n)
    vi = ap _holds iii

    vii : is-quasidecidable (∃ n ꞉ ℕ , P n)
    vii = ⋁ (n ↦ fiber-point (φ n)) , vi

\end{code}

Then we get quasidecidable induction by σ-induction:

\begin{code}

  quasidecidable-induction :
     (F : 𝓣 ̇ → 𝓥 ̇ )
   → ((P : 𝓣 ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓣 ̇ ) → is-quasidecidable P → F P
  quasidecidable-induction {𝓥} F i F₀ F₁ Fω P (a , r) = γ a P r
   where
    γ⊤ : (P : 𝓣 ̇ ) → τ ⊤ holds ＝ P → F P
    γ⊤ P s = transport F (t ⁻¹ ∙ s) F₁
     where
      t : τ ⊤ holds ＝ 𝟙
      t = ap _holds (σ-rec-⊤ Ω-qua-σ-SupLat ⊤')

    γ⊥ : (P : 𝓣 ̇ ) → τ ⊥ holds ＝ P → F P
    γ⊥ P s = transport F (t ⁻¹ ∙ s) F₀
     where
      t : τ ⊥ holds ＝ 𝟘
      t = ap _holds (σ-suplat-hom-⊥ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom) ∙ ⊥-holds-is-𝟘

    γ⋁ : (a : ℕ → A)
       → ((n : ℕ) (P : 𝓣 ̇ ) → (τ (a n) holds) ＝ P → F P)
       → (P : 𝓣 ̇ ) → (τ (⋁ a) holds) ＝ P → F P
    γ⋁ a φ P s = transport F (t ⁻¹ ∙ s) (Fω (λ n → τ (a n) holds) ψ)
     where
      t : τ (⋁ a) holds ＝ (∃ n ꞉ ℕ , τ (a n) holds)
      t = ap _holds (σ-suplat-hom-⋁ 𝓐 Ω-qua-σ-SupLat τ τ-is-hom a)
      ψ : (n : ℕ) → F (τ (a n) holds)
      ψ n = φ n (τ (a n) holds) refl

    γ : (a : A) (P : 𝓣 ̇ ) → τ a holds ＝ P → F P
    γ = σ-induction
         (λ a → (P : 𝓣 ̇ ) → τ a holds ＝ P → F P)
         (λ a → Π₂-is-prop fe (λ P _ → i P))
         γ⊤
         γ⊥
         γ⋁

\end{code}

We then get the dominance axiom for quasidecidable propositions by an
application of the submodule hypothetical-quasidecidability.

\begin{code}

  quasidecidable-closed-under-Σ
   : (P : 𝓣 ̇ )
   → (Q : P → 𝓣 ̇ )
   → is-quasidecidable P
   → ((p : P) → is-quasidecidable (Q p))
   → is-quasidecidable (Σ Q)
  quasidecidable-closed-under-Σ
   = hypothetical-quasidecidability.quasidecidable-closed-under-Σ
      (quasidecidable-propositions
         is-quasidecidable
         being-quasidecidable-is-prop
         𝟘-is-quasidecidable
         𝟙-is-quasidecidable
         quasidecidable-closed-under-ω-joins
         quasidecidable-induction)

\end{code}

Here are some consequences for the sake of illustration of the meaning
of this.

\begin{code}

  dependent-binary-meet
   : (a : A) (b : τ a holds → A)
   → Σ c ꞉ A , (τ c holds ＝ (Σ h ꞉ τ a holds , τ (b h) holds))
  dependent-binary-meet a b = quasidecidable-closed-under-Σ
                               (τ a holds)
                               (λ h → τ (b h) holds)
                               (a , refl)
                               (λ h → b h , refl)
\end{code}

The following just applies back-and-forth the characterization of
τ a holds as a ＝ ⊤.

\begin{code}

  dependent-binary-meet' : (a : A) (b : a ＝ ⊤ → A)
                         → Σ c ꞉ A , (c ＝ ⊤ ↔ (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤))
  dependent-binary-meet' a b = f σ
   where
    b' : τ a holds → A
    b' h = b (τ-charac→ a h)

    σ : Σ c ꞉ A , (τ c holds) ＝ (Σ h ꞉ τ a holds , τ (b' h) holds)
    σ = dependent-binary-meet a b'

    f : (Σ c ꞉ A , (τ c holds) ＝ (Σ h ꞉ τ a holds , τ (b' h) holds))
      → Σ c ꞉ A , ((c ＝ ⊤) ↔ (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤))
    f ( c , q) = c , g , h
     where
      g : c ＝ ⊤ → Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤
      g r = τ-charac→ a (pr₁ (Idtofun q (τ-charac← c r))) ,
            transport (λ - → b - ＝ ⊤)
              (⟨ 𝓐 ⟩-is-set _ _)
              (τ-charac→ (b _) (pr₂ (Idtofun q (τ-charac← c r))))

      h : (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤) → c ＝ ⊤
      h (p , s) = τ-charac→ c
                   (Idtofun
                     (q ⁻¹)
                     (τ-charac← a p , τ-charac← (b' (τ-charac← a p))
                     (transport (λ - → b - ＝ ⊤) (⟨ 𝓐 ⟩-is-set _ _) s)))
\end{code}

We can replace the bi-implication by an equality:

\begin{code}

  dependent-binary-meet'' : (a : A) (b : a ＝ ⊤ → A)
                          → Σ c ꞉ A , ((c ＝ ⊤) ＝ (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤))
  dependent-binary-meet'' a b = f (dependent-binary-meet' a b)
   where
    f : (Σ c ꞉ A , (c ＝ ⊤ ↔ (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤)))
      → Σ c ꞉ A , ((c ＝ ⊤) ＝ (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤))
    f (c , g , h) = c , ⌜ prop-univalent-≃ pe fe (c ＝ ⊤) (Σ p ꞉ a ＝ ⊤ , b p ＝ ⊤)
                           (Σ-is-prop ⟨ 𝓐 ⟩-is-set (λ p → ⟨ 𝓐 ⟩-is-set)) ⌝⁻¹
                          (logically-equivalent-props-are-equivalent
                             ⟨ 𝓐 ⟩-is-set
                             (Σ-is-prop
                               ⟨ 𝓐 ⟩-is-set
                               (λ p → ⟨ 𝓐 ⟩-is-set)) g h)
\end{code}

The non-dependent special case:

\begin{code}

  binary-meet : (a b : A) → Σ c ꞉ A , (c ＝ ⊤ ↔ ((a ＝ ⊤) × (b ＝ ⊤)))
  binary-meet a b = dependent-binary-meet' a (λ _ → b)

\end{code}

Using the criterion for ≤ we get that this does indeed give binary
meets:

\begin{code}

  binary-meet'-is-∧ : (a b c : A)
                    → (c ＝ ⊤ ↔ ((a ＝ ⊤) × (b ＝ ⊤)))
                    → c ＝ a ∧ b
  binary-meet'-is-∧ a b c (f , g) = viii
   where
    i : c ≤ a
    i = ≤-criterion c a (λ (p : c ＝ ⊤) → pr₁ (f p))

    ii : c ≤ b
    ii = ≤-criterion c b (λ (p : c ＝ ⊤) → pr₂ (f p))

    iii : c ≤ a ∧ b
    iii = ∧-is-ub-of-lbs a b c i ii

    iv : a ∧ b ＝ ⊤ → a ＝ ⊤
    iv p = ⟨ 𝓐 ⟩-antisym a ⊤
                (⊤-is-maximum a)
                (⟨ 𝓐 ⟩-trans ⊤ (a ∧ b) a
                      (⟨ 𝓐 ⟩-＝-gives-≤ (p ⁻¹))
                      (∧-is-lb-left a b))

    v : a ∧ b ＝ ⊤ → b ＝ ⊤
    v p = ⟨ 𝓐 ⟩-antisym b ⊤
               (⊤-is-maximum b)
               (⟨ 𝓐 ⟩-trans ⊤ (a ∧ b) b
                     (⟨ 𝓐 ⟩-＝-gives-≤ (p ⁻¹))
                     (∧-is-lb-right a b))

    vi : a ∧ b ＝ ⊤ → c ＝ ⊤
    vi p = g (iv p , v p)

    vii : a ∧ b ≤ c
    vii = ≤-criterion (a ∧ b) c vi

    viii : c ＝ a ∧ b
    viii = ⟨ 𝓐 ⟩-antisym c (a ∧ b) iii vii

\end{code}

σ-sup-lattices have joins of quasidecidable-indexed families:

\begin{code}

  σ-suplats-have-quasidecidable-joins : (𝓑 : σ-SupLat 𝓥 𝓦) (P : 𝓣 ̇ )
                                      → is-quasidecidable P
                                      → (f : P → ⟨ 𝓑 ⟩)
                                      → Σ b ꞉ ⟨ 𝓑 ⟩ , (b is-the-join-of f on 𝓑)
  σ-suplats-have-quasidecidable-joins {𝓥} {𝓦} 𝓑 =
    quasidecidable-induction F F-is-prop-valued F₀ F₁ Fω
   where
    F : 𝓣 ̇ → 𝓣 ⊔ 𝓥 ⊔ 𝓦 ̇
    F P = (f : P → ⟨ 𝓑 ⟩) → Σ b ꞉ ⟨ 𝓑 ⟩ , (b is-the-join-of f on 𝓑)

    F-is-prop-valued : ∀ P → is-prop (F P)
    F-is-prop-valued P = Π-is-prop fe
                          (λ f (b , i) (b' , i')
                             → to-subtype-＝
                                (λ b → being-join-is-prop 𝓑 b f)
                                (at-most-one-join 𝓑 b b' f i i'))

    F₀ : F 𝟘
    F₀ f = ⊥⟨ 𝓑 ⟩ , (λ (i : 𝟘) → 𝟘-elim i) , λ u ψ → ⟨ 𝓑 ⟩-⊥-is-minimum u

    F₁ : F 𝟙
    F₁ f = f ⋆ , (λ ⋆ → ⟨ 𝓑 ⟩-refl (f ⋆)) , λ u ψ → ψ ⋆

    Fω : ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
    Fω P φ f = b∞ , α∞ , β∞
     where
      g : (n : ℕ) → P n → ⟨ 𝓑 ⟩
      g n p = f ∣ n , p ∣

      h : (n : ℕ) → Σ b ꞉ ⟨ 𝓑 ⟩ , (b is-the-join-of g n on 𝓑)
      h n = φ n (g n)

      b : ℕ → ⟨ 𝓑 ⟩
      b n = pr₁ (h n)

      α : (n : ℕ) (p : P n) → g n p ≤⟨ 𝓑 ⟩ b n
      α n = pr₁ (pr₂ (h n))

      β : (n : ℕ) (u : ⟨ 𝓑 ⟩) → ((p : P n) → (g n p) ≤⟨ 𝓑 ⟩ u) → b n ≤⟨ 𝓑 ⟩ u
      β n = pr₂ (pr₂ (h n))

      b∞ : ⟨ 𝓑 ⟩
      b∞ = ⋁⟨ 𝓑 ⟩ b

      α∞ : (q : ∃ n ꞉ ℕ , P n) → f q ≤⟨ 𝓑 ⟩ b∞
      α∞ = ∥∥-induction (λ s → ⟨ 𝓑 ⟩-order-is-prop-valued (f s) b∞) α∞'
       where
        α∞' : (σ : Σ n ꞉ ℕ , P n) → f ∣ σ ∣ ≤⟨ 𝓑 ⟩ b∞
        α∞' (n , p) = ⟨ 𝓑 ⟩-trans (g n p) (b n) b∞ (α n p) (⟨ 𝓑 ⟩-⋁-is-ub b n)

      β∞ : (u : ⟨ 𝓑 ⟩) → ((q : ∃ n ꞉ ℕ , P n) → f q ≤⟨ 𝓑 ⟩ u) → b∞ ≤⟨ 𝓑 ⟩ u
      β∞ u ψ = ⟨ 𝓑 ⟩-⋁-is-lb-of-ubs b u l
       where
        l : (n : ℕ) → b n ≤⟨ 𝓑 ⟩ u
        l n = β n u (λ p → ψ ∣ n , p ∣)

\end{code}

We repackage the above.

\begin{code}

  module _ {𝓥 𝓦 : Universe}
           (𝓑 : σ-SupLat 𝓥 𝓦)
           (P : 𝓣 ̇ )
           (i : is-quasidecidable P)
           (f : P → ⟨ 𝓑 ⟩)
         where

    sup : ⟨ 𝓑 ⟩
    sup = pr₁ (σ-suplats-have-quasidecidable-joins 𝓑 P i f)

    sup-is-ub : (p : P) → f p ≤⟨ 𝓑 ⟩ sup
    sup-is-ub = pr₁ (pr₂ (σ-suplats-have-quasidecidable-joins 𝓑 P i f))

    sup-is-lb-of-ubs : (u : ⟨ 𝓑 ⟩) → ((p : P) → f p ≤⟨ 𝓑 ⟩ u) → sup ≤⟨ 𝓑 ⟩ u
    sup-is-lb-of-ubs = pr₂ (pr₂ (σ-suplats-have-quasidecidable-joins 𝓑 P i f))

\end{code}

We say that a map is a q-embedding if its fibers are all
quasidecidable. We define three versions of the same definition to
help Agda to solve constraints.

\begin{code}

  is-q-embedding : {X : 𝓣 ̇ } {Y : 𝓣 ̇ } → (X → Y) → 𝓣 ⁺ ̇
  is-q-embedding f = ∀ y → is-quasidecidable (fiber f y)

  is-q-embeddingl : {X : 𝓣 ̇ } {Y : 𝓤₀ ̇ } → (X → Y) → 𝓣 ⁺ ̇
  is-q-embeddingl f = ∀ y → is-quasidecidable (fiber f y)

  is-q-embeddingr : {X : 𝓤₀ ̇ } {Y : 𝓣 ̇ } → (X → Y) → 𝓣 ⁺ ̇
  is-q-embeddingr f = ∀ y → is-quasidecidable (fiber f y)

\end{code}

The following generalizes the existence of quasidecidable-indexed
joins.

\begin{code}

  σ-suplats-have-quasidecidable-joins'
   : (𝓑 : σ-SupLat 𝓥 𝓦) {I : 𝓣 ̇ }
   → (f : I → ℕ)
   → is-q-embeddingl f
   → (b : ℕ → ⟨ 𝓑 ⟩)
   → Σ c ꞉ ⟨ 𝓑 ⟩ , (c is-the-join-of (b ∘ f) on 𝓑)
  σ-suplats-have-quasidecidable-joins' {𝓥} {𝓦} 𝓑 {I} f q b
   = c , α , β
   where
    g : I → ⟨ 𝓑 ⟩
    g = b ∘ f

    a : ℕ → A
    a n = pr₁ (q n)

    e : (n : ℕ) → τ (a n) holds ＝ (Σ i ꞉ I , f i ＝ n)
    e n = pr₂ (q n)

    γ : (n : ℕ) → τ (a n) holds → (Σ i ꞉ I , f i ＝ n)
    γ n = Idtofun (e n)

    δ : (n : ℕ)  → (Σ i ꞉ I , f i ＝ n) → τ (a n) holds
    δ n = Idtofun ((e n)⁻¹)

    g' : (n : ℕ) → τ (a n) holds → ⟨ 𝓑 ⟩
    g' n h = g (pr₁ (γ n h))

    b' : ℕ → ⟨ 𝓑 ⟩
    b' n = sup 𝓑 (τ (a n) holds) (a n , refl) (g' n)

    c : ⟨ 𝓑 ⟩
    c = ⋁⟨ 𝓑 ⟩ b'

    α : ∀ i → b (f i) ≤⟨ 𝓑 ⟩ c
    α i = ⟨ 𝓑 ⟩-trans (b (f i)) (b' (f i)) c l₂ l₀
     where
      l₀ : b' (f i) ≤⟨ 𝓑 ⟩ c
      l₀ = ⟨ 𝓑 ⟩-⋁-is-ub b' (f i)

      l₁ : g' (f i) (δ (f i) (i , refl)) ≤⟨ 𝓑 ⟩ b' (f i)
      l₁ = sup-is-ub 𝓑
            (τ (a (f i)) holds)
            (a (f i) , refl)
            (g' (f i))
            (δ (f i)
            (i , refl))

      r : g' (f i) (δ (f i) (i , refl))
        ＝ b (f (pr₁ (γ (f i) (δ (f i) (i , refl)))))
      r = refl

      s : b (f (pr₁ (γ (f i) (δ (f i) (i , refl))))) ＝ b (f i)
      s = ap (λ - → b (f (pr₁ -))) (Idtofun-retraction (e (f i)) (i , refl))

      t : g' (f i) (δ (f i) (i , refl)) ＝ b (f i)
      t = s

      l₂ : b (f i) ≤⟨ 𝓑 ⟩ b' (f i)
      l₂ = transport (λ - → - ≤⟨ 𝓑 ⟩ b' (f i)) s l₁

    β : (u : ⟨ 𝓑 ⟩) → (∀ i → b (f i) ≤⟨ 𝓑 ⟩ u) → c ≤⟨ 𝓑 ⟩ u
    β u φ = ⟨ 𝓑 ⟩-⋁-is-lb-of-ubs b' u l
     where
      φ' : (n : ℕ) (h : τ (a n) holds) → g' n h ≤⟨ 𝓑 ⟩ u
      φ' n h = φ (pr₁ (γ n h))

      l : (n : ℕ) → b' n ≤⟨ 𝓑 ⟩ u
      l n = sup-is-lb-of-ubs 𝓑 (τ (a n) holds) (a n , refl) (g' n) u (φ' n)

\end{code}

We now generalize and resize part of the above (without resizing
axioms) by replacing equality by equivalence in the definition of
quasidecidability:

\begin{code}

  is-quasidecidable' : 𝓥 ̇ → 𝓣 ⊔ 𝓥 ̇
  is-quasidecidable' P = Σ a ꞉ A , (τ a holds ≃ P)

  is-quasidecidable₀ : 𝓣 ̇ → 𝓣 ̇
  is-quasidecidable₀ = is-quasidecidable' {𝓣}

  quasidecidability-resizing : (P : 𝓣 ̇ )
                             → is-quasidecidable P ≃ is-quasidecidable₀ P
  quasidecidability-resizing P = Σ-cong e
   where
    e : (a : A) → (τ a holds ＝ P) ≃ (τ a holds ≃ P)
    e a = prop-univalent-≃' pe fe P (τ a holds) (holds-is-prop (τ a))

  being-quasidecidable₀-is-prop : (P : 𝓣 ̇ ) → is-prop (is-quasidecidable₀ P)
  being-quasidecidable₀-is-prop P = equiv-to-prop
                                     (≃-sym (quasidecidability-resizing P))
                                     (being-quasidecidable-is-prop P)

  𝟘-is-quasidecidable₀ : is-quasidecidable₀ 𝟘
  𝟘-is-quasidecidable₀ = ⌜ quasidecidability-resizing 𝟘 ⌝ 𝟘-is-quasidecidable

  𝟙-is-quasidecidable₀ : is-quasidecidable₀ 𝟙
  𝟙-is-quasidecidable₀ = ⌜ quasidecidability-resizing 𝟙 ⌝ 𝟙-is-quasidecidable

  quasidecidable₀-closed-under-ω-joins
   : (P : ℕ → 𝓣 ̇ )
   → ((n : ℕ) → is-quasidecidable₀ (P n))
   → is-quasidecidable₀ (∃ n ꞉ ℕ , P n)
  quasidecidable₀-closed-under-ω-joins P φ =
   ⌜ quasidecidability-resizing (∃ n ꞉ ℕ , P n) ⌝
    (quasidecidable-closed-under-ω-joins P φ')
   where
    φ' : (n : ℕ) → is-quasidecidable (P n)
    φ' n = ⌜ quasidecidability-resizing (P n) ⌝⁻¹ (φ n)

  quasidecidable₀-induction
   : (F : 𝓣 ̇ → 𝓥 ̇ )
   → ((P : 𝓣 ̇ ) → is-prop (F P))
   → F 𝟘
   → F 𝟙
   → ((P : ℕ → 𝓣 ̇ ) → ((n : ℕ) → F (P n)) → F (∃ n ꞉ ℕ , P n))
   → (P : 𝓣 ̇ ) → is-quasidecidable₀ P → F P
  quasidecidable₀-induction F i F₀ F₁ Fω P q
   = quasidecidable-induction F i F₀ F₁ Fω P (⌜ quasidecidability-resizing P ⌝⁻¹ q)

\end{code}

This concludes the module hypothetical-free-σ-SupLat-on-one-generator.

We now give the proofs of the main theorems by calling the above modules.

\begin{code}

theorem₁ {𝓣} {𝓤} q = free-σ-SupLat-on-one-generator QD ⊤ QD-is-free-σ-SupLat
 where
  open quasidecidable-propositions-exist q
  open hypothetical-quasidecidability {𝓣} {𝓤}
        (quasidecidable-propositions
          is-quasidecidable
          being-quasidecidable-is-prop
          𝟘-is-quasidecidable
          𝟙-is-quasidecidable
          quasidecidable-closed-under-ω-joins
          quasidecidable-induction)

theorem₂ {𝓣} {𝓤} f = quasidecidable-propositions
                       is-quasidecidable₀
                       being-quasidecidable₀-is-prop
                       𝟘-is-quasidecidable₀
                       𝟙-is-quasidecidable₀
                       quasidecidable₀-closed-under-ω-joins
                       quasidecidable₀-induction
 where
  open free-σ-SupLat-on-one-generator-exists f
  open hypothetical-free-σ-SupLat-on-one-generator
  open assumptions {𝓣} {𝓤} 𝓐 ⊤ 𝓐-free

theorem₃ {𝓣} {𝓚} f = initial-σ-frame A-qua-σ-frame A-qua-σ-frame-is-initial
 where
  open free-σ-SupLat-on-one-generator-exists f
  open hypothetical-free-σ-SupLat-on-one-generator
  open assumptions {𝓣} {𝓚} 𝓐 ⊤ 𝓐-free

theorem₄ {𝓣} {𝓚} ρ = quasidecidable-propositions
                       is-quasidecidable
                       being-quasidecidable-is-prop
                       𝟘-is-quasidecidable
                       𝟙-is-quasidecidable
                       quasidecidable-closed-under-ω-joins
                       quasidecidable-induction
 where
  open quasidecidability-construction-from-resizing 𝓣 𝓚 ρ

\end{code}

TODO.

  * Very little here has to do with the nature of the type ℕ. We never
    used zero, successor, or induction! (But they are used in another
    module to construct binary joins, which are not used here.) Any
    indexing type replacing ℕ works in the above development, with the
    definition of σ-sup-lattice generalized to have an arbitrary (but
    fixed) indexing type in place of ℕ. (We could have multiple
    indexing types, but this would require a modification of the above
    development.)

  * Define, by induction (or as a W-type) a type similar to the
    Brouwer ordinals, with two constructors 0 and 1 and a formal
    ℕ-indexed sup operation. We have a unique map to the initial
    σ-sup-lattice that transforms formal sups into sups and maps 0 to
    ⊥ and 1 to ⊤. Is this function a surjection (it is definitely not
    an injection), or what (known) axioms are needed for it to be a
    surjection? Countable choice suffices. But is it necessary? It
    seems likely that the choice principle studied in the above paper
    with Cory Knapp is necessary and sufficient. This principle
    implies that the quasidecidable propositions agree with the
    semidecidable ones.
