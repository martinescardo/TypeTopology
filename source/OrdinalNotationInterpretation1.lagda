Martin Escardo, 2012, 2018, 2022

Compact ordinals, discrete ordinals and their relationships.

A 4-page abstract of a talk at Types'2019:
https://www.cs.bham.ac.uk/~mhe/papers/compact-ordinals-Types-2019-abstract.pdf

Begun December 2012, based on earlier work, circa 2010.

Most of the work has been done later, and coded in July 2018 after a
long pause to understand univalent foundations, which is what we use
in this development, and to develop the mathematical basis for this in
other modules.

Here an ordinal is a type equipped with a well order, namely
relation < which is

  * prop valued,
  * well founded,
  * transitive, and
  * extensional (any two elements with the same lower set are equal).

The extensionality axiom implies that the underlying type of an
ordinal is a set (or satisfies the K axiom), which is proved in the
module OrdinalNotions. This seems to be a new observation about the
univalent notion of ordinal (as introduced in the HoTT Book).

A dependency graph of this module is available at
https://www.cs.bham.ac.uk/~mhe/TypeTopology/OrdinalNotationInterpretation.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalNotationInterpretation1 (fe : FunExt) where

\end{code}

We work with ordinal encodings, or ordinal expressions, that are
slightly different from the traditional Brouwer ordinal trees, which
we also consider towards the end of this article.

\begin{code}

data OE : 𝓤₀ ̇ where
 One : OE
 Add : OE → OE → OE
 Mul : OE → OE → OE
 L   : (ℕ → OE) → OE

\end{code}

We consider two mappings from these ordinal expressions to actual
ordinals as discussed above:

  * Δ : OE → Ordᵀ
  * Κ : OE → Ordᵀ

Here Ordᵀ is the type of ordinals that have a top element (which, in
constructive mathematics, are not in general successor
ordinals). Technically, the top element allows us to prove the closure
of ordinals under ordinal-indexed sums, playing a crucial role in the
proof of extensionality of the sum. But the top element is equally
crucial for compactness purposes, as dicussed below.

  * The ordinals in the image of Δ are discrete (have decidable
    equality) and have countable underlying sets, which are in fact
    retracts of ℕ.

  * Those in the image of Κ are compact, or "exhaustibly searchable".

    Moreover, they are retracts of the Cantor type (ℕ → 𝟚) of binary
    sequences, and hence are totally separated, which means that the
    functions into 𝟚 separate the points.

    And not only the Κ ordinals are searchable, they are also
    inf-compact, which means that any detachable subset has an
    infimum, which belongs to the subset iff and only if the subset is
    non-empty (with non-emptiness expressed by a double negation).

    The discrete ordinals, being retracts of ℕ, cannot be retracts of
    the Cantor space. This is because the Cantor space is potentially
    compact, in the presence of Brouwerian axioms (which we are not
    assuming but are consistent), and compactness is inherited by
    retracts, and the compactnesss of the infinite discrete ordinals
    is equivalent to Bishop's LPO (limited principle of omnscient),
    which is not provable in any variety of constructive mathematics.

The Δ and Κ interpretation of One, Add and Mul are as expected. They
differ only in the interpretation of S.

   * In the discrete case, S is interpreted as simply the countable
     sum plus the ordinal 𝟙 (written ∑₁).

   * In the compact case, S is interpreted as the sum with an added
     non-isolated top point (written ∑¹). It is this that makes the
     searchability of the compact ordinals possible. The searchability
     of the discrete ordinals is a contructive taboo.

Additionally, we kave a map ι from the Δ-ordinals to the Κ-ordinals,
which is

  * an embedding (has subsingleton fibers),
  * dense (the complement of its image is empty),
  * order preserving and reflecting.

Lastly, we have a mapping from our ordinal trees to Brouwer trees that
allows us to use other people's constructions to get very "large"
compact ordinals. As a trivial example, we show how to map a Brouwer
code of ε₀ to a compact ordinal that dominates ε₀.

The bulk of the work to perform these constructions and prove their
properties is developed in the imported modules.

After a brief pause for importing the necessary definitions, we state
the theorems and constructions to be performed here:

\begin{code}

open import OrdinalsType
open import ToppedOrdinalsType fe
open import OrdinalArithmetic fe
open import ToppedOrdinalArithmetic fe
open import OrdinalsClosure fe
open import OrdinalCodes
open import CompactTypes
open import TotallySeparated
open import SquashedSum fe
open import SquashedCantor fe hiding (Κ)
open import DiscreteAndSeparated
open import Density
open import PairFun
open import SigmaDiscreteAndTotallySeparated

open import UF-Subsingletons
open import UF-Retracts
open import UF-Embeddings

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

\end{code}

In the following, ⟪ τ ⟫ denotes the underlying set of an ordinal τ, and
_≺⟪ τ ⟫_ denotes its underlying order.

\begin{code}

Κ                            : OE → Ordᵀ
Κ-compact∙                   : (ν : OE) → compact∙ ⟪ Κ ν ⟫
Κ-Cantor-retract             : (ν : OE) → retract ⟪ Κ ν ⟫ of (ℕ → 𝟚)
Κ-is-totally-separated       : (ν : OE) → is-totally-separated ⟪ Κ ν ⟫

Δ                            : OE → Ordᵀ
Δ-retract-of-ℕ               : (ν : OE) → retract ⟪ Δ ν ⟫ of ℕ
Δ-is-discrete                : (ν : OE) → is-discrete ⟪ Δ ν ⟫

ι                            : {ν : OE} → ⟪ Δ ν ⟫ → ⟪ Κ ν ⟫
ι-is-dense                   : (ν : OE) → is-dense (ι {ν})
ι-is-embedding               : (ν : OE) → is-embedding (ι {ν})

ι-is-order-preserving        : (ν : OE) (x y : ⟪ Δ ν ⟫)
                             →   x ≺⟪ Δ ν ⟫   y
                             → ι x ≺⟪ Κ ν ⟫ ι y

ι-is-order-reflecting        : (ν : OE) (x y : ⟪ Δ ν ⟫)
                             → ι x ≺⟪ Κ ν ⟫ ι y
                             →   x ≺⟪ Δ ν ⟫   y

Κ-has-infs-of-complemented-subsets
                             : propext 𝓤₀
                             → (ν : OE) → has-infs-of-complemented-subsets (Κ ν)

brouwer-to-oe                : B → OE
ε₀-upper-bound               : Ordᵀ
compact∙-ε₀-ub               : compact∙ ⟪ ε₀-upper-bound ⟫

\end{code}

The interpretation function is the following, with values on topped
ordinals, where an ordinal is a type equipped with a
prop-valued, well-founded, transitive and extensional relation
(and such a type is automatically a set). "Topped" means that there is
a top element in the order

This version of the function is from 1st July 2018 (the original
version considered only the underlying set of the ordinal and didn't
construct the order as this was work in progress):

\begin{code}

Κ One       = 𝟙ᵒ
Κ (Add ν μ) = Κ ν +ᵒ Κ μ
Κ (Mul ν μ) = Κ ν ×ᵒ  Κ μ
Κ (L ν)     = ∑¹ (Κ ∘ ν)

\end{code}

The underlying sets  of such ordinals are compact∙:

\begin{code}

Κ-compact∙ One       = 𝟙-compact∙
Κ-compact∙ (Add ν μ) = Σ-compact∙
                        𝟙+𝟙-compact∙
                        (dep-cases (λ _ → Κ-compact∙ ν) (λ _ → Κ-compact∙ μ))
Κ-compact∙ (Mul ν μ) = Σ-compact∙ (Κ-compact∙ ν) (λ _ → Κ-compact∙ μ)
Κ-compact∙ (L ν)     = Σ¹-compact∙ (λ n → ⟪ Κ (ν n) ⟫) (λ n → Κ-compact∙ (ν n))

\end{code}

Completed 20th July 2018:

The compact∙ ordinals are retracts of the Cantor type (ℕ → 𝟚).

\begin{code}

Κ-Cantor-retract One       = (λ _ → ⋆) , (λ _ → λ n → ₀) , 𝟙-is-prop ⋆
Κ-Cantor-retract (Add ν μ) = +-retract-of-Cantor (Κ ν) (Κ μ)
                              (Κ-Cantor-retract ν) (Κ-Cantor-retract μ)
Κ-Cantor-retract (Mul ν μ) = ×-retract-of-Cantor (Κ ν) (Κ μ)
                              (Κ-Cantor-retract ν) (Κ-Cantor-retract μ)
Κ-Cantor-retract (L ν)     = Σ¹-Cantor-retract
                               (λ n → ⟪ Κ (ν n) ⟫) (λ i → Κ-Cantor-retract (ν i))
\end{code}

And hence they are totally separated:

\begin{code}

Κ-is-totally-separated ν = retract-of-totally-separated
                             (Κ-Cantor-retract ν)
                             (Cantor-is-totally-separated fe₀)
\end{code}

Without total separatedness (enough functions into the type 𝟚 of
booleans), compactness wouldn't be an interesting property. It is
not possible to prove total separatedness directly, because this
property is not closed under Σ, which is used to define +ᵒ, ×ᵒ and Σ₁,
as shown in the module FailureOfTotalSeparatedness.

Classically, the squashed sum is the ordinal sum plus 1, and now we
give an alternative semantics of ordinal codes with this
interpretation, which produces ordinals with discrete underlying
sets. Moreover, there is a function that maps the underlying set of
the discrete version to the underlying set of the above version, with
many interesting properties, formulated above and proved below.

\begin{code}

Δ One       = 𝟙ᵒ
Δ (Add ν μ) = Δ ν +ᵒ Δ μ
Δ (Mul ν μ) = Δ ν ×ᵒ  Δ μ
Δ (L ν)     = ∑₁ (Δ ∘ ν)

Δ-is-discrete One       = 𝟙-is-discrete
Δ-is-discrete (Add ν μ) = Σ-is-discrete
                           (+-is-discrete 𝟙-is-discrete 𝟙-is-discrete)
                           (dep-cases (λ _ → Δ-is-discrete ν)
                           (λ _ → Δ-is-discrete μ))
Δ-is-discrete (Mul ν μ) = Σ-is-discrete (Δ-is-discrete ν) (λ _ → Δ-is-discrete μ)
Δ-is-discrete (L ν)     = Σ₁-is-discrete
                            (λ n → ⟪ Δ (ν n) ⟫)
                            (λ i → Δ-is-discrete (ν i))
\end{code}

Completed 27 July 2018. There is a dense embedding ι of the discrete
ordinals into the compact∙ ordinals, where density means that the
complement of the image of the embedding is empty. Moreover, it is
order preserving and reflecting (28 July 2018).

\begin{code}

ι {One}     = id
ι {Add ν μ} = pair-fun id (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
ι {Mul ν μ} = pair-fun (ι {ν}) (λ _ → ι {μ})
ι {L ν}     = ∑↑ (λ n → Δ (ν n)) (λ n → Κ (ν n)) (λ n → ι {ν n})

ι-is-dense One       = id-is-dense
ι-is-dense (Add ν μ) = pair-fun-dense
                        id
                        (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                        id-is-dense
                        (dep-cases (λ _ → ι-is-dense ν) (λ _ → ι-is-dense μ))
ι-is-dense (Mul ν μ) = pair-fun-dense _ _
                        (ι-is-dense ν)
                        (λ _ → ι-is-dense μ)
ι-is-dense (L ν)     =  Σ↑-dense
                        (λ n → ⟪ Δ (ν n) ⟫)
                        (λ n → ⟪ Κ (ν n) ⟫)
                        (λ n → ι {ν n})
                        (λ i → ι-is-dense (ν i))

ι-is-embedding One       = id-is-embedding
ι-is-embedding (Add ν μ) = pair-fun-is-embedding
                            id
                            (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                            id-is-embedding
                            (dep-cases (λ _ → ι-is-embedding ν) (λ _ → ι-is-embedding μ))
ι-is-embedding (Mul ν μ) = pair-fun-is-embedding _ _
                            (ι-is-embedding ν)
                            (λ _ → ι-is-embedding μ)
ι-is-embedding (L ν)     = Σ↑-embedding
                            (λ n → ⟪ Δ (ν n) ⟫)
                            (λ n → ⟪ Κ (ν n) ⟫)
                            (λ n → ι {ν n})
                            (λ i → ι-is-embedding (ν i))

ι-is-order-preserving One       = λ x y l → l
ι-is-order-preserving (Add ν μ) = pair-fun-is-order-preserving
                                   𝟚ᵒ
                                   𝟚ᵒ
                                   (cases (λ _ → Δ ν) (λ _ → Δ μ))
                                   (cases (λ _ → Κ ν) (λ _ → Κ μ))
                                   id
                                   (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                                   (λ x y l → l)
                                   (dep-cases (λ _ → ι-is-order-preserving ν)
                                              (λ _ → ι-is-order-preserving μ))
ι-is-order-preserving (Mul ν μ) = pair-fun-is-order-preserving
                                   (Δ ν)
                                   (Κ ν)
                                   (λ _ → Δ μ)
                                   (λ _ → Κ μ)
                                   (ι {ν})
                                   (λ _ → ι {μ})
                                   (ι-is-order-preserving ν)
                                   (λ _ → ι-is-order-preserving μ)
ι-is-order-preserving (L ν)    = ∑↑-is-order-preserving
                                  (Δ ∘ ν)
                                  (Κ ∘ ν)
                                  (λ n → ι {ν n})
                                  (λ i → ι-is-order-preserving (ν i))

ι-is-order-reflecting One       = λ x y l → l
ι-is-order-reflecting (Add ν μ) = pair-fun-is-order-reflecting
                                    𝟚ᵒ
                                    𝟚ᵒ
                                    (cases (λ _ → Δ ν) (λ _ → Δ μ))
                                    (cases (λ _ → Κ ν) (λ _ → Κ μ))
                                    id
                                    (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                                    (λ x y l → l)
                                    id-is-embedding
                                    (dep-cases (λ _ → ι-is-order-reflecting ν)
                                               (λ _ → ι-is-order-reflecting μ))
ι-is-order-reflecting (Mul ν μ) = pair-fun-is-order-reflecting
                                   (Δ ν)
                                   (Κ ν)
                                   (λ _ → Δ μ)
                                   (λ _ → Κ μ)
                                   (ι {ν})
                                   (λ _ → ι {μ})
                                   (ι-is-order-reflecting ν)
                                   (ι-is-embedding ν)
                                   (λ _ → ι-is-order-reflecting μ)
ι-is-order-reflecting (L ν)     = ∑↑-is-order-reflecting
                                    (Δ ∘ ν)
                                    (Κ ∘ ν)
                                    (λ n → ι {ν n})
                                    (λ i → ι-is-order-reflecting (ν i))
\end{code}

As discussed in the module Ordinals, propositional extensionality in
the following construction is not strictly needed but makes our life
much easier (given the mathematics we have already developed).

\begin{code}

Κ-has-infs-of-complemented-subsets pe One       = 𝟙ᵒ-has-infs-of-complemented-subsets
Κ-has-infs-of-complemented-subsets pe (Add ν μ) =
 ∑-has-infs-of-complemented-subsets pe
  𝟚ᵒ
  (cases (λ _ → Κ ν) (λ _ → Κ μ))
  𝟚ᵒ-has-infs-of-complemented-subsets
  (dep-cases (λ _ → Κ-has-infs-of-complemented-subsets pe ν)
                                                        (λ _ → Κ-has-infs-of-complemented-subsets pe μ))
Κ-has-infs-of-complemented-subsets pe (Mul ν μ) =
 ∑-has-infs-of-complemented-subsets pe
  (Κ ν)
  (λ _ → Κ μ)
  (Κ-has-infs-of-complemented-subsets pe ν)
  (λ _ → Κ-has-infs-of-complemented-subsets pe μ)
Κ-has-infs-of-complemented-subsets pe (L ν) =
 ∑₁-has-infs-of-complemented-subsets
   pe
   (Κ ∘ ν)
   (λ i → Κ-has-infs-of-complemented-subsets pe (ν i))

\end{code}

Added 31 July 2018:

\begin{code}

Δ-retract-of-ℕ One       = (λ _ → ⋆) , (λ _ → 0) , 𝟙-is-prop ⋆
Δ-retract-of-ℕ (Add ν μ) = Σ-retract-of-ℕ
                             retract-𝟙+𝟙-of-ℕ
                             (dep-cases (λ _ → Δ-retract-of-ℕ ν)
                                        (λ _ → Δ-retract-of-ℕ μ))
Δ-retract-of-ℕ (Mul ν μ) = Σ-retract-of-ℕ
                             (Δ-retract-of-ℕ ν)
                             (λ _ → Δ-retract-of-ℕ μ)
Δ-retract-of-ℕ (L ν)     = Σ₁-ℕ-retract (λ i → Δ-retract-of-ℕ (ν i))

\end{code}

NB. We could have proved that the Δ-ordinals are discrete using the
above, as discrete types are closed under retracts.

Hence the compactness of any infinite discrete ordinal is a
constructive taboo, logically equivalent to Bishop's LPO.

Brouwer ordinal codes can be mapped to compact∙ ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal, because sums dominate suprema.

\begin{code}

brouwer-to-oe    Z  = One
brouwer-to-oe (S ν) = Add One (brouwer-to-oe ν)
brouwer-to-oe (L ν) = L (λ i → brouwer-to-oe (ν i))

\end{code}

The following is a relatively "small" example: an upper bound of the
ordinal ε₀ (because sums dominate suprema):

\begin{code}

ε₀-upper-bound = Κ (brouwer-to-oe B-ε₀)

compact∙-ε₀-ub = Κ-compact∙ (brouwer-to-oe B-ε₀)

\end{code}

We can go much higher using the work of and Setzer, Hancock and
others.

Added 4th April 2022. A third interpretation of ordinal expressions.

\begin{code}

open import GenericConvergentSequence
open import ConvergentSequenceCompact
open import PropTychonoff

open import UF-PropTrunc
open import UF-Univalence
open import UF-Equiv
open import UF-Size

module _ (pt : propositional-truncations-exist)
         (ua : Univalence)
       where

 open PropositionalTruncation pt

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

 open import OrdinalOfOrdinalsSuprema ua
 open import OrdinalsType-Injectivity fe
 open import OrdinalOfOrdinals ua
 open import OrdinalArithmetic-Properties ua

 open import UF-ImageAndSurjection
 open ImageAndSurjection pt
 open ordinals-injectivity

 module _ (sr : Set-Replacement pt) where

  open suprema pt sr

  private
   extension : (ℕ → Ordinal 𝓤₀) → (ℕ∞ → Ordinal 𝓤₀)
   extension α = α ↗ (embedding-ℕ-to-ℕ∞ fe')

  𝓢 : OE → Ordinal 𝓤₀
  𝓢 One       = 𝟙ₒ
  𝓢 (Add ν μ) = 𝓢 ν +ₒ 𝓢 μ
  𝓢 (Mul ν μ) = 𝓢 ν ×ₒ 𝓢 μ
  𝓢 (L ν)     = sup (extension (𝓢 ∘ ν))

  𝓢-compact∙ : (ν : OE) → compact∙ ⟨ 𝓢 ν ⟩
  𝓢-compact∙ One       = 𝟙-compact∙
  𝓢-compact∙ (Add ν μ) = +-compact∙ (𝓢-compact∙ ν) (𝓢-compact∙ μ)
  𝓢-compact∙ (Mul ν μ) = ×-compact∙ (𝓢-compact∙ ν) (𝓢-compact∙ μ)
  𝓢-compact∙ (L ν)     = surjection-compact∙ pt
                           (sum-to-sup (extension (𝓢 ∘ ν)))
                           (sum-to-sup-is-surjection (extension (𝓢 ∘ ν)))
                           (Σ-compact∙
                             (ℕ∞-compact∙ fe₀)
                             (λ u → prop-tychonoff fe
                                     (ℕ-to-ℕ∞-is-embedding fe₀ u)
                                     (λ (i , _) → 𝓢-compact∙ (ν i))))

  σ : (ν : OE) → ⟪ Κ ν ⟫ → ⟨ 𝓢 ν ⟩
  σ One       x           = x
  σ (Add ν μ) (inl ⋆ , x) = inl (σ ν x)
  σ (Add ν μ) (inr ⋆ , y) = inr (σ μ y)
  σ (Mul ν μ) (x , y)     = (σ ν x , σ μ y)
  σ (L ν)     (u , f)     = sum-to-sup (extension (𝓢 ∘ ν)) (u , g)
   where
    g : ((i , _) : fiber ℕ-to-ℕ∞ u) → ⟨ 𝓢 (ν i) ⟩
    g (i , p) = σ (ν i) (f (i , p))

\end{code}

More can be said about this.
