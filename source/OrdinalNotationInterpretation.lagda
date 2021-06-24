Martin Escardo, 2012, 2018.

Compact ordinals, discrete ordinals and their relationships.

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

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalNotationInterpretation (fe : FunExt) where

\end{code}

We work with ordinal encodings, or ordinal expressions, that are
slightly different from the traditional Brouwer ordinal trees, which
we also consider towards the end of this article.

\begin{code}

data OE : 𝓤₀ ̇ where
 One  : OE
 Add  : OE → OE → OE
 Mul  : OE → OE → OE
 Sum1 : (ℕ → OE) → OE

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
differ only in the interpretation of Sum1.

   * In the discrete case, Sum1 is interpreted as simply the countable
     sum plus the ordinal 𝟙 (written ∑₁).

   * In the compact case, Sum1 is interpreted as the sum with an added
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
open import InfCompact
open import TotallySeparated
open import SquashedSum fe
open import SquashedCantor fe hiding (Κ)
open import DiscreteAndSeparated

open import UF-Subsingletons
open import UF-Retracts
open import UF-Embeddings
open import UF-Miscelanea

\end{code}

In the following, ⟪ τ ⟫ denotes the underlying set of an ordinal τ, and
_≺⟪ τ ⟫_ denotes its underlying order.

\begin{code}

Κ                      : OE → Ordᵀ
Κ-compact∙             : (ν : OE) → compact∙ ⟪ Κ ν ⟫
Κ-Cantor-retract       : (ν : OE) → retract ⟪ Κ ν ⟫ of (ℕ → 𝟚)
Κ-is-totally-separated : (ν : OE) → is-totally-separated ⟪ Κ ν ⟫

Δ                      : OE → Ordᵀ
Δ-retract-of-ℕ         : (ν : OE) → retract ⟪ Δ ν ⟫ of ℕ
Δ-is-discrete          : (ν : OE) → is-discrete ⟪ Δ ν ⟫

ι                      : {ν : OE} → ⟪ Δ ν ⟫ → ⟪ Κ ν ⟫
ι-dense                : (ν : OE) → is-dense (ι {ν})
ι-embedding            : (ν : OE) → is-embedding (ι {ν})

ι-order-preserving     : (ν : OE) (x y : ⟪ Δ ν ⟫)
                            →   x ≺⟪ Δ ν ⟫   y
                            → ι x ≺⟪ Κ ν ⟫ ι y

ι-order-reflecting     : (ν : OE) (x y : ⟪ Δ ν ⟫)
                            → ι x ≺⟪ Κ ν ⟫ ι y
                            →   x ≺⟪ Δ ν ⟫   y

Κ-inf-compact          : propext 𝓤₀
                       → (ν : OE) → inf-compact (λ x y → x ≼⟪ Κ ν ⟫ y)

brouwer-to-oe          : B → OE
ε₀-upper-bound         : Ordᵀ
compact∙-ε₀-ub         : compact∙ ⟪ ε₀-upper-bound ⟫

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

Κ One  = 𝟙ᵒ
Κ (Add ν μ) = Κ ν +ᵒ Κ μ
Κ (Mul ν μ) = Κ ν ×ᵒ  Κ μ
Κ (Sum1 ν) = ∑¹ λ(i : ℕ) → Κ(ν i)

\end{code}

The underlying sets  of such ordinals are compact∙:

\begin{code}

Κ-compact∙ One       = 𝟙-compact∙
Κ-compact∙ (Add ν μ) = Σ-compact∙
                        𝟙+𝟙-compact∙
                        (dep-cases (λ _ → Κ-compact∙ ν) (λ _ → Κ-compact∙ μ))
Κ-compact∙ (Mul ν μ) = Σ-compact∙ (Κ-compact∙ ν) (λ _ → Κ-compact∙ μ)
Κ-compact∙ (Sum1 ν)  = Σ¹-compact∙ (λ n → ⟪ Κ (ν n) ⟫) (λ i → Κ-compact∙ (ν i))

\end{code}

Completed 20th July 2018:

The compact∙ ordinals are retracts of the Cantor type (ℕ → 𝟚).

\begin{code}

Κ-Cantor-retract One       = (λ _ → *) , (λ _ → λ n → ₀) , 𝟙-is-prop *
Κ-Cantor-retract (Add ν μ) = +-retract-of-Cantor (Κ ν) (Κ μ)
                              (Κ-Cantor-retract ν) (Κ-Cantor-retract μ)
Κ-Cantor-retract (Mul ν μ) = ×-retract-of-Cantor (Κ ν) (Κ μ)
                              (Κ-Cantor-retract ν) (Κ-Cantor-retract μ)
Κ-Cantor-retract (Sum1 ν)  = Σ¹-Cantor-retract
                               (λ n → ⟪ Κ (ν n) ⟫) (λ i → Κ-Cantor-retract (ν i))
\end{code}

And hence they are totally separated:

\begin{code}

Κ-is-totally-separated ν = retract-totally-separated
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
Δ (Sum1 ν)  = ∑₁ λ(i : ℕ) → Δ(ν i)

Δ-is-discrete One       = 𝟙-is-discrete
Δ-is-discrete (Add ν μ) = Σ-is-discrete
                           (+discrete 𝟙-is-discrete 𝟙-is-discrete)
                          (dep-cases (λ _ → Δ-is-discrete ν)
                          (λ _ → Δ-is-discrete μ))
Δ-is-discrete (Mul ν μ) = Σ-is-discrete (Δ-is-discrete ν) (λ _ → Δ-is-discrete μ)
Δ-is-discrete (Sum1 ν)  = Σ₁-is-discrete
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
ι {Sum1 ν}  = ∑↑ (λ n → Δ (ν n)) (λ n → Κ (ν n)) (λ n → ι {ν n})

ι-dense One       = id-is-dense
ι-dense (Add ν μ) = pair-fun-dense
                     id
                    (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                    id-is-dense
                    (dep-cases (λ _ → ι-dense ν) (λ _ → ι-dense μ))
ι-dense (Mul ν μ) = pair-fun-dense _ _
                    (ι-dense ν)
                    (λ _ → ι-dense μ)
ι-dense (Sum1 ν) =  Σ↑-dense
                     (λ n → ⟪ Δ (ν n) ⟫)
                     (λ n → ⟪ Κ (ν n) ⟫)
                     (λ n → ι {ν n})
                     (λ i → ι-dense (ν i))

ι-embedding One       = id-is-embedding
ι-embedding (Add ν μ) = pair-fun-is-embedding
                         id
                         (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                         id-is-embedding
                         (dep-cases (λ _ → ι-embedding ν) (λ _ → ι-embedding μ))
ι-embedding (Mul ν μ) = pair-fun-is-embedding _ _
                         (ι-embedding ν)
                         (λ _ → ι-embedding μ)
ι-embedding (Sum1 ν)  = Σ↑-embedding
                         (λ n → ⟪ Δ (ν n) ⟫)
                         (λ n → ⟪ Κ (ν n) ⟫)
                         (λ n → ι {ν n})
                         (λ i → ι-embedding (ν i))

ι-order-preserving One       = λ x y l → l
ι-order-preserving (Add ν μ) = pair-fun-is-order-preserving
                                𝟚ᵒ
                                𝟚ᵒ
                                (cases (λ _ → Δ ν) (λ _ → Δ μ))
                                (cases (λ _ → Κ ν) (λ _ → Κ μ))
                                id
                                (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                                (λ x y l → l)
                                (dep-cases (λ _ → ι-order-preserving ν)
                                           (λ _ → ι-order-preserving μ))
ι-order-preserving (Mul ν μ) = pair-fun-is-order-preserving
                                (Δ ν)
                                (Κ ν)
                                (λ _ → Δ μ)
                                (λ _ → Κ μ)
                                (ι {ν})
                                (λ _ → ι {μ})
                                (ι-order-preserving ν)
                                (λ _ → ι-order-preserving μ)
ι-order-preserving (Sum1 ν) = ∑↑-is-order-preserving
                                (Δ ∘ ν)
                                (Κ ∘ ν)
                                (λ n → ι {ν n})
                                (λ i → ι-order-preserving (ν i))

ι-order-reflecting One       = λ x y l → l
ι-order-reflecting (Add ν μ) = pair-fun-is-order-reflecting
                                𝟚ᵒ
                                𝟚ᵒ
                                (cases (λ _ → Δ ν) (λ _ → Δ μ))
                                (cases (λ _ → Κ ν) (λ _ → Κ μ))
                                id
                                (dep-cases (λ _ → ι {ν}) (λ _ → ι {μ}))
                                (λ x y l → l)
                                id-is-embedding
                                (dep-cases (λ _ → ι-order-reflecting ν)
                                           (λ _ → ι-order-reflecting μ))
ι-order-reflecting (Mul ν μ) = pair-fun-is-order-reflecting
                                (Δ ν)
                                (Κ ν)
                                (λ _ → Δ μ)
                                (λ _ → Κ μ)
                                (ι {ν})
                                (λ _ → ι {μ})
                                (ι-order-reflecting ν)
                                (ι-embedding ν)
                                (λ _ → ι-order-reflecting μ)
ι-order-reflecting (Sum1 ν)  = ∑↑-is-order-reflecting
                                (Δ ∘ ν)
                                (Κ ∘ ν)
                                (λ n → ι {ν n})
                                (λ i → ι-order-reflecting (ν i))
\end{code}

As discussed in the module Ordinals, propositional extensionality in
the following construction is not strictly needed but makes our life
much easier (given the mathematics we have already developed).

\begin{code}

Κ-inf-compact pe One       = 𝟙ᵒ-inf-compact
Κ-inf-compact pe (Add ν μ) = ∑-inf-compact pe
                               𝟚ᵒ
                               (cases (λ _ → Κ ν) (λ _ → Κ μ))
                               𝟚ᵒ-inf-compact
                               (dep-cases (λ _ → Κ-inf-compact pe ν)
                                          (λ _ → Κ-inf-compact pe μ))
Κ-inf-compact pe (Mul ν μ) = ∑-inf-compact pe
                               (Κ ν)
                               (λ _ → Κ μ)
                               (Κ-inf-compact pe ν)
                               (λ _ → Κ-inf-compact pe μ)
Κ-inf-compact pe (Sum1 ν) = ∑₁-inf-compact
                               pe
                               (Κ ∘ ν)
                               (λ i → Κ-inf-compact pe (ν i))
\end{code}

Added 31 July 2018:

\begin{code}

Δ-retract-of-ℕ One       = (λ _ → *) , (λ _ → 0) , 𝟙-is-prop *
Δ-retract-of-ℕ (Add ν μ) = Σ-retract-of-ℕ
                             retract-𝟙+𝟙-of-ℕ
                             (dep-cases (λ _ → Δ-retract-of-ℕ ν)
                                        (λ _ → Δ-retract-of-ℕ μ))
Δ-retract-of-ℕ (Mul ν μ) = Σ-retract-of-ℕ
                             (Δ-retract-of-ℕ ν)
                             (λ _ → Δ-retract-of-ℕ μ)
Δ-retract-of-ℕ (Sum1 ν) = Σ₁-ℕ-retract (λ i → Δ-retract-of-ℕ (ν i))

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
brouwer-to-oe (L ν) = Sum1 (λ i → brouwer-to-oe (ν i))

\end{code}

The following is a relatively "small" example: an upper bound of the
ordinal ε₀ (because sums dominate suprema):

\begin{code}

ε₀-upper-bound = Κ (brouwer-to-oe B-ε₀)

compact∙-ε₀-ub = Κ-compact∙ (brouwer-to-oe B-ε₀)

\end{code}

We can go much higher using the work of and Setzer, Hancock and
others.
