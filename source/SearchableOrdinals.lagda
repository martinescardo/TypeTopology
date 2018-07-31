Martin Escardo, 2012, 2018.

Searchable ordinals, discrete ordinals and their relationships.

Begun December 2012, based on earlier work, circa 2010.

Most of the work has been done later, and coded in July 2018 after a
long pause to understand univalent foundations, which is what we use
in this development, and to develop the mathematica basis for this in
other modules.

Here an ordinal is a type equipped with a well order, namely
relation < which is

  * subsingleton valued,
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

module SearchableOrdinals (fe : ∀ U V → funext U V) where

\end{code}

We work with ordinal encodings, or ordinal expressions, that are
slightly different from the traditional Brouwer ordinal trees, which
we also consider towards the end of this article.

\begin{code}

data OE : U₀ ̇ where
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
crucial for searchability or compactness purposes, dicussed below.

  * The ordinals in the image of Δ are discrete (have decidable
    equality) and have countable underlying sets, which are in fact
    retracts of ℕ.

  * Those in the image of Κ are compact (they are searchable).

    Moreover, they are retracts of the Cantor type (ℕ → 𝟚) of binary
    sequences, and hence are totally separated, which means that the
    functions into 𝟚 separate the points.

    And not only the Κ ordinals are searchable, they are also
    inf-searchable, which means that any detachable subset has an
    infimum, which belongs to the subset iff and only if the subset is
    non-empty (with non-emptiness expressed by a double negation).

    The discrete ordinals, being retracts of ℕ, cannot be retracts of
    the Cantor space. This is because the Cantor space is potentially
    searchable, in the presence of Brouwerian axioms (which we are not
    assuming), and searchability is inherited by retracts, and the
    searchability of the infinite discrete ordinals is equivalent to
    Bishop's LPO (limited principle of omnscient), which is not
    provable in any variety of constructive mathematics.

The Δ and Κ interpretation of One, Add and Mul are as expected. They
differ only in the interpretation of Sum1.

   * In the discrete case, Sum1 is interpreted as simply the countable
     sum plus the ordinal 𝟙 (written ∑₁).

   * In the compact case, Sum1 is interpreted as the sum with an added
     non-isolated top point (written ∑¹). It is this that makes the
     searchability of the compact ordinals possible. The searchability
     of the discrete ordinals is a contructive taboo.

Additionally, we kave a map δκ from the Δ-ordinals to the Κ-ordinals,
which is

  * an embedding (has subsingleton fibers),
  * dense (the complement of its image is empty),
  * order preserving and reflecting.

Lastly, we have a mapping from our ordinal trees to Brouwer trees that
allows us to use other people's constructions to get very "large"
searchable ordinals. As a trivial example, we show how to map a
Brouwer code of ε₀ to a searchable ordinal that dominates ε₀.

The bulk of the work to perform these constructions and prove their
properties is developed in the imported modules.

After a brief pause for importing the necessary definitions, we state
the theorems and constructions to be performed here:

\begin{code}

open import Ordinals fe
open import OrdinalsClosure fe
open import OrdinalCodes
open import SearchableTypes
open import InfSearchable
open import TotallySeparated
open import SquashedSum fe
open import SquashedCantor fe hiding (Κ)
open import DiscreteAndSeparated
open import UF-Subsingletons
open import UF-Retracts
open import UF-Embedding
open import UF-SetExamples

\end{code}

In the following, ⟪ τ ⟫ denotes the underlying set of an ordinal τ, and
_≺⟪ τ ⟫_ denotes its underlying order.

\begin{code}

Κ                    : OE → Ordᵀ
Κ-searchable         : (α : OE) → searchable ⟪ Κ α ⟫
Κ-Cantor-retract     : (α : OE) → retract ⟪ Κ α ⟫ of (ℕ → 𝟚)
Κ-totally-separated  : (α : OE) → totally-separated ⟪ Κ α ⟫

Δ                    : OE → Ordᵀ
Δ-discrete           : (α : OE) → discrete ⟪ Δ α ⟫
Δ-retract-of-ℕ       : (α : OE) → retract ⟪ Δ α ⟫ of ℕ

δκ                   : {α : OE} → ⟪ Δ α ⟫ → ⟪ Κ α ⟫
δκ-dense             : (α : OE) → is-dense (δκ {α})
δκ-embedding         : (α : OE) → is-embedding (δκ {α})

δκ-order-preserving  : (α : OE) (x y : ⟪ Δ α ⟫)
                          →    x ≺⟪ Δ α ⟫    y
                          → δκ x ≺⟪ Κ α ⟫ δκ y

δκ-order-reflecting  : (α : OE) (x y : ⟪ Δ α ⟫)
                          → δκ x ≺⟪ Κ α ⟫ δκ y
                          →    x ≺⟪ Δ α ⟫    y

Κ-inf-searchable     : propext U₀ → (α : OE) → inf-searchable (λ x y → x ≼⟪ Κ α ⟫ y)

brouwer-to-oe        : B → OE
ε₀-upper-bound       : Ordᵀ
searchable-ε₀-ub     : searchable ⟪ ε₀-upper-bound ⟫

\end{code}

The empty ordinal is excluded because it is not searchable. It is
merely exhaustible or omniscient (see the module Searchable for a
partial discussion of this). The reason why sometimes including the
empty ordinal causes insurmountable problems regarding closure under
searchability is discussed in research papers and in other modules.

The interpretation function is the following, with values on topped
ordinals, where an ordinal is a type equipped with a
subsingleton-valued, well-founded, transitive and extensional relation
(and such a type is automatically a set). "Topped" means that there is
a top element in the order

This version of the function is from 1st July 2018 (the original
version considered only the underlying set of the ordinal and didn't
construct the order as this was work in progress):

\begin{code}

Κ One  = 𝟙ᵒ
Κ (Add α β) = Κ α +ᵒ Κ β
Κ (Mul α β) = Κ α ×ᵒ  Κ β
Κ (Sum1 α) = ∑¹ \(i : ℕ) → Κ(α i)

\end{code}

The underlying sets  of such ordinals are searchable:

\begin{code}

Κ-searchable One = 𝟙-searchable
Κ-searchable (Add α β) =
 Σ-searchable
  𝟙+𝟙-searchable
  (dep-cases (λ _ → Κ-searchable α) (λ _ → Κ-searchable β))
Κ-searchable (Mul α β) = Σ-searchable (Κ-searchable α) (λ _ → Κ-searchable β)
Κ-searchable (Sum1 α) = Σ¹-searchable (λ n → ⟪ Κ (α n) ⟫) (Κ-searchable ∘ α)

\end{code}

Completed 20th July 2018:

The searchable ordinals are retracts of the Cantor type (ℕ → 𝟚).


\begin{code}

Κ-Cantor-retract One = (λ _ → *) , (λ _ → λ n → ₀) , 𝟙-is-prop *
Κ-Cantor-retract (Add α β) = +-retract-of-Cantor (Κ α) (Κ β) (Κ-Cantor-retract α) (Κ-Cantor-retract β)
Κ-Cantor-retract (Mul α β) = ×-retract-of-Cantor (Κ α) (Κ β) (Κ-Cantor-retract α) (Κ-Cantor-retract β)
Κ-Cantor-retract (Sum1 α)  = Σ¹-Cantor-retract (λ n → ⟪ Κ (α n) ⟫) (Κ-Cantor-retract ∘ α)

\end{code}

And hence they are totally separated:

\begin{code}

Κ-totally-separated α = retract-totally-separated
                          (Κ-Cantor-retract α)
                          (Cantor-totally-separated fe₀)
\end{code}

Without total separatedness (enough functions into the type 𝟚 of
booleans), searchability wouldn't be an interesting property. It is
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

Δ One = 𝟙ᵒ
Δ (Add α β) = Δ α +ᵒ Δ β
Δ (Mul α β) = Δ α ×ᵒ  Δ β
Δ (Sum1 α) = ∑₁ \(i : ℕ) → Δ(α i)

Δ-discrete One  = 𝟙-discrete
Δ-discrete (Add α β) =
 Σ-discrete
  (+discrete 𝟙-discrete 𝟙-discrete)
  (dep-cases (λ _ → Δ-discrete α) (λ _ → Δ-discrete β))
Δ-discrete (Mul α β) = Σ-discrete (Δ-discrete α) (λ _ → Δ-discrete β)
Δ-discrete (Sum1 α) = Σ₁-discrete (λ n → ⟪ Δ (α n) ⟫) (Δ-discrete ∘ α)

\end{code}

Completed 27 July 2018. There is a dense embedding δκ of the discrete
ordinals into the searchable ordinals, where density means that the
complement of the image of the embedding is empty. Moreover, it is
order preserving and reflecting (28 July 2018).

\begin{code}

δκ {One} = id
δκ {Add α β} = pair-fun id (dep-cases (λ _ → δκ {α}) (λ _ → δκ {β}))
δκ {Mul α β} = pair-fun (δκ {α}) (λ _ → δκ {β})
δκ {Sum1 α} = ∑↑ (λ n → Δ (α n)) (λ n → Κ (α n)) (λ n → δκ {α n})

δκ-dense One = id-is-dense
δκ-dense (Add α β) =
 pair-fun-dense
  id
  (dep-cases (λ _ → δκ {α}) (λ _ → δκ {β}))
  id-is-dense
  (dep-cases (λ _ → δκ-dense α) (λ _ → δκ-dense β))
δκ-dense (Mul α β) =
 pair-fun-dense _ _
  (δκ-dense α)
  (λ _ → δκ-dense β)
δκ-dense (Sum1 α) =
 Σ↑-dense
  (λ n → ⟪ Δ (α n) ⟫)
  (λ n → ⟪ Κ (α n) ⟫)
  (λ n → δκ {α n})
  (δκ-dense ∘ α)

δκ-embedding One = id-is-embedding
δκ-embedding (Add α β) =
 pair-fun-embedding
  id
  (dep-cases (λ _ → δκ {α}) (λ _ → δκ {β}))
  id-is-embedding
  (dep-cases (λ _ → δκ-embedding α) (λ _ → δκ-embedding β))
δκ-embedding (Mul α β) =
 pair-fun-embedding _ _
  (δκ-embedding α)
  (λ _ → δκ-embedding β)
δκ-embedding (Sum1 α) =
 Σ↑-embedding
  (λ n → ⟪ Δ (α n) ⟫)
  (λ n → ⟪ Κ (α n) ⟫)
  (λ n → δκ {α n})
  (δκ-embedding ∘ α)

δκ-order-preserving One = λ x y l → l
δκ-order-preserving (Add α β) =
 pair-fun-order-preserving
   𝟚ᵒ
   𝟚ᵒ
   (cases (λ _ → Δ α) (λ _ → Δ β))
   (cases (λ _ → Κ α) (λ _ → Κ β))
   id
   (dep-cases (λ _ → δκ {α}) (λ _ → δκ {β}))
   (λ x y l → l)
   (dep-cases (λ _ → δκ-order-preserving α) λ _ → δκ-order-preserving β)
δκ-order-preserving (Mul α β) =
 pair-fun-order-preserving
  (Δ α)
  (Κ α)
  (λ _ → Δ β)
  (λ _ → Κ β)
  (δκ {α})
  (λ _ → δκ {β})
  (δκ-order-preserving α)
  (λ _ → δκ-order-preserving β)
δκ-order-preserving (Sum1 α) =
 ∑↑-order-preserving
   (Δ ∘ α)
   (Κ ∘ α)
   (λ n → δκ {α n})
   (δκ-order-preserving ∘ α)

δκ-order-reflecting One = λ x y l → l
δκ-order-reflecting (Add α β) =
 pair-fun-order-reflecting
   𝟚ᵒ
   𝟚ᵒ
   (cases (λ _ → Δ α) (λ _ → Δ β))
   (cases (λ _ → Κ α) (λ _ → Κ β))
   id
   (dep-cases (λ _ → δκ {α}) (λ _ → δκ {β}))
   (λ x y l → l)
   id-is-embedding
   (dep-cases (λ _ → δκ-order-reflecting α) λ _ → δκ-order-reflecting β)
δκ-order-reflecting (Mul α β) =
 pair-fun-order-reflecting
  (Δ α)
  (Κ α)
  (λ _ → Δ β)
  (λ _ → Κ β)
  (δκ {α})
  (λ _ → δκ {β})
  (δκ-order-reflecting α)
  (δκ-embedding α)
  (λ _ → δκ-order-reflecting β)
δκ-order-reflecting (Sum1 α)  =
 ∑↑-order-reflecting
   (Δ ∘ α)
   (Κ ∘ α)
   (λ n → δκ {α n})
   (δκ-order-reflecting ∘ α)

\end{code}

As discussed in the module Ordinals, propositional extensionality in
the following construction is not strictly needed but makes our life
much easier (given the mathematics we have already developed).

\begin{code}

Κ-inf-searchable pe One = 𝟙ᵒ-inf-searchable
Κ-inf-searchable pe (Add α β) =
 ∑-inf-searchable pe
  𝟚ᵒ
  (cases (λ _ → Κ α) (λ _ → Κ β))
  𝟚ᵒ-inf-searchable
  (dep-cases
    (λ _ → Κ-inf-searchable pe α)
    (λ _ → Κ-inf-searchable pe β))
Κ-inf-searchable pe (Mul α β) =
 ∑-inf-searchable pe
  (Κ α)
  (λ _ → Κ β)
  (Κ-inf-searchable pe α)
  (λ _ → Κ-inf-searchable pe β)
Κ-inf-searchable pe (Sum1 α) =
 ∑₁-inf-searchable
  pe
  (Κ ∘ α)
  (Κ-inf-searchable pe ∘ α)

\end{code}

Added 31 July 2018:

\begin{code}

Δ-retract-of-ℕ One = (λ _ → *) , (λ _ → 0) , 𝟙-is-prop *
Δ-retract-of-ℕ (Add α β) =
 Σ-retract-of-ℕ
  retract-𝟙+𝟙-of-ℕ
  (dep-cases (λ _ → Δ-retract-of-ℕ α) (λ _ → Δ-retract-of-ℕ β))
Δ-retract-of-ℕ (Mul α β) =
 Σ-retract-of-ℕ
 (Δ-retract-of-ℕ α)
 (λ _ → Δ-retract-of-ℕ β)
Δ-retract-of-ℕ (Sum1 α) = Σ₁-ℕ-retract (Δ-retract-of-ℕ ∘ α)

\end{code}

NB. We could have proved that the Δ-ordinals are discrete using the
above, as discrete types are closed under retracts.

Hence the searchability of any infinite discrete ordinal is a
constructive taboo, logically equivalent to Bishop's LPO.

Brouwer ordinal codes can be mapped to searchable ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal, because sums dominate suprema.

\begin{code}

brouwer-to-oe    Z  = One
brouwer-to-oe (S α) = Add One (brouwer-to-oe α)
brouwer-to-oe (L α) = Sum1(λ i → brouwer-to-oe(α i))

\end{code}

The following is a relatively "small" example: an upper bound of the
ordinal ε₀ (because sums dominate suprema):

\begin{code}

ε₀-upper-bound = Κ(brouwer-to-oe B-ε₀)

searchable-ε₀-ub = Κ-searchable(brouwer-to-oe B-ε₀)

\end{code}

We can go much higher using the work of and Setzer, Hancock and
others.
