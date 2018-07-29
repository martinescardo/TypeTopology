Martin Escardo, 2012, 2018.

Searchable ordinals, discrete ordinals and their relationships.

Begun December 2012, based on earlier work, circa 2010.

Most of the work has been done later, and coded in July 2018 after a
long pause to understand univalent foundations, which is what we use
in this development.

Here an ordinal is a type equipped with a well order. This is a
relation < which is assumed to be

  * subsingleton valued,
  * well founded,
  * transitive, and
  * extensional (any two elements with the same lower set are equal).

The extensionality axiom implies that the underlying type of an
ordinal is a set (or satisfies the K axiom), which is proved in the
module OrdinalNotions. This seems to be a new observation about the
univalent notion of ordinal.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module SearchableOrdinals (fe : ∀ U V → funext U V) where

\end{code}

We work with ordinal encodings, or ordinal expressions, that are
slightly different from the traditional Brouwer ordinal trees, which
we also consider towards the end of his article.

\begin{code}

data OE : U₀ ̇ where
 One  : OE
 Add  : OE → OE → OE
 Mul  : OE → OE → OE
 Sum1 : (ℕ → OE) → OE

\end{code}

We consider two mappings from these ordinal expressions to actual
ordinals as discussed above.

  * Δ : OE → Ordᵀ
  * Κ : OE → Ordᵀ

Here Ordᵀ is the type of ordinals that have a top element (which, in
constructive mathematics, are not in general successor
ordinals). Technically, the top element allows us to prove the closure
of ordinals under ordinal-indexed sums, paying a crucial role in the
proof of extensionality of the sum. But also the top element is
equally crucial for searchability or compactness purposes, dicussed
below.

  * The ordinals in the image of Δ are discrete (have decidable equality).

  * Those in the image of Κ are compact (are searchable).

    Moreover, they are retracts of the Cantor type (ℕ → 𝟚) of binary
    sequences, and hence are totally separated, which means that the
    functions into 𝟚 separate the points.

    And not only the Κ ordinals are searchable, they are also
    inf-searchable, which means that any detachable subset has an
    infimum, which belongs to the subset iff and only if the subset is
    non-empty (with non-emptiness expressed by a doble negation).

The Δ and Κ interpretation of one, addition and multiplication are as
expected. They differ only in the interpretation of Sum1.

   * In the discrete case, Sum1 is interpreted as simply the sum plus
     one (written ∑₁).

   * In the compact case, Sum1 is interpreted as the sum with an added
     non-isolated point (written ∑¹). In is this that makes the
     searchability of the compact ordinals possible. The searchability
     of the discrete ordinals is a contructive taboo.

Additionally, we kave a map δκ from the Δ-ordinals to the Κ-ordinals,
which is

  * an embedding (has subsingleton fibers),
  * is dense (the complement of its image is empty),
  * order preserving and reflecting.

Lastly, we have a mapping from our ordinal trees to Brouwer trees that
allows us to use other peoples constructions to construct very "large"
searchable ordinals. As a trivial example, we show how to map a
Brouwer code of ε₀ to a searchable ordinal that dominates ε₀.

After a brief pause for importing the necessary definitions, we state
the theorems and constructions to be performed here:

\begin{code}

open import Ordinals fe
open import SearchableTypes
open import TotallySeparated
open import UF-Retracts
open import SquashedCantor fe hiding (Κ)
open import DiscreteAndSeparated
open import UF-Embedding
open import UF-Subsingletons
open import InfSearchable
open import OrdinalCodes
open import SquashedSum fe
open import UF-SetExamples

Κ                    : OE → Ordᵀ
Κ-searchable         : (α : OE) → searchable ⟪ Κ α ⟫
Κ-totally-separated  : (α : OE) → totally-separated ⟪ Κ α ⟫
Κ-Cantor-retract     : (α : OE) → retract  ⟪ Κ α ⟫ of (ℕ → 𝟚)

Δ                    : OE → Ordᵀ
Δ-discrete           : (α : OE) → discrete ⟪ Δ α ⟫

δκ                   : (α : OE) → ⟪ Δ α ⟫ → ⟪ Κ α ⟫
δκ-dense             : (α : OE) → is-dense (δκ α)
δκ-embedding         : (α : OE) → is-embedding (δκ α)
δκ-order-preserving  : (α : OE) (x y : ⟪ Δ α ⟫)
                          → x ≺⟪ Δ α ⟫ y
                          → δκ α x ≺⟪ Κ α ⟫ δκ α y
δκ-order-reflecting  : (α : OE) (x y : ⟪ Δ α ⟫)
                          → δκ α x ≺⟪ Κ α ⟫ δκ α y
                          → x ≺⟪ Δ α ⟫ y

Κ-inf-searchable     : propext U₀
                       → (α : OE) → inf-searchable (λ x y → x ≼⟪ Κ α ⟫ y)

brouwer-to-oe        : B → OE
ε₀-upper-bound       : Ordᵀ
searchable-ε₀-ub     : searchable ⟪ ε₀-upper-bound ⟫
\end{code}

The empty ordinal is excluded because it is not searchable. It is
merely exhaustible or omniscient (see the module Searchable for a
partial discussion of this). The reason why including the empty
ordinal causes insurmountable problems is discussed in research papers.

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

The complication of the following proof in the case for addition is
that the ordinal 𝟚ᵒ has underlying set 𝟙+𝟙 rather than 𝟚, and that
(hence) we defined the ordinal +ᵒ as a sum indexed by 𝟙+𝟙 rather than
as a co-product. This saved lots of code elsewhere, but adds labour
here (and in some helper lemmas/constructions that we added in other
modules for this purpose). Notice that +' is the sum indexed by 𝟚,
defined in the module SpartanMLTT. The bulk of the work for the
following construction is performed in the module SquashedCantor.

\begin{code}

Κ-Cantor-retract One = (λ _ → *) , (λ _ → λ n → ₀) , (λ x → 𝟙-is-prop * x)
Κ-Cantor-retract (Add α β) = retracts-compose d e
 where
  a : retract (Cantor +' Cantor) of (Cantor + Cantor)
  a = +'-retract-of-+
  b : retract (Cantor +' Cantor) of Cantor
  b = retracts-compose +-Cantor-retract a
  c : retract ⟪ Κ α ⟫ +' ⟪ Κ β ⟫ of (Cantor +' Cantor)
  c = +'-retract (Κ-Cantor-retract α) (Κ-Cantor-retract β)
  d : retract ⟪ Κ α ⟫ +' ⟪ Κ β ⟫ of Cantor
  d = retracts-compose b c
  e : retract ⟪ Κ α +ᵒ Κ β ⟫ of (⟪ Κ α ⟫ +' ⟪ Κ β ⟫)
  e = transport (λ - → retract ⟪ Κ α +ᵒ Κ β ⟫ of (Σ -)) (dfunext (fe U₀ U₁) l) h
   where
    f : 𝟚 → 𝟙 + 𝟙
    f = pr₁ retract-𝟙+𝟙-of-𝟚
    h : retract ⟪ Κ α +ᵒ Κ β ⟫ of (Σ \(i : 𝟚) → ⟪ cases (λ _ → Κ α) (λ _ → Κ β) (f i) ⟫)
    h = Σ-reindex-retract f (pr₂ retract-𝟙+𝟙-of-𝟚)
    l : (i : 𝟚) → ⟪ cases (λ _ → Κ α) (λ _ → Κ β) (f i) ⟫
                ≡ 𝟚-cases ⟪ Κ α ⟫ ⟪ Κ β ⟫ i
    l ₀ = refl
    l ₁ = refl
Κ-Cantor-retract (Mul α β) = retracts-compose a b
 where
  a : retract (Cantor × Cantor) of Cantor
  a = pair-seq-retract fe₀
  b : retract ⟪ Κ α ⟫ × ⟪ Κ β ⟫ of (Cantor × Cantor)
  b = ×-retract (Κ-Cantor-retract α) (Κ-Cantor-retract β)
Κ-Cantor-retract (Sum1 α)  = squashed-Cantor-retract (λ n → ⟪ Κ (α n) ⟫) (Κ-Cantor-retract ∘ α)

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
sets. Moreover, there is a function maps the underlying set of the
discrete version to the underlying set of the above version, with many
interesting properties, formulated above and proved below.

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
order preserving and reflecting (28 July 2018). Most of the work to
perform these constructions and prove their properties is developed in
the imported modules.

\begin{code}

δκ One = id
δκ (Add α β) = pair-fun id (dep-cases (λ _ → δκ α) (λ _ → δκ β))
δκ (Mul α β) = pair-fun (δκ α) (λ _ → δκ β)
δκ (Sum1 α) = ∑↑ (λ n → Δ (α n)) (λ n → Κ (α n)) (δκ ∘ α)

δκ-dense One = id-is-dense
δκ-dense (Add α β) =
 pair-fun-dense
  id
  (dep-cases (λ _ → δκ α) (λ _ → δκ β))
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
  (δκ ∘ α)
  (δκ-dense ∘ α)

δκ-embedding One = id-is-embedding
δκ-embedding (Add α β) =
 pair-fun-embedding
  id
  (dep-cases (λ _ → δκ α) (λ _ → δκ β))
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
  (δκ ∘ α)
  (δκ-embedding ∘ α)

δκ-order-preserving One = λ x y l → l
δκ-order-preserving (Add α β) =
 pair-fun-order-preserving
   𝟚ᵒ
   𝟚ᵒ
   (cases (λ _ → Δ α) (λ _ → Δ β))
   (cases (λ _ → Κ α) (λ _ → Κ β))
   id
   (dep-cases (λ _ → δκ α) (λ _ → δκ β))
   (λ x y l → l)
   (dep-cases (λ _ → δκ-order-preserving α) λ _ → δκ-order-preserving β)
δκ-order-preserving (Mul α β) =
 pair-fun-order-preserving
  (Δ α)
  (Κ α)
  (λ _ → Δ β)
  (λ _ → Κ β)
  (δκ α)
  (λ _ → δκ β)
  (δκ-order-preserving α)
  (λ _ → δκ-order-preserving β)
δκ-order-preserving (Sum1 α) =
 ∑↑-order-preserving
   (Δ ∘ α)
   (Κ ∘ α)
   (δκ ∘ α)
   (δκ-order-preserving ∘ α)

δκ-order-reflecting One = λ x y l → l
δκ-order-reflecting (Add α β) =
 pair-fun-order-reflecting
   𝟚ᵒ
   𝟚ᵒ
   (cases (λ _ → Δ α) (λ _ → Δ β))
   (cases (λ _ → Κ α) (λ _ → Κ β))
   id
   (dep-cases (λ _ → δκ α) (λ _ → δκ β))
   (λ x y l → l)
   id-is-embedding
   (dep-cases (λ _ → δκ-order-reflecting α) λ _ → δκ-order-reflecting β)
δκ-order-reflecting (Mul α β) =
 pair-fun-order-reflecting
  (Δ α)
  (Κ α)
  (λ _ → Δ β)
  (λ _ → Κ β)
  (δκ α)
  (λ _ → δκ β)
  (δκ-order-reflecting α)
  (δκ-embedding α)
  (λ _ → δκ-order-reflecting β)
δκ-order-reflecting (Sum1 α)  =
 ∑↑-order-reflecting
   (Δ ∘ α)
   (Κ ∘ α)
   (δκ ∘ α)
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

{- TODO
Δ-countable : (α : OE) → (⟪ Δ α ⟫ ≃ ℕ) + Σ \(n : ℕ) → ⟪ Δ α ⟫ ≃ Fin n
Δ-countable = {!!}

-- Hence the searchability of any infinite discrete ordinal is a
constructive taboo.

-}

\end{code}

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

We can go much higher using the work of many people, including Hancock
and Setzer.
