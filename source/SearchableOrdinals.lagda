Martin Escardo, December 2012, based on earlier work, circa 2010.

Searchable ordinals via squashed sums (without using the Cantor space).

We can define plenty of searchable sets by transfinitely iterating
squashed sums. These are countable sums with an added limit point at
infinity (see the module SquashedSum).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module SearchableOrdinals (fe : ∀ U V → funext U V) where

open import SpartanMLTT
open import SquashedSum fe
open import SearchableTypes
open import TotallySeparated
open import UF-Retracts
open import UF-Embedding
open import DiscreteAndSeparated
open import UF-SetExamples
open import UF-Subsingletons
open import SquashedCantor fe
open import UF-Retracts-FunExt

\end{code}

We use ordinal encodings, or ordinal expressions, that are slightly
different from the traditional "Brouwer ordinals".

\begin{code}

data OE : U₀ ̇ where
 One  : OE
 Add  : OE → OE → OE
 Mul  : OE → OE → OE
 Sum1 : (ℕ → OE) → OE

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

open import Ordinals fe

ord : OE → Ordᵀ
ord      One  = 𝟙º
ord (Add α β) = ord α +º ord β
ord (Mul α β) = ord α ×º  ord β
ord (Sum1 α)  = ∑¹ \(i : ℕ) → ord(α i)

\end{code}

The underlying sets  of such ordinals are searchable:

\begin{code}

sord : (α : OE) → searchable ⟪ ord α ⟫
sord       One = 𝟙-searchable
sord (Add α β) = Σ-searchable
                   𝟙+𝟙-searchable
                   (dep-cases (λ _ → sord α) (λ _ → sord β))
sord (Mul α β) = Σ-searchable (sord α) (λ _ → sord β)
sord (Sum1 α)  = Σ¹-searchable (λ n → ⟪ ord (α n) ⟫) (sord ∘ α)

\end{code}

Completed 20th July 2018:
The searchable ordinals are retracts of the Cantor type (ℕ → 𝟚).

The complication of the following proof in the case for addition is
that the ordinal 𝟚º has underlying set 𝟙+𝟙 rather than 𝟚, and that
(hence) we defined the ordinal +º as a sum indexed by 𝟙+𝟙 rather than
as a co-product. This saved lots of code elsewhere, but adds labour
here (and in some helper lemmas/constructions that we added in other
modules for this purpose). Notice that +' is the sum indexed by 𝟚,
defined in the module SpartanMLTT.

\begin{code}

cord : (α : OE) → retract  ⟪ ord α ⟫ of Cantor
cord       One = (λ _ → *) , (λ _ → λ n → ₀) , (λ x → 𝟙-is-prop * x)
cord (Add α β) = retracts-compose d e
 where
  a : retract (Cantor +' Cantor) of (Cantor + Cantor)
  a = +'-retract-of-+
  b : retract (Cantor +' Cantor) of Cantor
  b = retracts-compose +-Cantor-retract a
  c : retract ⟪ ord α ⟫ +' ⟪ ord β ⟫ of (Cantor +' Cantor)
  c = +'-retract (cord α) (cord β)
  d : retract ⟪ ord α ⟫ +' ⟪ ord β ⟫ of Cantor
  d = retracts-compose b c
  e : retract ⟪ ord α +º ord β ⟫ of (⟪ ord α ⟫ +' ⟪ ord β ⟫)
  e = transport (λ - → retract ⟪ ord α +º ord β ⟫ of (Σ -)) (dfunext (fe U₀ (U₀ ′)) l) h
   where
    f : 𝟚 → 𝟙 + 𝟙
    f = 𝟚-cases (inl *) (inr *)
    g : 𝟙 + 𝟙 → 𝟚
    g = cases (λ x → ₀) (λ x → ₁)
    fg : (x : 𝟙 + 𝟙) → f (g x) ≡ x
    fg (inl *) = refl
    fg (inr *) = refl
    h : retract ⟪ ord α +º ord β ⟫ of (Σ \(i : 𝟚) → ⟪ cases (λ _ → ord α) (λ _ → ord β) (f i) ⟫)
    h = Σ-reindex-retract f (g , fg)
    l : (i : 𝟚) → ⟪ cases (λ _ → ord α) (λ _ → ord β) (f i) ⟫
                ≡ 𝟚-cases ⟪ ord α ⟫ ⟪ ord β ⟫ i
    l ₀ = refl
    l ₁ = refl
cord (Mul α β) = retracts-compose a b
 where
  a : retract (Cantor × Cantor) of Cantor
  a = pair-seq-retract fe₀
  b : retract ⟪ ord α ⟫ × ⟪ ord β ⟫ of (Cantor × Cantor)
  b = ×-retract (cord α) (cord β)
cord (Sum1 α)  = squashed-Cantor-retract (λ n → ⟪ ord (α n) ⟫) (cord ∘ α)

\end{code}

And hence they are totally separated:

\begin{code}

tsord : (α : OE) → totally-separated ⟪ ord α ⟫
tsord α = retract-totally-separated (cord α) (Cantor-totally-separated fe₀)

\end{code}

Without total separatedness (enough functions into the type 𝟚 of
booleans), searchability wouldn't be an interesting property. It is
not possible to prove total separated directly, because this property
is not closed under Σ, which is used to define +º, ×º and Σ₁, as shown
in the module FailureOfTotalSeparatedness.

Classically, the squashed sum is the ordinal sum plus 1, and we have a
semantics with this interpretation, which gives ordinals with discrete
underlying sets. Moreover, there is a function maps the underlying set
of the discrete version to the underlying set of the above version.

\begin{code}

ord' : OE → Ordᵀ
ord'        One = 𝟙º
ord' (Add α β) = ord' α +º ord' β
ord' (Mul α β) = ord' α ×º  ord' β
ord' (Sum1 α)  = ∑₁ \(i : ℕ) → ord'(α i)

dord' : (α : OE) → discrete ⟪ ord' α ⟫
dord'      One  = 𝟙-discrete
dord' (Add α β) = Σ-discrete
                    (+discrete 𝟙-discrete 𝟙-discrete)
                    (dep-cases (λ _ → dord' α) (λ _ → dord' β))
dord' (Mul α β) = Σ-discrete (dord' α) (λ _ → dord' β)
dord' (Sum1 α)  = Σ₁-discrete (λ n → ⟪ ord' (α n) ⟫) (dord' ∘ α)

\end{code}

Completed 27 July 2018. There is a dense embedding of the discrete
ordinals into the searchable ordinals, where density means that the
complement of the image of the embedding is empty.

"eds" stands for "embedding of the discrete ordinals into the
searchable ordinals".

\begin{code}

eds           : (α : OE) → ⟪ ord' α ⟫ → ⟪ ord α ⟫
eds-dense     : (α : OE) → is-dense (eds α)
eds-embedding : (α : OE) → is-embedding (eds α)

eds One = id
eds (Add α β) = pair-fun id (dep-cases (λ _ → eds α) (λ _ → eds β))
eds (Mul α β) = pair-fun (eds α) (λ _ → eds β)
eds (Sum1 α) = Σ↑ (λ n → ⟪ ord' (α n) ⟫) (λ n → ⟪ ord (α n) ⟫) (eds ∘ α)

eds-dense One = id-is-dense
eds-dense (Add α β) = pair-fun-dense
                       id
                       (dep-cases (λ _ → eds α) (λ _ → eds β))
                       id-is-dense
                       (dep-cases (λ _ → eds-dense α) (λ _ → eds-dense β))
eds-dense (Mul α β) = pair-fun-dense _ _ (eds-dense α) (λ _ → eds-dense β)
eds-dense (Sum1 α) = Σ↑-dense
                      (λ n → ⟪ ord' (α n) ⟫)
                      (λ n → ⟪ ord (α n) ⟫)
                      (eds ∘ α)
                      (eds-dense ∘ α)

eds-embedding One = id-is-embedding
eds-embedding (Add α β) = pair-fun-embedding
                           id
                           (dep-cases (λ _ → eds α) (λ _ → eds β))
                           id-is-embedding
                           (dep-cases (λ _ → eds-embedding α) (λ _ → eds-embedding β))
eds-embedding (Mul α β) = pair-fun-embedding _ _ (eds-embedding α) (λ _ → eds-embedding β)
eds-embedding (Sum1 α) = Σ↑-embedding
                          (λ n → ⟪ ord' (α n) ⟫)
                          (λ n → ⟪ ord (α n) ⟫)
                          (eds ∘ α)
                          (eds-embedding ∘ α)

{- TODO: The embedding preserves and reflects order.
eds-preserves-order : (α : OE) (x y : ⟪ ord' α ⟫)
               → x ≺⟪ ord' α ⟫ y
               → (eds α x) ≺⟪ ord α ⟫ (eds α y)
eds-preserves-order = {!!}

eds-reflects-order : (α : OE) (x y : ⟪ ord' α ⟫)
               → (eds α x) ≺⟪ ord α ⟫ (eds α y)
               → x ≺⟪ ord' α ⟫ y
eds-reflects-order = {!!}
-}

{- TODO: every decidable inhabited subset has a least element.
open import InfSearchable

ord-inf-searchable : (α : OE) → inf-searchable (λ x y → x ≼⟪ ord α ⟫ y)
ord-inf-searchable = {!!}
-}

\end{code}


TODO: The above discrete ordinals are enumerable.

Brouwer ordinal codes can be mapped to searchable ordinal codes, so
that the meaning is not necessarily preserved, but so that it is
bigger or equal, because sums dominate suprema.

\begin{code}

open import OrdinalCodes

brouwer-to-oe : B → OE
brouwer-to-oe    Z  = One
brouwer-to-oe (S α) = Add One (brouwer-to-oe α)
brouwer-to-oe (L α) = Sum1(λ i → brouwer-to-oe(α i))

\end{code}

The following is a relatively "small" example: an upper bound of the
ordinal ε₀ (because sums dominate suprema):

\begin{code}

ε₀-upper-bound : Ordᵀ
ε₀-upper-bound = ord(brouwer-to-oe B-ε₀)

searchable-ε₀-ub : searchable ⟪ ε₀-upper-bound ⟫
searchable-ε₀-ub = sord(brouwer-to-oe B-ε₀)

\end{code}

We can go much higher using the work of many people, including Hancock
and Setzer.
