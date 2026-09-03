Martin Escardo, March 2022

This generalizes the 2018 file OrdinalBrouwerCodesVariationInterpretations.

A Tarski universe E of ordinal codes with two related decoding
functions Δ and Κ (standing for "discrete" and "compact"
respectively).

Roughly speaking, E gives ordinal codes or expressions denoting
infinite ordinals. The expressions themselves are infinitary.

An ordinal is a type equipped with an order _≺_ that satisfies
suitable properties, which in particular imply that the type is a set
in the sense of HoTT/UF. The adopted notion of ordinal is that of the
HoTT book.

For a code ν : E, we have an ordinal Δ ν, which is discrete (has
decidable equality).

For a code ν : E, we have an ordinal Κ ν, which is compact (or
"searchable"). More than that, every complemented subset of Κ ν is
either empty or has a minimal element.

There is an embedding ι : Δ ν → Κ ν which is order preserving and
reflecting, and whose image has empty complement. The assumption that
it is a bijection implies LPO.

This extends and generalizes OrdinalBrouwerCodesVariationInterpretations, for
which slides for a talk are available at
https://www.cs.bham.ac.uk/~mhe/.talks/csl2022.pdf which may well serve
as an introduction to this file. The main difference is that the
ordinal expressions considered there amount to a W type, whereas the
ones considered here amount to an inductive-recursive type,
generalizing that, which is explained in these slides
https://www.cs.bham.ac.uk/~mhe/.talks/ljubljana2022.pdf

This is a draft version that needs polishing and more explanation.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Ordinals.InductiveRecursiveCodesInterpretations (fe : FunExt) where

private
 fe₀ = fe 𝓤₀ 𝓤₀

open import CoNaturals.Type
open import Fin.Topology
open import Fin.Type
open import MLTT.Two-Properties
open import Naturals.Binary hiding (_+_)
open import Notation.CanonicalMap hiding (ι)
open import Ordinals.Arithmetic fe
open import Ordinals.Closure fe
open import Ordinals.Equivalence
open import Ordinals.InfProperty
open import Ordinals.Injectivity
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import Taboos.LPO
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.Density
open import TypeTopology.FailureOfTotalSeparatedness fe₀
open import TypeTopology.GenericConvergentSequenceCompactness fe₀
open import TypeTopology.LimitPoints
open import TypeTopology.MicroInfTychonoff fe
open import TypeTopology.MicroTychonoff
open import TypeTopology.SigmaDiscrete
open import TypeTopology.SigmaTotallySeparated
open import TypeTopology.TotallySeparated
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PairFun
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
import W.Properties
open import W.Type

\end{code}

We define E and Δ by simultaneous induction. The type Ordᵀ is that of
ordinals with a top element (classically, successor ordinals). Recall
that ⟨ α ⟩ is the underlying type of α : Ordᵀ.

\begin{code}

data E : 𝓤₀ ̇
Δ : E → Ordᵀ

data E where
 ⌜𝟙⌝   : E
 ⌜ω+𝟙⌝ : E
 _⌜+⌝_ : E → E → E
 _⌜×⌝_ : E → E → E
 ⌜Σ⌝   : (ν : E) → (⟨ Δ ν ⟩ → E) → E

Δ ⌜𝟙⌝         = 𝟙ᵒ
Δ ⌜ω+𝟙⌝       = succₒ ω
Δ (ν₀ ⌜+⌝ ν₁) = Δ ν₀ +ᵒ Δ ν₁
Δ (ν₀ ⌜×⌝ ν₁) = Δ ν₀ ×ᵒ Δ ν₁
Δ (⌜Σ⌝ ν A)   = ∑ (Δ ν) (Δ ∘ A)

\end{code}

The underlying sets of all ordinals in the image of Δ are retracts of
ℕ and hence countable.

\begin{code}

Δ-retract-of-ℕ : (ν : E) → retract ⟨ Δ ν ⟩ of ℕ
Δ-retract-of-ℕ ⌜𝟙⌝         = (λ _ → ⋆) , (λ _ → 0) , 𝟙-is-prop ⋆
Δ-retract-of-ℕ ⌜ω+𝟙⌝       = ≃-gives-◁ ℕ-plus-𝟙
Δ-retract-of-ℕ (ν₀ ⌜+⌝ ν₁) = Σ-retract-of-ℕ
                              retract-𝟙+𝟙-of-ℕ
                              (dep-cases
                                (λ _ → Δ-retract-of-ℕ ν₀)
                                (λ _ → Δ-retract-of-ℕ ν₁))
Δ-retract-of-ℕ (ν₀ ⌜×⌝ ν₁) = Σ-retract-of-ℕ
                              (Δ-retract-of-ℕ ν₀)
                              (λ _ → Δ-retract-of-ℕ ν₁)
Δ-retract-of-ℕ (⌜Σ⌝ ν A)   = Σ-retract-of-ℕ
                              (Δ-retract-of-ℕ ν)
                              (λ x → Δ-retract-of-ℕ (A x))
\end{code}

Hence all ordinals in the image of Δ are discrete (have decidable
equality).

\begin{code}

Δ-is-discrete : (ν : E) → is-discrete ⟨ Δ ν ⟩
Δ-is-discrete ν = retract-is-discrete (Δ-retract-of-ℕ ν) ℕ-is-discrete

\end{code}

The discrete interpretation is compact for every code precisely when
LPO holds. One direction is that Δ ν is a retract of ℕ, and the other
uses the single code ⌜ω+𝟙⌝, whose discrete interpretation has ℕ + 𝟙 as
its underlying type.

\begin{code}

LPO-gives-Δ-compact : LPO → (ν : E) → is-compact ⟨ Δ ν ⟩
LPO-gives-Δ-compact lpo ν = retract-is-compact
                             (Δ-retract-of-ℕ ν)
                             (LPO-gives-compact-ℕ fe₀ lpo)

Δ-compact-gives-LPO : ((ν : E) → is-compact ⟨ Δ ν ⟩) → LPO
Δ-compact-gives-LPO κ = compact-ℕ-gives-LPO fe₀
                         (retract-is-compact
                           (≃-gives-◁ (≃-sym ℕ-plus-𝟙))
                           (κ ⌜ω+𝟙⌝))

Δ-compact-iff-LPO : ((ν : E) → is-compact ⟨ Δ ν ⟩) ↔ LPO
Δ-compact-iff-LPO = Δ-compact-gives-LPO , LPO-gives-Δ-compact

\end{code}

A stronger result is that the ordinals in the image of Δ are
trichotomous:

\begin{code}

Δ-is-trichotomous : (ν : E) → is-trichotomous [ Δ ν ]
Δ-is-trichotomous ⌜𝟙⌝         = 𝟙ₒ-is-trichotomous
Δ-is-trichotomous ⌜ω+𝟙⌝       = succₒ-is-trichotomous ω ω-is-trichotomous
Δ-is-trichotomous (ν₀ ⌜+⌝ ν₁) = +ᵒ-is-trichotomous (Δ ν₀) (Δ ν₁)
                                 (Δ-is-trichotomous ν₀)
                                 (Δ-is-trichotomous ν₁)
Δ-is-trichotomous (ν₀ ⌜×⌝ ν₁) = ×ᵒ-is-trichotomous (Δ ν₀) (Δ ν₁)
                                 (Δ-is-trichotomous ν₀)
                                 (Δ-is-trichotomous ν₁)
Δ-is-trichotomous (⌜Σ⌝ ν A)   = ∑-is-trichotomous (Δ ν) (Δ ∘ A)
                                 (Δ-is-trichotomous ν)
                                 (Δ-is-trichotomous ∘ A)

\end{code}

Now we define Κ, ι, ι-is-embedding by simultaneous induction.

\begin{code}

Κ : E → Ordᵀ
ι : (ν : E) → ⟨ Δ ν ⟩ → ⟨ Κ ν ⟩
ι-is-embedding : (ν : E) → is-embedding (ι ν)

\end{code}

Before completing the induction, we define the following abbreviation.

\begin{code}

j : (ν : E) → ⟨ Δ ν ⟩ ↪ ⟨ Κ ν ⟩
j ν = ι ν , ι-is-embedding ν

\end{code}

We use the following auxiliary extension constructions, illustrated by
this diagram

                   ι ν
          ⟨ Δ ν ⟩  ⟶ ⟨ Κ ν ⟩
              |           .
              |           .
           A  |           .  (K ∘ A) ↗ j ν
              |           .
              ↓           ↓
              E    ⟶   Ordᵀ
                    Κ

See the files ToppedOrdinalArithmetic and InjectiveTypes for details.

\begin{code}

open topped-ordinals-injectivity fe

𝓚 : (ν : E) → (⟨ Δ ν ⟩ → E) → ⟨ Κ ν ⟩ → Ordᵀ
𝓚 ν A = (Κ ∘ A) ↗ j ν

\end{code}

Explicitly, the underlying set of this ordinal is given as follows in
the file InjectiveTypes.

\begin{code}

_ : (ν : E) (A : ⟨ Δ ν ⟩ → E) (y : ⟨ Κ ν ⟩)
  → ⟨ 𝓚 ν A y ⟩ ＝ (Π (x , _) ꞉ fiber (ι ν) y , ⟨ Κ (A x) ⟩)
_ = λ ν A y → refl

\end{code}

The above gives an extension up to ordinal equivalence

\begin{code}

module Κ-extension (ν : E) (A : ⟨ Δ ν ⟩ → E) where

 ϕ : (x : ⟨ Δ ν ⟩) → [ 𝓚 ν A (ι ν x) ] ≃ₒ [ Κ (A x) ]
 ϕ = ↗-propertyₒ (Κ ∘ A) (j ν)

 φ : (x : ⟨ Δ ν ⟩) → ⟨ 𝓚 ν A (ι ν x) ⟩ → ⟨ Κ (A x) ⟩
 φ x = ≃ₒ-to-fun [ 𝓚 ν A (ι ν x) ] [ Κ (A x) ] (ϕ x)

 φ⁻¹ : (x : ⟨ Δ ν ⟩) → ⟨ Κ (A x) ⟩ → ⟨ 𝓚 ν A (ι ν x) ⟩
 φ⁻¹ x = ≃ₒ-to-fun⁻¹ [ 𝓚 ν A (ι ν x) ] [ Κ (A x) ] (ϕ x)

 φ-is-equiv : (x : ⟨ Δ ν ⟩) → is-equiv (φ x)
 φ-is-equiv x = ≃ₒ-to-fun-is-equiv [ 𝓚 ν A (ι ν x) ] [ Κ (A x) ] (ϕ x)

 φ⁻¹-is-equiv : (x : ⟨ Δ ν ⟩) → is-equiv (φ⁻¹ x)
 φ⁻¹-is-equiv x = ≃ₒ-to-fun⁻¹-is-equiv [ 𝓚 ν A (ι ν x) ] [ Κ (A x) ] (ϕ x)

 Φ : (x : ⟨ Δ ν ⟩) → ⟨ Κ (A x) ⟩ ≃ ⟨ 𝓚 ν A (ι ν x) ⟩
 Φ x = φ⁻¹ x , φ⁻¹-is-equiv x

Κ ⌜𝟙⌝         = 𝟙ᵒ
Κ ⌜ω+𝟙⌝       = ℕ∞ᵒ
Κ (ν₀ ⌜+⌝ ν₁) = Κ ν₀ +ᵒ Κ ν₁
Κ (ν₀ ⌜×⌝ ν₁) = Κ ν₀ ×ᵒ Κ ν₁
Κ (⌜Σ⌝ ν A)   = ∑ (Κ ν) (𝓚 ν A)

ι ⌜𝟙⌝         = id
ι ⌜ω+𝟙⌝       = ι𝟙
ι (ν₀ ⌜+⌝ ν₁) = pair-fun id (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
ι (ν₀ ⌜×⌝ ν₁) = pair-fun (ι ν₀) (λ _ → ι ν₁)
ι (⌜Σ⌝ ν A)   = pair-fun (ι ν) (λ x → φ⁻¹ x ∘ ι (A x))
 where
  open Κ-extension ν A

ι-is-embedding ⌜𝟙⌝         = id-is-embedding
ι-is-embedding ⌜ω+𝟙⌝       = ι𝟙-is-embedding fe₀
ι-is-embedding (ν₀ ⌜+⌝ ν₁) = pair-fun-is-embedding
                              id
                              (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                              id-is-embedding
                              (dep-cases
                                (λ _ → ι-is-embedding ν₀)
                                (λ _ → ι-is-embedding ν₁))
ι-is-embedding (ν₀ ⌜×⌝ ν₁) = pair-fun-is-embedding _ _
                              (ι-is-embedding ν₀)
                              (λ _ → ι-is-embedding ν₁)
ι-is-embedding (⌜Σ⌝ ν A)   = pair-fun-is-embedding _ _
                              (ι-is-embedding ν)
                              (λ x → ∘-is-embedding
                                      (ι-is-embedding (A x))
                                      (equivs-are-embeddings' (Φ x)))
 where
  open Κ-extension ν A

\end{code}

This completes the definitions of Κ, ι and ι-is-embedding.

The important fact about the Κ interpretation is that the ordinals in
its image are compact, which we prove directly by induction, and that
they moreover have the least element property for non-empty
complemented subsets, and more generally infima of arbitrary
complemented subsets.

Compactness used to be derived from the least element property
instead. It is now derived from the induction here so that it does not
depend on propositional extensionality any longer, and so that we get
the pointed form, which is the stronger one and is what the induction
gives. The unpointed form is kept as a corollary because it is what
the results about limit points below need.

\begin{code}

Κ-compact∙ : (ν : E) → is-compact∙ ⟨ Κ ν ⟩
𝓚-compact∙ : (ν : E) (A : ⟨ Δ ν ⟩ → E) (y : ⟨ Κ ν ⟩)
           → is-compact∙ ⟨ 𝓚 ν A y ⟩

\end{code}

These two are proved by simultaneous induction. The second one holds
because the underlying type of 𝓚 ν A y is a product indexed by the
fiber of ι ν over y, which is a proposition since ι ν is an embedding,
so that micro-tychonoff applies.

The pointedness is essential in this induction, as it is in the module
Ordinals.BrouwerCodesVariationInterpretations, because a version of
micro-tychonoff without pointedness implies excluded middle.

\begin{code}

Κ-compact∙ ⌜𝟙⌝         = 𝟙-is-compact∙
Κ-compact∙ ⌜ω+𝟙⌝       = ℕ∞-compact∙
Κ-compact∙ (ν₀ ⌜+⌝ ν₁) = Σ-is-compact∙
                          𝟙+𝟙-is-compact∙
                          (dep-cases
                            (λ _ → Κ-compact∙ ν₀)
                            (λ _ → Κ-compact∙ ν₁))
Κ-compact∙ (ν₀ ⌜×⌝ ν₁) = Σ-is-compact∙
                          (Κ-compact∙ ν₀)
                          (λ _ → Κ-compact∙ ν₁)
Κ-compact∙ (⌜Σ⌝ ν A)   = Σ-is-compact∙
                          (Κ-compact∙ ν)
                          (𝓚-compact∙ ν A)

𝓚-compact∙ ν A y = micro-tychonoff
                    (fe 𝓤₀ 𝓤₀)
                    (ι-is-embedding ν y)
                    (λ (x , _) → Κ-compact∙ (A x))

Κ-Compact : {𝓥 : Universe} (ν : E) → is-Compact ⟨ Κ ν ⟩ {𝓥}
Κ-Compact ν = compact-types-are-Compact
               (compact∙-types-are-compact (Κ-compact∙ ν))

𝓚-Compact : {𝓥 : Universe} (ν : E) (A : ⟨ Δ ν ⟩ → E) (y : ⟨ Κ ν ⟩)
          → is-Compact ⟨ 𝓚 ν A y ⟩ {𝓥}
𝓚-Compact ν A y = compact-types-are-Compact
                   (compact∙-types-are-compact (𝓚-compact∙ ν A y))

\end{code}

The ordinals in the image of Κ moreover have the least element property
for non-empty complemented subsets, and more generally infima of
arbitrary complemented subsets. This needs propositional extensionality,
which, as discussed in the module Ordinals.Closure, is not strictly
needed but makes our life much easier.

\begin{code}

module _ (pe : propext 𝓤₀) where

 K-has-infs-of-complemented-subsets : (ν : E)
                                    → has-infs-of-complemented-subsets (Κ ν)
 𝓚-has-infs-of-complemented-subsets : (ν : E) (A : ⟨ Δ ν ⟩ → E) (x : ⟨ Κ ν ⟩)
                                    → has-infs-of-complemented-subsets (𝓚 ν A x)

 K-has-infs-of-complemented-subsets ⌜𝟙⌝
  = 𝟙ᵒ-has-infs-of-complemented-subsets
 K-has-infs-of-complemented-subsets ⌜ω+𝟙⌝
  = ℕ∞ᵒ-has-infs-of-complemented-subsets pe
 K-has-infs-of-complemented-subsets (ν₀ ⌜+⌝ ν₁)
  = ∑-has-infs-of-complemented-subsets pe
     𝟚ᵒ
     (cases (λ _ → Κ ν₀) (λ _ → Κ ν₁))
     𝟚ᵒ-has-infs-of-complemented-subsets
     (dep-cases
       (λ _ → K-has-infs-of-complemented-subsets ν₀)
       (λ _ → K-has-infs-of-complemented-subsets ν₁))
 K-has-infs-of-complemented-subsets (ν₀ ⌜×⌝ ν₁)
  = ∑-has-infs-of-complemented-subsets pe
     (Κ ν₀)
     (λ _ → Κ ν₁)
     (K-has-infs-of-complemented-subsets ν₀)
     (λ _ → K-has-infs-of-complemented-subsets ν₁)
 K-has-infs-of-complemented-subsets (⌜Σ⌝ ν A)
  = ∑-has-infs-of-complemented-subsets pe (Κ ν) (𝓚 ν A)
     (K-has-infs-of-complemented-subsets ν)
     (𝓚-has-infs-of-complemented-subsets ν A)
 𝓚-has-infs-of-complemented-subsets ν A x
  = micro-inf-tychonoff
     (ι-is-embedding ν x)
     (λ {(x , _)} y z → y ≺⟨ Κ (A x) ⟩ z)
     (λ (x , _) → K-has-infs-of-complemented-subsets (A x))

\end{code}

The embedding of the Δ interpretation into the Κ interpretation is
order-preserving, order-reflecting, and dense (its image has empty
complement).

\begin{code}

ι-is-order-preserving : (ν : E) (x y : ⟨ Δ ν ⟩)
                      → x ≺⟨ Δ ν ⟩ y
                      → ι ν x ≺⟨ Κ ν ⟩ ι ν y
ι-is-order-preserving ⌜𝟙⌝         = λ x y l → l
ι-is-order-preserving ⌜ω+𝟙⌝       = ι𝟙ᵒ-is-order-preserving
ι-is-order-preserving (ν₀ ⌜+⌝ ν₁) = pair-fun-is-order-preserving
                                     𝟚ᵒ
                                     𝟚ᵒ
                                     (cases (λ _ → Δ ν₀) (λ _ → Δ ν₁))
                                     (cases (λ _ → Κ ν₀) (λ _ → Κ ν₁))
                                     id
                                     (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                                     (λ x y l → l)
                                     (dep-cases
                                       (λ _ → ι-is-order-preserving ν₀)
                                       (λ _ → ι-is-order-preserving ν₁))
ι-is-order-preserving (ν₀ ⌜×⌝ ν₁) = pair-fun-is-order-preserving
                                     (Δ ν₀)
                                     (Κ ν₀)
                                     (λ _ → Δ ν₁)
                                     (λ _ → Κ ν₁)
                                     (ι ν₀)
                                     (λ _ → ι ν₁)
                                     (ι-is-order-preserving ν₀)
                                     (λ _ → ι-is-order-preserving ν₁)
ι-is-order-preserving (⌜Σ⌝ ν A)   = pair-fun-is-order-preserving
                                     (Δ ν)
                                     (Κ ν)
                                     (Δ ∘ A)
                                     (𝓚 ν A)
                                     (ι ν)
                                     (λ x → φ⁻¹ x ∘ ι (A x))
                                     (ι-is-order-preserving ν)
                                     g
 where
  open Κ-extension ν A

  IH : (x : ⟨ Δ ν ⟩) (y z : ⟨ Δ (A x) ⟩)
     → y ≺⟨ Δ (A x) ⟩ z
     → ι (A x) y ≺⟨ Κ (A x) ⟩ ι (A x) z
  IH x = ι-is-order-preserving (A x)

  f : (x : ⟨ Δ ν ⟩) (y z : ⟨ Δ (A x) ⟩)
    → ι (A x) y ≺⟨ Κ (A x) ⟩ ι (A x) z
    →  φ⁻¹ x (ι (A x) y) ≺⟨ 𝓚 ν A (ι ν x) ⟩ φ⁻¹ x (ι (A x) z)
  f x y z = inverses-of-order-equivs-are-order-preserving
             [ 𝓚 ν A (ι ν x) ]
             [ Κ (A x) ]
             (≃ₒ-to-fun-is-order-equiv [ 𝓚 ν A (ι ν x) ] [ Κ (A x) ] (ϕ x))
             (ι (A x) y)
             (ι (A x) z)

  g : (x : ⟨ Δ ν ⟩) (y z : ⟨ Δ (A x) ⟩)
    → y ≺⟨ Δ (A x) ⟩ z
    → φ⁻¹ x (ι (A x) y) ≺⟨ 𝓚 ν A (ι ν x) ⟩ φ⁻¹ x (ι (A x) z)
  g x y z l = f x y z (IH x y z l)


ι-is-order-reflecting : (ν : E) (x y : ⟨ Δ ν ⟩)
                      → ι ν x ≺⟨ Κ ν ⟩ ι ν y
                      → x ≺⟨ Δ ν ⟩ y
ι-is-order-reflecting ⌜𝟙⌝        = λ x y l → l
ι-is-order-reflecting ⌜ω+𝟙⌝      = ι𝟙ᵒ-is-order-reflecting
ι-is-order-reflecting (ν₀ ⌜+⌝ ν₁) = pair-fun-is-order-reflecting
                                     𝟚ᵒ
                                     𝟚ᵒ
                                     (cases (λ _ → Δ ν₀) (λ _ → Δ ν₁))
                                     (cases (λ _ → Κ ν₀) (λ _ → Κ ν₁))
                                     id
                                     (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                                     (λ x y l → l)
                                     id-is-embedding
                                     (dep-cases
                                       (λ _ → ι-is-order-reflecting ν₀)
                                       (λ _ → ι-is-order-reflecting ν₁))
ι-is-order-reflecting (ν₀ ⌜×⌝ ν₁) = pair-fun-is-order-reflecting
                                     (Δ ν₀)
                                     (Κ ν₀)
                                     (λ _ → Δ ν₁)
                                     (λ _ → Κ ν₁)
                                     (ι ν₀)
                                     (λ _ → ι ν₁)
                                     (ι-is-order-reflecting ν₀)
                                     (ι-is-embedding ν₀)
                                     (λ _ → ι-is-order-reflecting ν₁)
ι-is-order-reflecting (⌜Σ⌝ ν A)  = pair-fun-is-order-reflecting
                                    (Δ ν)
                                    (Κ ν)
                                    (Δ ∘ A)
                                    (𝓚 ν A)
                                    (ι ν)
                                    (λ x → φ⁻¹ x ∘ ι (A x))
                                    (ι-is-order-reflecting ν)
                                    (ι-is-embedding ν)
                                    g
 where
  open Κ-extension ν A

  IH : (x : ⟨ Δ ν ⟩) (y z : ⟨ Δ (A x) ⟩)
     → ι (A x) y ≺⟨ Κ (A x) ⟩ ι (A x) z
     → y ≺⟨ Δ (A x) ⟩ z
  IH x = ι-is-order-reflecting (A x)

  f : (x : ⟨ Δ ν ⟩) (y z : ⟨ Δ (A x) ⟩)
    → φ⁻¹ x (ι (A x) y) ≺⟨ 𝓚 ν A (ι ν x) ⟩ φ⁻¹ x (ι (A x) z)
    → ι (A x) y ≺⟨ Κ (A x) ⟩ ι (A x) z
  f x y z = inverses-of-order-equivs-are-order-reflecting
             [ 𝓚 ν A (ι ν x) ]
             [ Κ (A x) ]
             (≃ₒ-to-fun-is-order-equiv [ 𝓚 ν A (ι ν x) ] [ Κ (A x) ] (ϕ x))
             (ι (A x) y)
             (ι (A x) z)

  g : (x : ⟨ Δ ν ⟩) (y z : ⟨ Δ (A x) ⟩)
    → φ⁻¹ x (ι (A x) y) ≺⟨ 𝓚 ν A (ι ν x) ⟩ φ⁻¹ x (ι (A x) z)
    → y ≺⟨ Δ (A x) ⟩ z
  g x y z l = IH x y z (f x y z l)


ι-is-dense : (ν : E) → is-dense (ι ν)
ι-is-dense ⌜𝟙⌝         = id-is-dense
ι-is-dense ⌜ω+𝟙⌝       = ι𝟙-dense fe₀
ι-is-dense (ν₀ ⌜+⌝ ν₁) = pair-fun-dense
                          id
                          (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                          id-is-dense
                          (dep-cases (λ _ → ι-is-dense ν₀) (λ _ → ι-is-dense ν₁))
ι-is-dense (ν₀ ⌜×⌝ ν₁) = pair-fun-dense _ _
                          (ι-is-dense ν₀)
                          (λ _ → ι-is-dense ν₁)
ι-is-dense (⌜Σ⌝ ν A)   = pair-fun-dense
                          (ι ν)
                          (λ x → φ⁻¹ x ∘ ι (A x))
                          (ι-is-dense ν)
                          (λ x → comp-is-dense
                                  (ι-is-dense (A x))
                                  (equivs-are-dense' (Φ x)))
 where
  open Κ-extension ν A

\end{code}

The characteristic function of topological limit points.

\begin{code}

ℓ : (ν : E) → ⟨ Δ ν ⟩ → 𝟚
ℓ ⌜𝟙⌝         ⋆            = ₀
ℓ ⌜ω+𝟙⌝       (inl n)      = ₀
ℓ ⌜ω+𝟙⌝       (inr ⋆)      = ₁
ℓ (ν₀ ⌜+⌝ ν₁) (inl ⋆ , x₀) = ℓ ν₀ x₀
ℓ (ν₀ ⌜+⌝ ν₁) (inr ⋆ , x₁) = ℓ ν₁ x₁
ℓ (ν₀ ⌜×⌝ ν₁) (x₀ , x₁)    = max𝟚 (ℓ ν₀ x₀) (ℓ ν₁ x₁)
ℓ (⌜Σ⌝ ν A)   (x  , y)     = max𝟚 (ℓ ν x) (ℓ (A x) y)

\end{code}

Non-limit points are isolated in the Κ interpretation:

\begin{code}

ℓ-isolated : (ν : E) (x : ⟨ Δ ν ⟩) → ℓ ν x ＝ ₀ → is-isolated (ι ν x)
ℓ-isolated ⌜𝟙⌝         ⋆            p    = 𝟙-is-discrete ⋆
ℓ-isolated ⌜ω+𝟙⌝       (inl n)      refl = finite-isolated fe₀ n
ℓ-isolated (ν₀ ⌜+⌝ ν₁) (inl ⋆ , x₀) p    = Σ-isolated
                                            (inl-is-isolated ⋆ (𝟙-is-discrete ⋆))
                                            (ℓ-isolated ν₀ x₀ p)
ℓ-isolated (ν₀ ⌜+⌝ ν₁) (inr ⋆ , x₁) p    = Σ-isolated
                                            (inr-is-isolated ⋆ (𝟙-is-discrete ⋆))
                                            (ℓ-isolated ν₁ x₁ p)
ℓ-isolated (ν₀ ⌜×⌝ ν₁) (x₀ , x₁)    p    = Σ-isolated
                                            (ℓ-isolated ν₀ x₀ (max𝟚-₀-left p))
                                            (ℓ-isolated ν₁ x₁ (max𝟚-₀-right p))
ℓ-isolated (⌜Σ⌝ ν A)   (x , y)      p    = iv
 where
  open Κ-extension ν A

  i : is-isolated (ι ν x)
  i = ℓ-isolated ν x (max𝟚-₀-left p)

  ii : is-isolated (ι (A x) y)
  ii = ℓ-isolated (A x) y (max𝟚-₀-right p)

  iii : is-isolated (φ⁻¹ x (ι (A x) y))
  iii = equivs-preserve-isolatedness (φ⁻¹ x) (φ⁻¹-is-equiv x) (ι (A x) y) ii

  iv : is-isolated (ι ν x , φ⁻¹ x (ι (A x) y))
  iv = Σ-isolated i iii

\end{code}

The function ℓ really does detect limit points:

\begin{code}

ℓ-limit : (ν : E) (x : ⟨ Δ ν ⟩) → ℓ ν x ＝ ₁ → is-limit-point (ι ν x)
ℓ-limit ⌜ω+𝟙⌝       (inr ⋆)      p i = is-isolated-gives-is-isolated' ∞ i
ℓ-limit (ν₀ ⌜+⌝ ν₁) (inl ⋆ , x₀) p i = ℓ-limit ν₀ x₀ p
                                        (Σ-isolated-right
                                          (underlying-type-is-setᵀ fe 𝟚ᵒ)
                                          i)
ℓ-limit (ν₀ ⌜+⌝ ν₁) (inr ⋆ , x₁) p i = ℓ-limit ν₁ x₁ p
                                        (Σ-isolated-right
                                          (underlying-type-is-setᵀ fe 𝟚ᵒ)
                                          i)
ℓ-limit (ν₀ ⌜×⌝ ν₁) (x₀ , x₁)    p i =
  Cases (max𝟚-lemma p)
   (λ (p₀ : ℓ ν₀ x₀ ＝ ₁) → ℓ-limit ν₀ x₀ p₀ (×-isolated-left i))
   (λ (p₁ : ℓ ν₁ x₁ ＝ ₁) → ℓ-limit ν₁ x₁ p₁ (×-isolated-right i))
ℓ-limit (⌜Σ⌝ ν A)   (x , y)      p i =
  Cases (max𝟚-lemma p)
   (λ (p₀ : ℓ ν x ＝ ₁)
          → ℓ-limit ν x p₀ (Σ-isolated-left (𝓚-Compact ν A) i))
   (λ (p₁ : ℓ (A x) y ＝ ₁)
          → ℓ-limit (A x) y p₁
             (equivs-reflect-isolatedness (φ⁻¹ x)
               (φ⁻¹-is-equiv x)
               (ι (A x) y)
               (Σ-isolated-right
                 (underlying-type-is-setᵀ fe (Κ ν)) i)))
 where
  open Κ-extension ν A

isolatedness-decision : (ν : E) (x : ⟨ Δ ν ⟩)
                      → is-isolated (ι ν x) + is-limit-point (ι ν x)
isolatedness-decision ν x = 𝟚-equality-cases
                             (λ (p : ℓ ν x ＝ ₀) → inl (ℓ-isolated ν x p))
                             (λ (p : ℓ ν x ＝ ₁) → inr (ℓ-limit ν x p))

isolatedness-decision' : ¬ WLPO
                       → (ν : E) (x : ⟨ Δ ν ⟩)
                       → is-decidable (is-isolated (ι ν x))
isolatedness-decision' f ν x =
  Cases (isolatedness-decision ν x)
   inl
   (λ (g : is-isolated (ι ν x) → WLPO)  → inr (contrapositive g f))

\end{code}

Added 14th October 2024. Actually we have that a stronger property of
limit point holds.

\begin{code}

ℓ-limit⁺ : (ν : E) (x : ⟨ Δ ν ⟩) → ℓ ν x ＝ ₁ → is-limit-point⁺ (ι ν x)
ℓ-limit⁺ ⌜ω+𝟙⌝ (inr x) p i = ∞-is-a-limit-point⁺-of-ℕ∞ i
ℓ-limit⁺ (ν₀ ⌜+⌝ ν₁) (inl ⋆ , x₀) p i
 = ℓ-limit⁺ ν₀ x₀ p
    (Σ-weakly-isolated-right
      (underlying-type-is-setᵀ fe 𝟚ᵒ)
      i)
ℓ-limit⁺ (ν₀ ⌜+⌝ ν₁) (inr ⋆ , x₁) p i
 = ℓ-limit⁺ ν₁ x₁ p
    (Σ-weakly-isolated-right
      (underlying-type-is-setᵀ fe 𝟚ᵒ)
      i)
ℓ-limit⁺ (ν₀ ⌜×⌝ ν₁) (x₀ , x₁)    p i
 = Cases (max𝟚-lemma p)
    (λ (p₀ : ℓ ν₀ x₀ ＝ ₁) → ℓ-limit⁺ ν₀ x₀ p₀ (×-weakly-isolated-left i))
    (λ (p₁ : ℓ ν₁ x₁ ＝ ₁) → ℓ-limit⁺ ν₁ x₁ p₁ (×-weakly-isolated-right i))
ℓ-limit⁺ (⌜Σ⌝ ν A)   (x , y)      p i
 = Cases (max𝟚-lemma p)
    (λ (p₀ : ℓ ν x ＝ ₁)
           → ℓ-limit⁺ ν x p₀ (Σ-weakly-isolated-left (𝓚-Compact ν A) i))
    (λ (p₁ : ℓ (A x) y ＝ ₁)
           → ℓ-limit⁺ (A x) y p₁
              (equivs-reflect-weak-isolatedness
                (Φ x)
                (ι (A x) y)
                (Σ-weakly-isolated-right
                  (underlying-type-is-setᵀ fe (Κ ν)) i)))
  where
   open Κ-extension ν A

\end{code}

End of addition and back to the past.

We conclude with some impossibility results.

\begin{code}

ι-is-equiv-gives-LPO : ((ν : E) → is-equiv (ι ν))
                     → LPO
ι-is-equiv-gives-LPO f = ι𝟙-is-equiv-gives-LPO (f ⌜ω+𝟙⌝)

LPO-gives-ι-is-equiv : LPO
                     → ((ν : E) → is-equiv (ι ν))
LPO-gives-ι-is-equiv lpo ⌜𝟙⌝         = id-is-equiv 𝟙
LPO-gives-ι-is-equiv lpo ⌜ω+𝟙⌝       = LPO-gives-ι𝟙-is-equiv fe₀ lpo
LPO-gives-ι-is-equiv lpo (ν₀ ⌜+⌝ ν₁) = pair-fun-is-equiv
                                        id
                                        (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                                        (id-is-equiv (𝟙 + 𝟙))
                                        (dep-cases
                                          (λ _ → LPO-gives-ι-is-equiv lpo ν₀)
                                          (λ _ → LPO-gives-ι-is-equiv lpo ν₁))
LPO-gives-ι-is-equiv lpo (ν₀ ⌜×⌝ ν₁) = pair-fun-is-equiv _ _
                                        (LPO-gives-ι-is-equiv lpo ν₀)
                                        (λ _ → LPO-gives-ι-is-equiv lpo ν₁)
LPO-gives-ι-is-equiv lpo (⌜Σ⌝ ν A)   = pair-fun-is-equiv
                                        (ι ν)
                                        (λ x → φ⁻¹ x ∘ ι (A x))
                                        (LPO-gives-ι-is-equiv lpo ν)
                                        (λ x → ∘-is-equiv
                                                (LPO-gives-ι-is-equiv lpo (A x))
                                                (φ⁻¹-is-equiv x))
 where
  open Κ-extension ν A

ι-is-equiv-iff-LPO : ((ν : E) → is-equiv (ι ν)) ↔ LPO
ι-is-equiv-iff-LPO = ι-is-equiv-gives-LPO , LPO-gives-ι-is-equiv

\end{code}

We also have the following:

\begin{code}

ι-has-section-gives-Κ-discrete : (ν : E)
                               → has-section (ι ν)
                               → is-discrete ⟨ Κ ν ⟩
ι-has-section-gives-Κ-discrete ν (θ , ιθ) = lc-maps-reflect-discreteness θ
                                             (sections-are-lc θ (ι ν , ιθ))
                                             (Δ-is-discrete ν)

ι-is-equiv-gives-Κ-discrete : (ν : E)
                            → is-equiv (ι ν)
                            → is-discrete ⟨ Κ ν ⟩
ι-is-equiv-gives-Κ-discrete ν e = ι-has-section-gives-Κ-discrete ν
                                   (equivs-have-sections (ι ν) e)

LPO-gives-Κ-discrete : LPO
                     → ((ν : E) → is-discrete ⟨ Κ ν ⟩)
LPO-gives-Κ-discrete lpo ν = ι-is-equiv-gives-Κ-discrete ν
                              (LPO-gives-ι-is-equiv lpo ν)

Κ-discrete-gives-WLPO : ((ν : E) → is-discrete ⟨ Κ ν ⟩)
                      → WLPO
Κ-discrete-gives-WLPO f = ℕ∞-discrete-gives-WLPO (f ⌜ω+𝟙⌝)

\end{code}

We close with some open questions.

TODO. Can we close the gap between the last two facts? The difficulty
that arises here is similar to the following.

Let P be a proposition and assume function extensionality.

(0) If P is decidable, then the function type (P → 𝟚) has decidable equality.

(1) If (P → 𝟚) has decidable equality, then ¬ P is decidable.

It doesn't seem to be possible to reverse any of the implications (0)
and (1), so that the proposition "(P → 2) has decidable equality"
seems to be strictly between "P is decidable" and "¬P is decidable".
This is discussed in the file Taboos.P2.

TODO. Do we have (ν : E) → [ Δ ν ] ⊴ [ Κ ν ]? Notice that we do have
(ω +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ, proved in Ordinals.ConvergentSequence.

TODO. Define an element x of an ordinal to be trisolated if for every
y we have that y ≺ x or x ＝ y or x ≺ y.  Notice that trisolated
elements are isolated. Then an ordinal is trichotomous iff every
element is trisolated. We should have the following:

ℓ-trisolated : (ν : E) (x : ⟨ Δ ν ⟩) → ℓ ν x ＝ ₀ → is-trisolated (ι ν x)

We don't need to discuss the case ℓ ν x ＝ ₁ because this is already
covered by ℓ-limit as trisolated points are isolated.

TODO. An element x of α is trisolated iff there are ordinals αₕ and αₜ
and an ordinal-equivalence αₕ +ₒ 𝟙ₒ + αₜ → α that maps the point at
the component 𝟙ₒ to x.

Suprema of compact-indexed families of compact ordinals are compact,
proved in Ordinals.CompactnessOfSuprema from the constructions in
Ordinals.OrdinalOfOrdinalsSuprema.

TODO. Are the ordinals in the image of K totally separated?

Added August 2026. The universe E is a set. We prove this by
encoding it into a W-type, which is possible because the branching type
⟨ Δ ν ⟩ of the constructor ⌜Σ⌝ is a retract of ℕ, so that a family
indexed by it is determined by its restriction along the retraction,
and ℕ can serve as the arity of that constructor.

Only the five pairs of equal constructors of E occur in the induction
below. The other twenty are refuted by the clash of shapes of the
W-type in the hypothesis.

\begin{code}

E-is-set : is-set E
E-is-set = subtypes-of-sets-are-sets' e e-lc 𝕋-is-set
 where
  shape : 𝓤₀ ̇
  shape = Fin 5

  arity : shape → 𝓤₀ ̇
  arity 𝟎 = 𝟘
  arity 𝟏 = 𝟘
  arity 𝟐 = 𝟙 + 𝟙
  arity 𝟑 = 𝟙 + 𝟙
  arity 𝟒 = 𝟙 + ℕ

  𝕋 : 𝓤₀ ̇
  𝕋 = W shape arity

  open W.Properties shape arity

  𝕋-is-set : is-set 𝕋
  𝕋-is-set = W-is-set (fe 𝓤₀ 𝓤₀) Fin-is-set

  ρ : (ν : E) → ℕ → ⟨ Δ ν ⟩
  ρ ν = retraction (Δ-retract-of-ℕ ν)

  σ : (ν : E) → ⟨ Δ ν ⟩ → ℕ
  σ ν = section (Δ-retract-of-ℕ ν)

  ρσ : (ν : E) (x : ⟨ Δ ν ⟩) → ρ ν (σ ν x) ＝ x
  ρσ ν = retract-condition (Δ-retract-of-ℕ ν)

  e : E → 𝕋
  e ⌜𝟙⌝       = ssup 𝟎 𝟘-elim
  e ⌜ω+𝟙⌝     = ssup 𝟏 𝟘-elim
  e (ν ⌜+⌝ μ) = ssup 𝟐 (cases (λ _ → e ν) (λ _ → e μ))
  e (ν ⌜×⌝ μ) = ssup 𝟑 (cases (λ _ → e ν) (λ _ → e μ))
  e (⌜Σ⌝ ν A) = ssup 𝟒 (cases (λ _ → e ν) (λ n → e (A (ρ ν n))))

  ⌜Σ⌝-＝ : (ν ν' : E) → ν ＝ ν'
         → (A : ⟨ Δ ν ⟩ → E) (A' : ⟨ Δ ν' ⟩ → E)
         → ((n : ℕ) → A (ρ ν n) ＝ A' (ρ ν' n))
         → ⌜Σ⌝ ν A ＝ ⌜Σ⌝ ν' A'
  ⌜Σ⌝-＝ ν .ν refl A A' h = ap (⌜Σ⌝ ν) (dfunext (fe 𝓤₀ 𝓤₀) I)
   where
    I : A ∼ A'
    I x = A x               ＝⟨ ap A ((ρσ ν x)⁻¹) ⟩
          A (ρ ν (σ ν x))   ＝⟨ h (σ ν x) ⟩
          A' (ρ ν (σ ν x))  ＝⟨ ap A' (ρσ ν x) ⟩
          A' x              ∎

  e-lc : left-cancellable e
  e-lc {⌜𝟙⌝}     {⌜𝟙⌝}       p = refl
  e-lc {⌜ω+𝟙⌝}   {⌜ω+𝟙⌝}     p = refl
  e-lc {ν ⌜+⌝ μ} {ν' ⌜+⌝ μ'} p =
   ν  ⌜+⌝ μ  ＝⟨ ap (λ - → - ⌜+⌝ μ) (e-lc (φ (inl ⋆))) ⟩
   ν' ⌜+⌝ μ  ＝⟨ ap (λ - → ν' ⌜+⌝ -) (e-lc (φ (inr ⋆))) ⟩
   ν' ⌜+⌝ μ' ∎
    where
     φ = forest-＝ Fin-is-set p
  e-lc {ν ⌜×⌝ μ} {ν' ⌜×⌝ μ'} p =
   ν  ⌜×⌝ μ  ＝⟨ ap (λ - → - ⌜×⌝ μ) (e-lc (φ (inl ⋆))) ⟩
   ν' ⌜×⌝ μ  ＝⟨ ap (λ - → ν' ⌜×⌝ -) (e-lc (φ (inr ⋆))) ⟩
   ν' ⌜×⌝ μ' ∎
    where
     φ = forest-＝ Fin-is-set p
  e-lc {⌜Σ⌝ ν A} {⌜Σ⌝ ν' A'} p = ⌜Σ⌝-＝ ν ν'
                                  (e-lc (φ (inl ⋆)))
                                  A A'
                                  (λ n → e-lc (φ (inr n)))
   where
    φ = forest-＝ Fin-is-set p

\end{code}

Added 28th August 2026.

The compact ordinals Κ ν are not totally separated in general. This is
in contrast with the compact interpretation of the Brouwer codes, given
in Ordinals.BrouwerCodesDiscreteAndCompactInterpretations.

The reason is that the constructor ⌜Σ⌝ takes a sum, indexed by the
compact ordinal Κ ν, of a family extended along the dense embedding ι ν.
For the code ⌜ω+𝟙⌝ the discrete ordinal Δ ⌜ω+𝟙⌝ is ℕ + 𝟙 and the
embedding ι𝟙 sends the added point to ∞, so the extended family is
unconstrained at ∞, and we can make it two-valued there. This
reproduces the type ℕ∞₂ of TypeTopology.FailureOfTotalSeparatedness,
whose total separatedness gives ¬¬ WLPO.

Over the finite points of ω+1 we put the one-point ordinal, and over
the added point we put the two-point one.

\begin{code}

private
 A₂ : ⟨ Δ ⌜ω+𝟙⌝ ⟩ → E
 A₂ (inl n) = ⌜𝟙⌝
 A₂ (inr ⋆) = ⌜𝟙⌝ ⌜+⌝ ⌜𝟙⌝

⌜ℕ∞₂⌝ : E
⌜ℕ∞₂⌝ = ⌜Σ⌝ ⌜ω+𝟙⌝ A₂

\end{code}

By definition, the underlying type of Κ ⌜ℕ∞₂⌝ is the sum over ℕ∞ of the
extension of the above family along ι𝟙.

\begin{code}

_ : ⟨ Κ ⌜ℕ∞₂⌝ ⟩ ＝ (Σ u ꞉ ℕ∞ , (Π (d , _) ꞉ fiber ι𝟙 u , ⟨ Κ (A₂ d) ⟩))
_ = refl

\end{code}

This sum is the type ℕ∞₂, and so its total separatedness gives ¬¬ WLPO.

\begin{code}

Κ⌜ℕ∞₂⌝-totally-separated-gives-¬¬WLPO
 : is-totally-separated ⟨ Κ ⌜ℕ∞₂⌝ ⟩ → ¬¬ WLPO
Κ⌜ℕ∞₂⌝-totally-separated-gives-¬¬WLPO ts
 = III
 where
  F : ⟨ Δ ⌜ω+𝟙⌝ ⟩ → 𝓤₀ ̇
  F d = ⟨ Κ (A₂ d) ⟩

\end{code}

The two points over ∞ are those of the two-point ordinal, whose
underlying type is a sum over the two-element type, so that we identify
them with the booleans by cases.

\begin{code}

  I : F (inr ⋆) ≃ 𝟚
  I = qinveq f (g , gf , fg)
   where
    f : F (inr ⋆) → 𝟚
    f (inl ⋆ , ⋆) = ₀
    f (inr ⋆ , ⋆) = ₁

    g : 𝟚 → F (inr ⋆)
    g ₀ = inl ⋆ , ⋆
    g ₁ = inr ⋆ , ⋆

    gf : g ∘ f ∼ id
    gf (inl ⋆ , ⋆) = refl
    gf (inr ⋆ , ⋆) = refl

    fg : f ∘ g ∼ id
    fg ₀ = refl
    fg ₁ = refl

\end{code}

The fiber of ι𝟙 over a conatural number u splits into a finite part,
over which the family is a singleton, and the part over ∞, which is
where the two points live. So the fiber of the extension over u is the
type of functions from u ＝ ∞ to the booleans.

\begin{code}

  II : (u : ℕ∞) → (Π (d , _) ꞉ fiber ι𝟙 u , F d) ≃ (u ＝ ∞ → 𝟚)
  II u = (Π (d , _) ꞉ fiber ι𝟙 u , F d)             ≃⟨ II₀ ⟩
         (Π d ꞉ ℕ + 𝟙 , (ι𝟙 d ＝ u → F d))          ≃⟨ II₁ ⟩
         (Π n ꞉ ℕ , (ι𝟙 (inl n) ＝ u → F (inl n)))
         × (𝟙 → ∞ ＝ u → F (inr ⋆))                 ≃⟨ II₂ ⟩
         𝟙 × (∞ ＝ u → F (inr ⋆))                   ≃⟨ II₃ ⟩
         𝟙 × (u ＝ ∞ → 𝟚)                           ≃⟨ II₄ ⟩
         (u ＝ ∞ → 𝟚) ■
   where
    II₀ = curry-uncurry fe
    II₁ = ≃-sym (Π×+ fe₀)
    II₂ = ×-cong
           (singleton-≃-𝟙
            (Π-is-singleton fe₀
              (λ n → Π-is-singleton fe₀ (λ _ → 𝟙-is-singleton))))
           (≃-sym (𝟙→ fe₀))
    II₃ = ×-cong {𝓤₀} {𝓤₀} {𝓤₀}
           (≃-refl _)
           (→cong fe₀ fe₀ ＝-flip I)
    II₄ = 𝟙-lneutral

  𝕖 : ⟨ Κ ⌜ℕ∞₂⌝ ⟩ ≃ ℕ∞₂
  𝕖 = Σ-cong II

  III : ¬¬ WLPO
  III = ℕ∞₂-is-not-totally-separated-in-general
         (subtype-is-totally-separated''
           ⌜ 𝕖 ⌝⁻¹
           ts
           (equivs-are-lc ⌜ 𝕖 ⌝⁻¹ (⌜⌝⁻¹-is-equiv 𝕖)))

\end{code}

Hence the compact ordinals of the codes E are not totally separated in
general.

\begin{code}

Κ-totally-separated-gives-¬¬WLPO
 : ((ν : E) → is-totally-separated ⟨ Κ ν ⟩) → ¬¬ WLPO
Κ-totally-separated-gives-¬¬WLPO ts
 = Κ⌜ℕ∞₂⌝-totally-separated-gives-¬¬WLPO (ts ⌜ℕ∞₂⌝)

\end{code}

Added 2nd September 2026.

Every non-empty complemented subset of the compact interpretation has
a least element. For the discrete interpretation this exactly LPO, and
the code ⌜ω+𝟙⌝ alone witnesses one direction, its discrete
interpretation being ω + 1 by definition.

\begin{code}

K-has-least-roots-of-complemented-subsets
 : propext 𝓤₀
 → (ν : E) → has-least-roots-of-complemented-subsets (Κ ν)
K-has-least-roots-of-complemented-subsets pe ν =
 has-inf-gives-least-roots
  (underlying-weak-order (Κ ν))
  (K-has-infs-of-complemented-subsets pe ν)

Δ-least-roots-gives-LPO
 : ((ν : E) → has-least-roots-of-complemented-subsets (Δ ν))
 → LPO
Δ-least-roots-gives-LPO h = succₒ-ω-least-roots-gives-LPO (h ⌜ω+𝟙⌝)

LPO-gives-Δ-least-roots
 : propext 𝓤₀
 → LPO
 → (ν : E) → has-least-roots-of-complemented-subsets (Δ ν)
LPO-gives-Δ-least-roots pe lpo ν = ≃ₒ-gives-has-least-roots
                                    [ Κ ν ]
                                    [ Δ ν ]
                                    (≃ₒ-sym [ Δ ν ] [ Κ ν ] e)
                                    (K-has-least-roots-of-complemented-subsets
                                      pe ν)
 where
  e : [ Δ ν ] ≃ₒ [ Κ ν ]
  e = ι ν ,
      order-preserving-reflecting-equivs-are-order-equivs
       [ Δ ν ] [ Κ ν ] (ι ν)
       (LPO-gives-ι-is-equiv lpo ν)
       (ι-is-order-preserving ν)
       (ι-is-order-reflecting ν)

Δ-least-roots-iff-LPO
 : propext 𝓤₀
 → ((ν : E) → has-least-roots-of-complemented-subsets (Δ ν)) ↔ LPO
Δ-least-roots-iff-LPO pe = Δ-least-roots-gives-LPO ,
                           LPO-gives-Δ-least-roots pe

\end{code}
