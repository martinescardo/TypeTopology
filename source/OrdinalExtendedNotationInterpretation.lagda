Martin Escardo, March 2022

This generalizes the 2018 file OrdinalNotationInterpretation.

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

This extends and generalizes OrdinalNotationInterpretation.lagda, for
which slides for a talk are available at
https://www.cs.bham.ac.uk/~mhe/.talks/csl2022.pdf which may well serve
as an introduction to this file. The main difference is that the
ordinal expressions considered there amount to a W type, whereas the
ones considered here amount to an inductive-recursive type,
generalizing that.

This is a draft version that needs polishing and more explanation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalExtendedNotationInterpretation (fe : FunExt) where

private
 fe₀ = fe 𝓤₀ 𝓤₀

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Embeddings
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Miscelanea

open import SigmaDiscreteAndTotallySeparated
open import ToppedOrdinalsType fe
open import OrdinalArithmetic fe
open import ToppedOrdinalArithmetic fe
open import OrdinalsClosure fe
open import DiscreteAndSeparated
open import GenericConvergentSequence
open import ConvergentSequenceHasLeast
open import PropTychonoff fe
open import PropInfTychonoff fe
open import BinaryNaturals hiding (_+_)
open import Two-Properties
open import CompactTypes
open import LeastElementProperty
open import WLPO
open import LPO fe
open import Density
open import PairFun

\end{code}

We define E and Δ by simultaneous induction. The type Ordᵀ is that of
ordinals with a top element (classically, successor ordinals). Recall
that ⟪ α ⟫ is the underlying type of α : Ordᵀ.

\begin{code}

data E : 𝓤₀ ̇
Δ : E → Ordᵀ

data E where
 ⌜𝟙⌝     : E
 ⌜ω+𝟙⌝   : E
 _⌜+⌝_   : E → E → E
 _⌜×⌝_   : E → E → E
 ⌜Σ⌝     : (ν : E) → (⟪ Δ ν ⟫ → E) → E

Δ ⌜𝟙⌝         = 𝟙ᵒ
Δ ⌜ω+𝟙⌝       = succₒ ℕₒ
Δ (ν₀ ⌜+⌝ ν₁) = Δ ν₀ +ᵒ Δ ν₁
Δ (ν₀ ⌜×⌝ ν₁) = Δ ν₀ ×ᵒ Δ ν₁
Δ (⌜Σ⌝ ν A)   = ∑ (Δ ν) (Δ ∘ A)

\end{code}

All ordinals in the image of Δ are retracts of ℕ.

\begin{code}

Δ-retract-of-ℕ : (ν : E) → retract ⟪ Δ ν ⟫ of ℕ
Δ-retract-of-ℕ ⌜𝟙⌝         = (λ _ → ⋆) , (λ _ → 0) , 𝟙-is-prop ⋆
Δ-retract-of-ℕ ⌜ω+𝟙⌝       = ≃-gives-◁ ℕ-plus-𝟙
Δ-retract-of-ℕ (ν₀ ⌜+⌝ ν₁) = Σ-retract-of-ℕ
                              retract-𝟙+𝟙-of-ℕ
                              (dep-cases (λ _ → Δ-retract-of-ℕ ν₀)
                                         (λ _ → Δ-retract-of-ℕ ν₁))
Δ-retract-of-ℕ (ν₀ ⌜×⌝ ν₁) = Σ-retract-of-ℕ
                              (Δ-retract-of-ℕ ν₀)
                              (λ _ → Δ-retract-of-ℕ ν₁)
Δ-retract-of-ℕ (⌜Σ⌝ ν A)   = Σ-retract-of-ℕ
                              (Δ-retract-of-ℕ ν)
                              (λ x → Δ-retract-of-ℕ (A x))
\end{code}

Hence all ordinals in the image of Δ are discrete (have decidable equality):

\begin{code}

Δ-is-discrete : (ν : E) → is-discrete ⟪ Δ ν ⟫
Δ-is-discrete ν = retract-is-discrete (Δ-retract-of-ℕ ν) ℕ-is-discrete

\end{code}

And now we define Κ, ι, ι-is-embedding by simultaneous
induction:

\begin{code}

Κ : E → Ordᵀ
ι : (ν : E) → ⟪ Δ ν ⟫ → ⟪ Κ ν ⟫
ι-is-embedding : (ν : E) → is-embedding (ι ν)

\end{code}

We use the following auxiliary extension constructions:

\begin{code}

𝓚 : (ν : E) → (⟪ Δ ν ⟫ → E) → ⟪ Κ ν ⟫ → Ordᵀ
𝓚 ν A = (Κ ∘ A) ↗ (ι ν , ι-is-embedding ν)

module Κ-extension (ν : E) (A : ⟪ Δ ν ⟫ → E) where

 open import InjectiveTypes fe

 ϕ : (x : ⟪ Δ ν ⟫) → ⟪ 𝓚 ν A (ι ν x) ⟫ ≃ ⟪ Κ (A x) ⟫
 ϕ = Π-extension-property (λ x → ⟪ Κ (A x) ⟫) (ι ν) (ι-is-embedding ν)

 φ : (x : ⟪ Δ ν ⟫) → ⟪ 𝓚 ν A (ι ν x) ⟫ → ⟪ Κ (A x) ⟫
 φ x = ⌜ ϕ x ⌝

 φ⁻¹ : (x : ⟪ Δ ν ⟫) → ⟪ Κ (A x) ⟫ → ⟪ 𝓚 ν A (ι ν x) ⟫
 φ⁻¹ x = ⌜ ϕ x ⌝⁻¹

 γ : (x : ⟪ Δ ν ⟫) → ⟪ Δ (A x) ⟫ → ⟪ 𝓚 ν A (ι ν x) ⟫
 γ x = φ⁻¹ x ∘ ι (A x)

 γ-is-embedding : (x : ⟪ Δ ν ⟫) → is-embedding (γ x)
 γ-is-embedding x = ∘-is-embedding
                     (ι-is-embedding (A x))
                     (equivs-are-embeddings _ (⌜⌝⁻¹-is-equiv (ϕ x)))

 ι-fiber-point : (x : ⟪ Δ ν ⟫) → fiber (ι ν) (ι ν x)
 ι-fiber-point x = (x , refl)

 notice-that : (x : ⟪ Δ ν ⟫) (y : ⟪ Δ (A x) ⟫)
             → φ x (γ x y) ≡ γ x y (ι-fiber-point x)
 notice-that x y = refl

 ι-γ-lemma : (x : ⟪ Δ ν ⟫) (y : ⟪ Δ (A x) ⟫)
           → ι (A x) y ≡ φ x (γ x y)
 ι-γ-lemma x y =
  ι (A x) y               ≡⟨ (inverses-are-sections (φ x)
                               (⌜⌝-is-equiv (ϕ x)) (ι (A x) y))⁻¹ ⟩
  φ x (φ⁻¹ x (ι (A x) y)) ≡⟨ refl ⟩
  φ x (γ x y)             ∎

 isolated-γ-gives-isolated-ι : (x : ⟪ Δ ν ⟫) (y : ⟪ Δ (A x) ⟫)
                             → is-isolated (γ x y) → is-isolated (ι (A x) y)
 isolated-γ-gives-isolated-ι x y i = iii
   where
    ii : is-isolated (φ x (γ x y))
    ii = equivs-preserve-isolatedness (φ x) (⌜⌝-is-equiv (ϕ x)) (γ x y) i

    iii : is-isolated (ι (A x) y)
    iii = transport is-isolated ((ι-γ-lemma x y)⁻¹) ii

Κ ⌜𝟙⌝         = 𝟙ᵒ
Κ ⌜ω+𝟙⌝       = ℕ∞ᵒ
Κ (ν₀ ⌜+⌝ ν₁) = Κ ν₀ +ᵒ Κ ν₁
Κ (ν₀ ⌜×⌝ ν₁) = Κ ν₀ ×ᵒ Κ ν₁
Κ (⌜Σ⌝ ν A)   = ∑ (Κ ν) (𝓚 ν A)

ι ⌜𝟙⌝         = id
ι ⌜ω+𝟙⌝       = ι𝟙
ι (ν₀ ⌜+⌝ ν₁) = pair-fun id (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
ι (ν₀ ⌜×⌝ ν₁) = pair-fun (ι ν₀) (λ _ → ι ν₁)
ι (⌜Σ⌝ ν A)   = pair-fun (ι ν) γ
 where
  open Κ-extension ν A

ι-is-embedding ⌜𝟙⌝         = id-is-embedding
ι-is-embedding ⌜ω+𝟙⌝       = ι𝟙-is-embedding fe₀
ι-is-embedding (ν₀ ⌜+⌝ ν₁) = pair-fun-is-embedding
                              id
                              (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                              id-is-embedding
                              (dep-cases (λ _ → ι-is-embedding ν₀)
                                         (λ _ → ι-is-embedding ν₁))
ι-is-embedding (ν₀ ⌜×⌝ ν₁) = pair-fun-is-embedding _ _
                              (ι-is-embedding ν₀)
                              (λ _ → ι-is-embedding ν₁)
ι-is-embedding (⌜Σ⌝ ν A)   = pair-fun-is-embedding _ _
                              (ι-is-embedding ν)
                              γ-is-embedding
 where
  open Κ-extension ν A

\end{code}

This completes the definitions of Κ, ι and ι-is-embedding.

The important fact about the Κ interpretation is that the ordinals in
its image have the least element property for decidable subsets, and,
in particular, they are compact.

\begin{code}

module _ (pe : propext 𝓤₀) where

 K-has-least-element-property : (ν : E)
                              → has-least-element-property (Κ ν)
 𝓚-has-least-element-property : (ν : E) (A : ⟪ Δ ν ⟫ → E) (x : ⟪ Κ ν ⟫)
                              → has-least-element-property (𝓚 ν A x)

 K-has-least-element-property ⌜𝟙⌝         = 𝟙ᵒ-has-least-element-property
 K-has-least-element-property ⌜ω+𝟙⌝       = ℕ∞ᵒ-has-least-element-property pe
 K-has-least-element-property (ν₀ ⌜+⌝ ν₁) =
   ∑-has-least-element-property pe
     𝟚ᵒ
     (cases (λ _ → Κ ν₀) (λ _ → Κ ν₁))
     𝟚ᵒ-has-least-element-property
     (dep-cases (λ _ → K-has-least-element-property ν₀)
                (λ _ → K-has-least-element-property ν₁))
 K-has-least-element-property (ν₀ ⌜×⌝ ν₁) =
   ∑-has-least-element-property pe
     (Κ ν₀)
     (λ _ → Κ ν₁)
     (K-has-least-element-property ν₀)
     (λ _ → K-has-least-element-property ν₁)
 K-has-least-element-property (⌜Σ⌝ ν A)   =
   ∑-has-least-element-property pe (Κ ν) (𝓚 ν A)
     (K-has-least-element-property ν)
     (𝓚-has-least-element-property ν A)

 𝓚-has-least-element-property ν A x =
   prop-inf-tychonoff
    (ι-is-embedding ν x)
    (λ {(x , _)} y z → y ≺⟪ Κ (A x) ⟫ z)
    (λ (x , _) → K-has-least-element-property (A x))

 Κ-Compact : {𝓥 : Universe} (ν : E) → Compact ⟪ Κ ν ⟫ {𝓥}
 Κ-Compact ν = has-least-gives-Compact _ (K-has-least-element-property ν)

 𝓚-Compact : {𝓥 : Universe} (ν : E) (A : ⟪ Δ ν ⟫ → E) (x : ⟪ Κ ν ⟫)
            → Compact ⟪ 𝓚 ν A x ⟫ {𝓥}
 𝓚-Compact ν A x = has-least-gives-Compact _ (𝓚-has-least-element-property ν A x)

\end{code}

The embedding of the Δ interpretation into the Κ interpretation is
order-preserving, order-reflecting, and dense (its image has empty
complement):

\begin{code}

ι-is-order-preserving : (ν : E) (x y : ⟪ Δ ν ⟫)
                      →     x ≺⟪ Δ ν ⟫     y
                      → ι ν x ≺⟪ Κ ν ⟫ ι ν y
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
                                     (dep-cases (λ _ → ι-is-order-preserving ν₀)
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
                                     γ
                                     (ι-is-order-preserving ν)
                                     g
 where
  open Κ-extension ν A

  IH : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
     →         y ≺⟪ Δ (A x) ⟫ z
     → ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
  IH x = ι-is-order-preserving (A x)

  f : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → ι (A x) y ≺⟪ Κ (A x) ⟫        ι (A x) z
    →     γ x y ≺⟪ 𝓚 ν A (ι ν x) ⟫     γ x z
  f x y z l = (ι-fiber-point x ,
              transport₂ (λ j k → j ≺⟪ Κ (A x) ⟫ k)
               (ι-γ-lemma x y)
               (ι-γ-lemma x z)
              l)

  g : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    →     y ≺⟪ Δ (A x) ⟫            z
    → γ x y ≺⟪ 𝓚 ν A (ι ν x) ⟫ γ x z
  g x y z l = f x y z (IH x y z l)


ι-is-order-reflecting : (ν : E) (x y : ⟪ Δ ν ⟫)
                      → ι ν x ≺⟪ Κ ν ⟫ ι ν y
                      →     x ≺⟪ Δ ν ⟫     y
ι-is-order-reflecting ⌜𝟙⌝        = λ x y l → l
ι-is-order-reflecting ⌜ω+𝟙⌝      = ι𝟙ᵒ-is-order-reflecting
ι-is-order-reflecting (ν₀ ⌜+⌝ ν₁) =  pair-fun-is-order-reflecting
                                      𝟚ᵒ
                                      𝟚ᵒ
                                      (cases (λ _ → Δ ν₀) (λ _ → Δ ν₁))
                                      (cases (λ _ → Κ ν₀) (λ _ → Κ ν₁))
                                      id
                                      (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
                                      (λ x y l → l)
                                      id-is-embedding
                                      (dep-cases (λ _ → ι-is-order-reflecting ν₀)
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
                                    γ
                                    (ι-is-order-reflecting ν)
                                    (ι-is-embedding ν)
                                    g
 where
  open Κ-extension ν A

  IH : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
     → ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
     →         y ≺⟪ Δ (A x) ⟫         z
  IH x = ι-is-order-reflecting (A x)

  f : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    →     γ x y ≺⟪ 𝓚 ν A (ι ν x) ⟫    γ x z
    → ι (A x) y ≺⟪ Κ (A x)   ⟫     ι (A x) z
  f x y z (w , l) = n
   where
    q : w ≡ ι-fiber-point x
    q = ι-is-embedding ν (ι ν x) _ _

    m : γ x y (ι-fiber-point x) ≺⟪ Κ (A x) ⟫  γ x z (ι-fiber-point x)
    m = transport (λ (x' , p) → γ x y (x' , p) ≺⟪ Κ (A x') ⟫ γ x z (x' , p)) q l

    n : ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
    n = transport₂ (λ u v → u ≺⟪ Κ (A x) ⟫ v)
         ((ι-γ-lemma x y)⁻¹)
         ((ι-γ-lemma x z)⁻¹)
         m

  g : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → γ x y ≺⟪ 𝓚 ν A (ι ν x) ⟫ γ x z
    →     y ≺⟪ Δ (A x)   ⟫     z
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
                          γ
                          (ι-is-dense ν)
                          (λ x → comp-is-dense
                                  (ι-is-dense (A x))
                                  (equivs-are-dense
                                    (φ⁻¹ x)
                                    (inverses-are-equivs (φ x) (⌜⌝-is-equiv (ϕ x)))))
 where
  open Κ-extension ν A

\end{code}

We define limit points as follows:

\begin{code}

private
 recall-notion-of-isolatedness  : {X : 𝓤 ̇ } (x : X)
                                → is-isolated x ≡ ((y : X) → decidable (x ≡ y))
 recall-notion-of-isolatedness x = refl

is-limit-point : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-limit-point x = is-isolated x → WLPO

\end{code}

The characteristic function of limit points:

\begin{code}

ℓ : (ν : E) → ⟪ Δ ν ⟫ → 𝟚
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

ℓ-isolated : (ν : E) (x : ⟪ Δ ν ⟫) → ℓ ν x ≡ ₀ → is-isolated (ι ν x)
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

  iii : is-isolated (γ x y)
  iii = equivs-preserve-isolatedness (φ⁻¹ x) (⌜⌝⁻¹-is-equiv (ϕ x)) (ι (A x) y) ii

  iv : is-isolated (ι ν x , γ x y)
  iv = Σ-isolated i iii

\end{code}

The function ℓ really does detect limit points:

\begin{code}

module _ (pe : propext 𝓤₀) where

 ℓ-limit : (ν : E) (x : ⟪ Δ ν ⟫) → ℓ ν x ≡ ₁ → is-limit-point (ι ν x)
 ℓ-limit ⌜ω+𝟙⌝       (inr ⋆)      p i = is-isolated-gives-is-isolated' ∞ i
 ℓ-limit (ν₀ ⌜+⌝ ν₁) (inl ⋆ , x₀) p i = ℓ-limit ν₀ x₀ p
                                         (Σ-isolated-right
                                           (underlying-type-is-setᵀ fe 𝟚ᵒ) i)
 ℓ-limit (ν₀ ⌜+⌝ ν₁) (inr ⋆ , x₁) p i = ℓ-limit ν₁ x₁ p
                                         (Σ-isolated-right
                                           (underlying-type-is-setᵀ fe 𝟚ᵒ) i)
 ℓ-limit (ν₀ ⌜×⌝ ν₁) (x₀ , x₁)    p i =
   Cases (max𝟚-lemma p)
    (λ (p₀ : ℓ ν₀ x₀ ≡ ₁) → ℓ-limit ν₀ x₀ p₀ (×-isolated-left i))
    (λ (p₁ : ℓ ν₁ x₁ ≡ ₁) → ℓ-limit ν₁ x₁ p₁ (×-isolated-right i))
 ℓ-limit (⌜Σ⌝ ν A)   (x , y)      p i =
   Cases (max𝟚-lemma p)
    (λ (p₀ : ℓ ν x ≡ ₁)
           → ℓ-limit ν x p₀ (Σ-isolated-left (𝓚-Compact pe ν A) i))
    (λ (p₁ : ℓ (A x) y ≡ ₁)
           → ℓ-limit (A x) y p₁
              (isolated-γ-gives-isolated-ι x y
                (Σ-isolated-right
                  (underlying-type-is-setᵀ fe (Κ ν)) i)))
  where
   open Κ-extension ν A

 isolatedness-decision : (ν : E) (x : ⟪ Δ ν ⟫)
                       → is-isolated (ι ν x) + is-limit-point (ι ν x)
 isolatedness-decision ν x = 𝟚-equality-cases
                              (λ (p : ℓ ν x ≡ ₀) → inl (ℓ-isolated ν x p))
                              (λ (p : ℓ ν x ≡ ₁) → inr (ℓ-limit ν x p))

 isolatedness-decision' : ¬ WLPO → (ν : E) (x : ⟪ Δ ν ⟫)
                        → decidable (is-isolated (ι ν x))
 isolatedness-decision' f ν x =
   Cases (isolatedness-decision ν x)
    inl
    (λ (g : is-isolated (ι ν x) → WLPO)  → inr (contrapositive g f))

\end{code}

We conclude with some impossibility results.

\begin{code}

ι-is-equiv-gives-LPO : ((ν : E) → is-equiv (ι ν)) → LPO
ι-is-equiv-gives-LPO f = ι𝟙-is-equiv-gives-LPO (f ⌜ω+𝟙⌝)

LPO-gives-ι-is-equiv : LPO → (ν : E) → is-equiv (ι ν)
LPO-gives-ι-is-equiv lpo ⌜𝟙⌝         = id-is-equiv 𝟙
LPO-gives-ι-is-equiv lpo ⌜ω+𝟙⌝       = LPO-gives-ι𝟙-is-equiv lpo
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
                                          γ
                                          (LPO-gives-ι-is-equiv lpo ν)
                                          (λ x → ∘-is-equiv
                                                  (LPO-gives-ι-is-equiv lpo (A x))
                                                  (⌜⌝⁻¹-is-equiv (ϕ x)))
 where
  open Κ-extension ν A

ι-is-equiv-iff-LPO : ((ν : E) → is-equiv (ι ν)) ⇔ LPO
ι-is-equiv-iff-LPO = ι-is-equiv-gives-LPO , LPO-gives-ι-is-equiv

\end{code}

We also have the following:

\begin{code}

ι-has-section-gives-Κ-discrete : (ν : E) → has-section (ι ν) → is-discrete ⟪ Κ ν ⟫
ι-has-section-gives-Κ-discrete ν (θ , ιθ) = lc-maps-reflect-discreteness θ
                                              (sections-are-lc θ (ι ν , ιθ))
                                              (Δ-is-discrete ν)

ι-is-equiv-gives-Κ-discrete : (ν : E) → is-equiv (ι ν) → is-discrete ⟪ Κ ν ⟫
ι-is-equiv-gives-Κ-discrete ν e = ι-has-section-gives-Κ-discrete ν
                                   (equivs-have-sections (ι ν) e)

LPO-gives-Κ-discrete : LPO → (ν : E) → is-discrete ⟪ Κ ν ⟫
LPO-gives-Κ-discrete lpo ν = ι-is-equiv-gives-Κ-discrete ν
                              (LPO-gives-ι-is-equiv lpo ν)

Κ-discrete-gives-WLPO : ((ν : E) → is-discrete ⟪ Κ ν ⟫) → WLPO
Κ-discrete-gives-WLPO f = ℕ∞-discrete-gives-WLPO (f ⌜ω+𝟙⌝)

\end{code}

TODO. Can we close the gap between the last two facts? The difficulty
that arises here is similar to the following.

Let P be a proposition and assume function extensionality.

(0) If P is decidable, then the function type (P → 𝟚) has decidable equality.

(1) If (P → 𝟚) has decidable equality, then ¬ P is decidable.

It doesn't seem to be possible to reverse any of the implications (0)
and (1), so that the proposition "(P -> 2) has decidable equality"
seems to be strictly between "P is decidable" and "¬P is decidable".
