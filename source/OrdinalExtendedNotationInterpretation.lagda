Martin Escardo, 1st March 2022

A Tarski universe E of ordinal codes with two related decoding
functions Δ and Κ (standing for "discrete" and "compact"
respectively).

Roughly speaking, E gives ordinal codes or expressions denoting
infinite ordinals. The expressions themselves are infinitary.

An ordinal is a type equipped with an order that _≺_ satisfies
suitable properties (which in particular implies that the type is a
set in the sense of HoTT/UF).

For a code ν : E, we have an ordinal Δ ν, which is discrete (has
decidable equality).

For a code ν : E, we have an ordinal Κ ν, which is searchable (or
compact). More than that, evey decidable subset of Κ ν is either empty
or has a minimal element.

There is an embedding ι : Δ ν → Κ ν which is order preserving and
reflecting, and whose image has empty complement. The assumption that
it is a bijection implies LPO.

The adopted notion of ordinal is that of the HoTT book.

This extends and generalizes OrdinalNotationInterpretation.lagda, for
which slides for a talk are available at
https://www.cs.bham.ac.uk/~mhe/.talks/csl2022.pdf which may well serve
as an introduction to this file. The main difference is that the
ordinal expressions considered there amount to a W type, where the
ones considered here amount to an inductive-recursive type,
generalizing that.

This is a draft version that needs polishing and more explanation.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalExtendedNotationInterpretation (fe : FunExt) where

fe₀ = fe 𝓤₀ 𝓤₀

open import ToppedOrdinalsType fe
open import OrdinalArithmetic fe
open import ToppedOrdinalArithmetic fe
open import OrdinalsClosure fe
open import DiscreteAndSeparated
open import GenericConvergentSequence
open import ConvergentSequenceHasLeast
open import PropInfTychonoff fe
open import BinaryNaturals hiding (_+_)

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Embeddings
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Miscelanea

\end{code}

We define E and Δ by simultaneous induction. The type Ordᵀ is that or
ordinals with a top element (classically, successor ordinals).

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
Δ-retract-of-ℕ (ν₀ ⌜×⌝ ν₁) = Σ-retract-of-ℕ (Δ-retract-of-ℕ ν₀) (λ _ → Δ-retract-of-ℕ ν₁)
Δ-retract-of-ℕ (⌜Σ⌝ ν A)   = Σ-retract-of-ℕ (Δ-retract-of-ℕ ν) (λ x → Δ-retract-of-ℕ (A x))

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

I : (ν : E) → ⟪ Δ ν ⟫ ↪ ⟪ Κ ν ⟫
I ν = (ι ν , ι-is-embedding ν)

\end{code}

We use the following auxiliary extension constructions:

\begin{code}

module Κ-extension (ν : E) (A : ⟪ Δ ν ⟫ → E) where

 open import InjectiveTypes fe

 B : ⟪ Κ ν ⟫ → Ordᵀ
 B = (Κ ∘ A) ↗ I ν

 ϕ : (x : ⟪ Δ ν ⟫) → ⟪ B (ι ν x) ⟫ ≃ ⟪ Κ (A x) ⟫
 ϕ = Π-extension-property (λ x → ⟪ Κ (A x) ⟫) (ι ν) (ι-is-embedding ν)

 φ : (x : ⟪ Δ ν ⟫) → ⟪ B (ι ν x) ⟫ → ⟪ Κ (A x) ⟫
 φ x = ⌜ ϕ x ⌝

 φ⁻¹ : (x : ⟪ Δ ν ⟫) → ⟪ Κ (A x) ⟫ → ⟪ B (ι ν x) ⟫
 φ⁻¹ x = ⌜ ϕ x ⌝⁻¹

 γ : (x : ⟪ Δ ν ⟫) → ⟪ Δ (A x) ⟫ → ⟪ B (ι ν x) ⟫
 γ x = φ⁻¹ x ∘ ι (A x)

 γ-is-embedding : (x : ⟪ Δ ν ⟫) → is-embedding (γ x)
 γ-is-embedding x = ∘-is-embedding
                     (ι-is-embedding (A x))
                     (equivs-are-embeddings _ (⌜⌝⁻¹-is-equiv (ϕ x)))

 canonical-fiber-point : (x : ⟪ Δ ν ⟫) → fiber (ι ν) (ι ν x)
 canonical-fiber-point x = (x , refl)

 ι-γ-lemma : (x : ⟪ Δ ν ⟫) (y : ⟪ Δ (A x) ⟫)
           → ι (A x) y ≡ γ x y (canonical-fiber-point x)
 ι-γ-lemma x = q
  where
   p : refl ≡ (ι-is-embedding ν (ι ν x) (x , refl) (x , refl))
   p = props-are-sets (ι-is-embedding ν (ι ν x)) _ _

   q : (y : ⟪ Δ (A x) ⟫) → ι (A x) y ≡ γ x y (x , refl)
   q y = ap (λ - → transport (λ (x , _) → ⟪ Κ (A x) ⟫) - (ι (A x) y)) p

Κ ⌜𝟙⌝         = 𝟙ᵒ
Κ ⌜ω+𝟙⌝       = ℕ∞ᵒ
Κ (ν₀ ⌜+⌝ ν₁) = Κ ν₀ +ᵒ Κ ν₁
Κ (ν₀ ⌜×⌝ ν₁) = Κ ν₀ ×ᵒ Κ ν₁
Κ (⌜Σ⌝ ν A)   = ∑ (Κ ν) B
 where
  open Κ-extension ν A

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
                             (dep-cases (λ _ → ι-is-embedding ν₀) (λ _ → ι-is-embedding ν₁))
ι-is-embedding (ν₀ ⌜×⌝ ν₁) = pair-fun-is-embedding _ _
                              (ι-is-embedding ν₀)
                              (λ _ → ι-is-embedding ν₁)
ι-is-embedding (⌜Σ⌝ ν A)   = pair-fun-is-embedding _ _
                              (ι-is-embedding ν)
                              γ-is-embedding
 where
  open Κ-extension ν A

\end{code}

The Κ interpretation gives ordinals such that every decidable subset
is either empty or has a least element (and so in particular these
ordinals are searchable, or compact):

\begin{code}

K-has-least-element-property : propext 𝓤₀ → (ν : E) → has-least-element-property (Κ ν)
K-has-least-element-property pe ⌜𝟙⌝         = 𝟙ᵒ-has-least-element-property
K-has-least-element-property pe ⌜ω+𝟙⌝       = ℕ∞ᵒ-has-least-element-property pe
K-has-least-element-property pe (ν₀ ⌜+⌝ ν₁) = ∑-has-least-element-property pe
                                               𝟚ᵒ
                                               (cases (λ _ → Κ ν₀) (λ _ → Κ ν₁))
                                               𝟚ᵒ-has-least-element-property
                                               (dep-cases (λ _ → K-has-least-element-property pe ν₀)
                                                          (λ _ → K-has-least-element-property pe ν₁))
K-has-least-element-property pe (ν₀ ⌜×⌝ ν₁) = ∑-has-least-element-property pe
                                               (Κ ν₀)
                                               (λ _ → Κ ν₁)
                                               (K-has-least-element-property pe ν₀)
                                               (λ _ → K-has-least-element-property pe ν₁)
K-has-least-element-property pe (⌜Σ⌝ ν A)   = ∑-has-least-element-property pe (Κ ν) B
                                               (K-has-least-element-property pe ν)
                                               (λ x → prop-inf-tychonoff
                                                       (ι-is-embedding ν x)
                                                       (λ {w} x y → x ≺⟪ Κ (A (pr₁ w)) ⟫ y)
                                                       (λ (x , _) → K-has-least-element-property pe (A x)))
 where
  open Κ-extension ν A

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
                                     B
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
    → ι (A x) y ≺⟪ Κ (A x) ⟫   ι (A x) z
    →     γ x y ≺⟪ B (ι ν x) ⟫     γ x z
  f x y z l = canonical-fiber-point x ,
              transport₂ (λ j k → j ≺⟪ Κ (A x) ⟫ k)
               (ι-γ-lemma x y)
               (ι-γ-lemma x z)
               l

  g : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    →     y ≺⟪ Δ (A x) ⟫       z
    → γ x y ≺⟪ B (ι ν x) ⟫ γ x z
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
                                    B
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
    →     γ x y ≺⟪ B (ι ν x) ⟫     γ x z
    → ι (A x) y ≺⟪ Κ (A x)   ⟫ ι (A x) z
  f x y z (w , l) = n
   where
    q : w ≡ canonical-fiber-point x
    q = ι-is-embedding ν (ι ν x) _ _

    m : γ x y (canonical-fiber-point x) ≺⟪ Κ (A x) ⟫  γ x z (canonical-fiber-point x)
    m = transport (λ (x' , p) → γ x y (x' , p) ≺⟪ Κ (A x') ⟫ γ x z (x' , p)) q l

    n : ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
    n = transport₂ (λ u v → u ≺⟪ Κ (A x) ⟫ v) ((ι-γ-lemma x y)⁻¹) ((ι-γ-lemma x z)⁻¹) m

  g : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → γ x y ≺⟪ B (ι ν x) ⟫ γ x z
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

We would like to have the following, but I don't think we do. However,
I like the following failed proof because it shows exactly where the
problem is if we follow the (successful) approach of the module
OrdinalExtendedNotation:

\begin{code}
{-
Κ-Cantor-retract : (ν : E) → retract ⟪ Κ ν ⟫ of (ℕ → 𝟚)
Κ-Cantor-retract ⌜𝟙⌝         =  (λ _ → ⋆) , (λ _ → λ n → ₀) , 𝟙-is-prop ⋆
Κ-Cantor-retract ⌜ω+𝟙⌝       = ℕ∞-retract-of-Cantor fe₀
Κ-Cantor-retract (ν₀ ⌜+⌝ ν₁) = +-retract-of-Cantor
                                 (Κ ν₀)
                                 (Κ ν₁)
                                 (Κ-Cantor-retract ν₀)
                                 (Κ-Cantor-retract ν₁)
Κ-Cantor-retract (ν₀ ⌜×⌝ ν₁) =  ×-retract-of-Cantor
                                 (Κ ν₀)
                                 (Κ ν₁)
                                 (Κ-Cantor-retract ν₀)
                                 (Κ-Cantor-retract ν₁)
Κ-Cantor-retract (⌜Σ⌝ ν A)   = g
 where
  open Κ-extension ν A

  i : retract ⟪ Κ ν ⟫ of (ℕ → 𝟚)
  i = Κ-Cantor-retract ν

  ii : (x : ⟪ Δ ν ⟫) → retract ⟪ Κ (A x) ⟫ of (ℕ → 𝟚)
  ii x = Κ-Cantor-retract (A x)

  s : (y : ⟪ Κ ν ⟫) → retract ⟪ B y ⟫ of ((λ _ → ℕ → 𝟚) / ι ν) y
  s y = retract-extension (λ - → ⟪ Κ (A -) ⟫) (λ _ → ℕ → 𝟚) (ι ν) ii y

  r : retract (Σ y ꞉ ⟪ Κ ν ⟫ , ⟪ B y ⟫) of (Σ y ꞉ ⟪ Κ ν ⟫ , (fiber (ι ν) y → ℕ → 𝟚))
  r = Σ-retract ((λ x → ⟪ Κ (A x) ⟫) / ι ν) ((λ _ → ℕ → 𝟚) / ι ν) s

  t : retract (Σ y ꞉ ⟪ Κ ν ⟫ , (fiber (ι ν) y → ℕ → 𝟚))
      of (Σ α ꞉ (ℕ → 𝟚) , ((fiber (ι ν) (retraction i α)) → ℕ → 𝟚))
  t = Σ-reindex-retract' i

  u : retract (Σ y ꞉ ⟪ Κ ν ⟫ , ⟪ B y ⟫) of (Σ α ꞉ (ℕ → 𝟚) , ((fiber (ι ν) (retraction i α)) → ℕ → 𝟚))
  u = retracts-compose t r

  unlikely : retract (Σ α ꞉ (ℕ → 𝟚) , ((fiber (ι ν) (retraction i α)) → ℕ → 𝟚)) of (ℕ → 𝟚)
  unlikely = {!!}

  h : retract (Σ y ꞉ ⟪ Κ ν ⟫ , ⟪ B y ⟫) of (ℕ → 𝟚)
  h = retracts-compose unlikely u

  g : retract ⟪ ∑ (Κ ν) B ⟫ of (ℕ → 𝟚)
  g = h
-}
\end{code}

In the file OrdinalNotationInterpretation.lagda, which is less general
that this one, this proof idea succeeds. And the proof is quite
complicated (with the difficult lemmas provided in other files).

TODO. Derive a taboo from the hypothesis that the above could be
proved. This should be easy using the file
FailureOfTotalSeparatedness.lagda.
