Martin Escardo, 1st March 2022

This extends OrdinalNotationInterpretation.lagda.

This is a draft version that needs polishing.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module OrdinalExtendedNotationInterpretation (fe : FunExt) where

open import ToppedOrdinalsType fe
open import OrdinalArithmetic fe
open import ToppedOrdinalArithmetic fe
open import OrdinalsClosure fe
open import DiscreteAndSeparated
open import InjectiveTypes fe
open import GenericConvergentSequence
open import ConvergentSequenceHasLeast
open import PropInfTychonoff fe

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Embeddings
open import UF-Equiv
open import UF-Subsingletons-FunExt

\end{code}

We define E and Δ by simultaneous induction:

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

And now we define Κ, ι, ι-is-embedding by simultaneous
induction, using the above definitions:

\begin{code}

Κ : E → Ordᵀ
ι : (ν : E) → ⟪ Δ ν ⟫ → ⟪ Κ ν ⟫
ι-is-embedding : (ν : E) → is-embedding (ι ν)

I : (ν : E) → ⟪ Δ ν ⟫ ↪ ⟪ Κ ν ⟫
I ν = (ι ν , ι-is-embedding ν)

module _ (ν : E) (A : ⟪ Δ ν ⟫ → E) where

 ψ : ⟪ Κ ν ⟫ → Ordᵀ
 ψ = (Κ ∘ A) ↗ I ν

 ϕ : (x : ⟪ Δ ν ⟫) → ((λ x → ⟪ Κ (A x) ⟫) / (ι ν)) (ι ν x) ≃ ⟪ Κ (A x) ⟫
 ϕ = Π-extension-property (λ x → ⟪ Κ (A x) ⟫) (ι ν) (ι-is-embedding ν)

 φ : (x : ⟪ Δ ν ⟫) → ⟪ ψ (ι ν x) ⟫ → ⟪ Κ (A x) ⟫
 φ x = ⌜ ϕ x ⌝

 φ⁻¹ : (x : ⟪ Δ ν ⟫) → ⟪ Κ (A x) ⟫ → ⟪ ψ (ι ν x) ⟫
 φ⁻¹ x = ⌜ ϕ x ⌝⁻¹

 εφ : (x : ⟪ Δ ν ⟫) → φ x ∘ φ⁻¹ x ∼ id
 εφ x = inverses-are-sections (φ x) (⌜⌝-is-equiv (ϕ x))

 γ : (x : ⟪ Δ ν ⟫) → ⟪ Δ (A x) ⟫ → ⟪ ψ (ι ν x) ⟫
 γ x = φ⁻¹ x ∘ ι (A x)

 γ-is-embedding : (x : ⟪ Δ ν ⟫) → is-embedding (γ x)
 γ-is-embedding x = ∘-is-embedding
                     (ι-is-embedding (A x))
                     (equivs-are-embeddings _ (⌜⌝⁻¹-is-equiv (ϕ x)))

 ι-γ-lemma : (x : ⟪ Δ ν ⟫) (y : ⟪ Δ (A x) ⟫)
           → ι (A x) y ≡ γ x y (x , refl)
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
Κ (⌜Σ⌝ ν A)   = ∑ (Κ ν) (ψ ν A)

ι ⌜𝟙⌝         = id
ι ⌜ω+𝟙⌝       = ι𝟙
ι (ν₀ ⌜+⌝ ν₁) = pair-fun id (dep-cases (λ _ → ι ν₀) (λ _ → ι ν₁))
ι (ν₀ ⌜×⌝ ν₁) = pair-fun (ι ν₀) (λ _ → ι ν₁)
ι (⌜Σ⌝ ν A)   = pair-fun (ι ν) (γ ν A)

ι-is-embedding ⌜𝟙⌝         = id-is-embedding
ι-is-embedding ⌜ω+𝟙⌝       = ι𝟙-is-embedding (fe 𝓤₀ 𝓤₀)
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
                              (γ-is-embedding ν A)
\end{code}

The Κ interpretation gives ordinals such that every decidable subset
is either empty or has a least element:

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
K-has-least-element-property pe (⌜Σ⌝ ν A)   = ∑-has-least-element-property pe (Κ ν)
                                               (ψ ν A)
                                               (K-has-least-element-property pe ν)
                                               (λ x → prop-inf-tychonoff
                                                       (ι-is-embedding ν x)
                                                       (λ {w} x y → x ≺⟪ Κ (A (pr₁ w)) ⟫ y)
                                                       (λ (x , _) → K-has-least-element-property pe (A x)))
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
                                     (λ x → Δ (A x))
                                     (ψ ν A)
                                     (ι ν)
                                     (γ ν A)
                                     (ι-is-order-preserving ν)
                                     g
 where
  IH : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
     → y ≺⟪ Δ (A x) ⟫ z
     → ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
  IH x = ι-is-order-preserving (A x)

  f : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
    → γ ν A x y ≺⟪ ψ ν A (ι ν x) ⟫ γ ν A x z
  f x y z l = (x , refl) ,
              transport₂ (λ j k → j ≺⟪ Κ (A x) ⟫ k)
               (ι-γ-lemma ν A x y)
               (ι-γ-lemma ν A x z) l

  g : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → y ≺⟪ Δ (A x) ⟫ z
    → γ ν A x y ≺⟪ ψ ν A (ι ν x) ⟫ γ ν A x z
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
                                    (λ x → Δ (A x))
                                    (ψ ν A)
                                    (ι ν)
                                    (γ ν A)
                                    (ι-is-order-reflecting ν)
                                    (ι-is-embedding ν)
                                    g
 where
  IH : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
     → ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
     → y ≺⟪ Δ (A x) ⟫ z
  IH x = ι-is-order-reflecting (A x)

  f : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → γ ν A x y ≺⟪ ψ ν A (ι ν x) ⟫ γ ν A x z
    → ι (A x) y ≺⟪ Κ (A x) ⟫ ι (A x) z
  f x y z ((x' , p) , l) = n
   where
    q : (x' , p) ≡ (x , refl)
    q = ι-is-embedding ν (ι ν x) _ _

    m : φ⁻¹ ν A x  (ι (A x) y) (x , refl) ≺⟪ Κ (A x) ⟫  φ⁻¹ ν A x (ι (A x) z) (x , refl)
    m = transport (λ (x' , p) → γ ν A x y (x' , p) ≺⟪ Κ (A x') ⟫ γ ν A x z (x' , p)) q l

    n : ι (A x) y ≺⟪ Κ (A x) ⟫  ι (A x) z
    n = transport₂ (λ u v → u ≺⟪ Κ (A x) ⟫ v) ((ι-γ-lemma ν A x y)⁻¹) ((ι-γ-lemma ν A x z)⁻¹) m

  g : (x : ⟪ Δ ν ⟫) (y z : ⟪ Δ (A x) ⟫)
    → γ ν A x y ≺⟪ ψ ν A (ι ν x) ⟫ γ ν A x z
    → y ≺⟪ Δ (A x) ⟫ z
  g x y z l = IH x y z (f x y z l)

ι-is-dense : (ν : E) → is-dense (ι ν)
ι-is-dense ⌜𝟙⌝         = id-is-dense
ι-is-dense ⌜ω+𝟙⌝       = ι𝟙-dense (fe 𝓤₀ 𝓤₀)
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
                          (γ ν A)
                          (ι-is-dense ν)
                          (λ x → comp-is-dense
                                  (ι-is-dense (A x))
                                  (equivs-are-dense
                                    (φ⁻¹ ν A x)
                                    (inverses-are-equivs (φ ν A x) (⌜⌝-is-equiv (ϕ ν A x)))))
\end{code}
