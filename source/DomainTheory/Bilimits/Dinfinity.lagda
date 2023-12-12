Tom de Jong, 12 May 2020 - 9 June 2020.

We construct Scott's famous nontrivial pointed dcpo D∞ for which D∞ is
isomorphic to its own function space and prove that it is algebraic.

The construction of D∞ is based on Scott's "Continuous lattices"
(doi:10.1007/BFB0073967), specifically pages 126--128.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

\end{code}

We use the flag --lossy-unification to speed up the type-checking.

This flag was kindly implemented by Andrea Vezzosi upon request.

Documentation for the flag (written by Andrea Vezzosi) can be found here:
https://agda.readthedocs.io/en/latest/language/lossy-unification.html

The most important takeaway from the documentation is that the flag is sound:

  "[...] if Agda accepts code with the flag enabled it should also accept it
  without the flag (with enough resources, and possibly needing extra type
  annotations)."

A related issue (originally opened by Wolfram Kahl in 2015) can be found here:
https://github.com/agda/agda/issues/1625

\begin{code}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DomainTheory.Bilimits.Dinfinity
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open PropositionalTruncation pt

open import UF.Base
open import UF.Subsingletons-Properties

open import DomainTheory.Basics.Dcpo pt fe 𝓤₀
open import DomainTheory.Basics.Exponential pt fe 𝓤₀
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀
open import DomainTheory.Basics.Pointed pt fe 𝓤₀
open import DomainTheory.Bilimits.Sequential pt fe 𝓤₁ 𝓤₁
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe

open import Naturals.Order hiding (subtraction')
open import Naturals.Addition renaming (_+_ to _+'_)
open import Notation.Order

\end{code}

We start by defining the ℕ-indexed diagram of iterated exponentials.

\begin{code}

𝓓⊥ : ℕ → DCPO⊥ {𝓤₁} {𝓤₁}
𝓓⊥ zero     = 𝓛-DCPO⊥ {𝓤₀} {𝟙{𝓤₀}} (props-are-sets 𝟙-is-prop)
𝓓⊥ (succ n) = 𝓓⊥ n ⟹ᵈᶜᵖᵒ⊥ 𝓓⊥ n

𝓓 : ℕ → DCPO {𝓤₁} {𝓤₁}
𝓓 n = pr₁ (𝓓⊥ n)

𝓓-diagram : (n : ℕ)
          → DCPO[ 𝓓 n , 𝓓 (succ n) ]
          × DCPO[ 𝓓 (succ n) , 𝓓 n ]
𝓓-diagram zero = (e₀ , e₀-continuity) , p₀ , p₀-continuity
 where
  e₀ : ⟨ 𝓓 0 ⟩ → ⟨ 𝓓 1 ⟩
  e₀ x = (λ y → x) , (constant-functions-are-continuous (𝓓 0) (𝓓 0))
  e₀-continuity : is-continuous (𝓓 0) (𝓓 1) e₀
  e₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → e₀ (α i) ⊑⟨ (𝓓 1) ⟩ e₀ (∐ (𝓓 0) δ)
    ub i y =  α i          ⊑⟨ 𝓓 0 ⟩[ ∐-is-upperbound (𝓓 0) δ i ]
              ∐ (𝓓 0) δ    ∎⟨ 𝓓 0 ⟩
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 1))
                  (e₀ (∐ (𝓓 0) δ)) (λ x → e₀ (α x))
    lb-of-ubs (g , c) ub y =
     ∐-is-lowerbound-of-upperbounds (𝓓 0) δ (g y) (λ i → ub i y)
  p₀ : ⟨ 𝓓 1 ⟩ → ⟨ 𝓓 0 ⟩
  p₀ (f , c) = f (⊥ (𝓓⊥ 0))
  p₀-continuity : is-continuous (𝓓 1) (𝓓 0) p₀
  p₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → p₀ (α i) ⊑⟨ 𝓓 0 ⟩ p₀ (∐ (𝓓 1) {I} {α} δ)
    ub i = ∐-is-upperbound (𝓓 1) {I} {α} δ i (⊥ (𝓓⊥ 0))
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 0))
                  (p₀ (∐ (𝓓 1) {I} {α} δ)) (λ x → p₀ (α x))
    lb-of-ubs y ub =
     ∐-is-lowerbound-of-upperbounds (𝓓 0) ε y ub
      where
       ε : is-Directed (𝓓 0) (pointwise-family (𝓓 0) (𝓓 0) α (⊥ (𝓓⊥ 0)))
       ε = pointwise-family-is-directed (𝓓 0) (𝓓 0) α δ (⊥ (𝓓⊥ 0))
𝓓-diagram (succ n) = (e , e-continuity) , (p , p-continuity)
 where
  IH : DCPO[ 𝓓 n , 𝓓 (succ n) ] × DCPO[ 𝓓 (succ n) , 𝓓 n ]
  IH = 𝓓-diagram n
  eₙ : DCPO[ 𝓓 n , 𝓓 (succ n) ]
  eₙ = pr₁ IH
  pₙ : DCPO[ 𝓓 (succ n) , 𝓓 n ]
  pₙ = pr₂ IH
  e : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ (succ n)) ⟩
  e f = DCPO-∘₃ (𝓓 (succ n)) (𝓓 n) (𝓓 n) (𝓓 (succ n)) pₙ f eₙ
  e-continuity : is-continuous (𝓓 (succ n)) (𝓓 (succ (succ n))) e
  e-continuity = ∘-is-continuous
                  (𝓓 (succ n))
                  ((𝓓 n) ⟹ᵈᶜᵖᵒ (𝓓 (succ n)))
                  (𝓓 (succ (succ n)))
                  (λ f → DCPO-∘ (𝓓 n) (𝓓 n) (𝓓 (succ n)) f eₙ)
                  (DCPO-∘ (𝓓 (succ n)) (𝓓 n) (𝓓 (succ n)) pₙ)
                  (DCPO-∘-is-continuous₂ (𝓓 n) (𝓓 n) (𝓓 (succ n)) eₙ)
                  (DCPO-∘-is-continuous₁ (𝓓 (succ n)) (𝓓 n)
                   (𝓓 (succ n)) pₙ)
  p : ⟨ 𝓓 (succ (succ n)) ⟩ → ⟨ 𝓓 (succ n) ⟩
  p f = DCPO-∘₃ (𝓓 n) (𝓓 (succ n)) (𝓓 (succ n)) (𝓓 n) eₙ f pₙ
  p-continuity : is-continuous (𝓓 (succ (succ n))) (𝓓 (succ n)) p
  p-continuity = ∘-is-continuous
                  (𝓓 (succ (succ n)))
                  ((𝓓 n) ⟹ᵈᶜᵖᵒ (𝓓 (succ n)))
                  (𝓓 (succ n))
                  (DCPO-∘ (𝓓 n) (𝓓 (succ n)) (𝓓 (succ n)) eₙ)
                  (λ f → DCPO-∘ (𝓓 n) (𝓓 (succ n)) (𝓓 n) f pₙ)
                  (DCPO-∘-is-continuous₁ (𝓓 n) (𝓓 (succ n))
                   (𝓓 (succ n)) eₙ)
                  (DCPO-∘-is-continuous₂ (𝓓 n) (𝓓 (succ n)) (𝓓 n) pₙ)

π' : (n : ℕ) → DCPO[ 𝓓 (succ n) , 𝓓 n ]
π' n = pr₂ (𝓓-diagram n)

π : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 n ⟩
π n = underlying-function (𝓓 (succ n)) (𝓓 n) (π' n)

π-is-continuous : (n : ℕ) → is-continuous (𝓓 (succ n)) (𝓓 n) (π n)
π-is-continuous n = pr₂ (pr₂ (𝓓-diagram n))

ε' : (n : ℕ) → DCPO[ 𝓓 n , 𝓓 (succ n) ]
ε' n = pr₁ (𝓓-diagram n)

ε : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (succ n) ⟩
ε n = underlying-function (𝓓 n) (𝓓 (succ n)) (ε' n)

ε-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓 (succ n)) (ε n)
ε-is-continuous n = pr₂ (pr₁ (𝓓-diagram n))

π-on-0 : (f : ⟨ 𝓓 0 ⟩ → ⟨ 𝓓 0 ⟩) (c : is-continuous (𝓓 0) (𝓓 0) f)
       → π 0 (f , c) ＝ f (⊥ (𝓓⊥ 0))
π-on-0 f c = refl

π-on-succ : (n : ℕ) (f : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ n) ⟩)
            (c : is-continuous (𝓓 (succ n)) (𝓓 (succ n)) f)
          → [ 𝓓 n , 𝓓 n ]⟨ π (succ n) (f , c) ⟩ ＝ π n ∘ f ∘ ε n
π-on-succ n f c = refl

π-on-succ' : (n : ℕ) (f : DCPO[ 𝓓 (succ n) , 𝓓 (succ n) ])
           → [ 𝓓 n , 𝓓 n ]⟨ π (succ n) f ⟩
           ＝ π n ∘ [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ f ⟩ ∘ ε n
π-on-succ' n f = refl

ε-on-0 : (x : ⟨ 𝓓 0 ⟩) → [ 𝓓 0 , 𝓓 0 ]⟨ ε 0 x ⟩ ＝ (λ y → x)
ε-on-0 x = refl

ε-on-succ : (n : ℕ) (f : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 n ⟩) (c : is-continuous (𝓓 n) (𝓓 n) f)
          → [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ ε (succ n) (f , c) ⟩ ＝ ε n ∘ f ∘ π n
ε-on-succ n f c = refl

ε-section-of-π : (n : ℕ) → π n ∘ ε n ∼ id
ε-section-of-π zero x = refl
ε-section-of-π (succ n) (f , _) = to-continuous-function-＝ (𝓓 n) (𝓓 n) γ
 where
  γ : π n ∘ ε n ∘ f ∘ π n ∘ ε n ∼ f
  γ x = (π n ∘ ε n ∘ f ∘ π n ∘ ε n) x ＝⟨ IH (f (π n (ε n x))) ⟩
        (f ∘ π n ∘ ε n) x             ＝⟨ ap f (IH x) ⟩
        f x                           ∎
   where
    IH : π n ∘ ε n ∼ id
    IH = ε-section-of-π n

επ-deflation : (n : ℕ) (f : ⟨ 𝓓 (succ n) ⟩) → ε n (π n f) ⊑⟨ 𝓓 (succ n) ⟩ f
επ-deflation zero (f , c) x =
 f (⊥ (𝓓⊥ 0)) ⊑⟨ 𝓓 0 ⟩[ m (⊥ (𝓓⊥ 0)) x (⊥-is-least (𝓓⊥ 0) x) ]
 f x          ∎⟨ 𝓓 0 ⟩
  where
   m : is-monotone (𝓓 0) (𝓓 0) f
   m = monotone-if-continuous (𝓓 0) (𝓓 0) (f , c)
επ-deflation (succ n) (f , c) x =
 {- I would use the ⊑⟨ 𝓓 (succ n) ⟩[ ? ] syntax here, but Agda has trouble
    figuring out some implicit arguments. -}
 transitivity (𝓓 (succ n))
  ((ε n ∘ π n ∘ f ∘ ε n ∘ π n) x) (f (ε n (π n x))) (f x)
  (IH (f (ε n (π n x))))
  (m (ε n (π n x)) x (IH x))
{-
 (ε n ∘ π n ∘ f ∘ ε n ∘ π n) x ⊑⟨ 𝓓 (succ n) ⟩[ IH (f (ε n (π n x)))     ]
 f (ε n (π n x))               ⊑⟨ 𝓓 (succ n) ⟩[ m (ε n (π n x)) x (IH x) ]
 f x                           ∎⟨ 𝓓 (succ n) ⟩ -}
  where
   IH : (g : ⟨ 𝓓 (succ n) ⟩) → ε n (π n g) ⊑⟨ 𝓓 (succ n) ⟩ g
   IH = επ-deflation n
   m : is-monotone (𝓓 (succ n)) (𝓓 (succ n)) f
   m = monotone-if-continuous (𝓓 (succ n)) (𝓓 (succ n)) (f , c)

\end{code}

With the diagram defined, we consider its bilimit D∞.

\begin{code}

open SequentialDiagram
      𝓓 ε π
      επ-deflation
      ε-section-of-π
      ε-is-continuous
      π-is-continuous

π-exp-to-succ : (n : ℕ) → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓 (succ n) ⟩
π-exp-to-succ n f = DCPO-∘₃ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) f (π∞' n)

π-exp-to-succ-is-continuous : (n : ℕ)
                            → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 (succ n))
                               (π-exp-to-succ n)
π-exp-to-succ-is-continuous n =
 DCPO-∘₃-is-continuous₂ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) (π∞' n)

π-exp : (n : ℕ) → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓 n ⟩
π-exp zero     = π 0 ∘ π-exp-to-succ 0
π-exp (succ n) = π-exp-to-succ n

π-exp-is-continuous : (n : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (π-exp n)
π-exp-is-continuous zero = ∘-is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 1) (𝓓 0)
                            (π-exp-to-succ 0) (π 0)
                            (π-exp-to-succ-is-continuous 0) (π-is-continuous 0)
π-exp-is-continuous (succ n) = π-exp-to-succ-is-continuous n

π-exp-commutes-with-π : (n : ℕ) → π n ∘ π-exp (succ n) ∼ π-exp n
π-exp-commutes-with-π zero f = refl
π-exp-commutes-with-π (succ n) (f , c) =
 to-continuous-function-＝ (𝓓 n) (𝓓 n) γ
   where
    h : DCPO[ 𝓓 (succ n) , 𝓓 (succ n) ]
    h = DCPO-∘₃ (𝓓 (succ n)) 𝓓∞ 𝓓∞ (𝓓 (succ n))
         (ε∞' (succ n)) (f , c) (π∞' (succ n))
    γ : ([ 𝓓 n , 𝓓 n ]⟨ π (succ n) h ⟩) ∼ π∞ n ∘ f ∘ ε∞ n
    γ x = [ 𝓓 n , 𝓓 n ]⟨ (π (succ n) h) ⟩ x                       ＝⟨ e₁   ⟩
          (π n ∘ [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ h ⟩ ∘ ε n) x        ＝⟨ refl ⟩
          (π n ∘ π∞ (succ n) ∘ f') x                              ＝⟨ e₂   ⟩
          (π⁺ {n} {succ n} (≤-succ n) ∘ π∞ (succ n) ∘ f') x       ＝⟨ e₃   ⟩
          (π∞ n ∘ f ∘ ε∞ (succ n) ∘ ε n) x                        ＝⟨ e₄   ⟩
          (π∞ n ∘ f ∘ ε∞ (succ n) ∘ ε⁺ {n} {succ n} (≤-succ n)) x ＝⟨ e₅   ⟩
          (π∞ n ∘ f ∘ ε∞ n) x                                     ∎
           where
            f' : ⟨ 𝓓 n ⟩ → ⟨ 𝓓∞ ⟩
            f' = f ∘ ε∞ (succ n) ∘ ε n
            e₁ = happly (π-on-succ' n h) x
            e₂ = π-in-terms-of-π⁺ n (π∞ (succ n) (f' x))
            e₃ = π∞-commutes-with-πs n (succ n) (≤-succ n)
                  (f (ε∞ (succ n) (ε n x)))
            e₄ = ap (π∞ n ∘ f ∘ ε∞ (succ n)) (ε-in-terms-of-ε⁺ n x)
            e₅ = ap (π∞ n ∘ f) (ε∞-commutes-with-εs n (succ n) (≤-succ n) x)

π-exp-commutes-with-π⁺ : (n m : ℕ) (l : n ≤ m) → π⁺ {n} {m} l ∘ π-exp m ∼ π-exp n
π-exp-commutes-with-π⁺ n m l = commute-with-πs-lemma (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                            π-exp π-exp-commutes-with-π n m l

open DcpoCone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) π-exp π-exp-is-continuous π-exp-commutes-with-π⁺

π-exp∞ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
π-exp∞ = limit-mediating-arrow

π-exp∞-is-continuous : is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞
π-exp∞-is-continuous = limit-mediating-arrow-is-continuous

π-exp∞' : DCPO[ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ , 𝓓∞ ]
π-exp∞' = π-exp∞ , π-exp∞-is-continuous

\end{code}

The point is to prove that the map π-exp∞ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩ is an
isomorphism.

\begin{code}

ε-exp-from-succ : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp-from-succ n f = DCPO-∘₃ 𝓓∞ (𝓓 n) (𝓓 n) 𝓓∞ (π∞' n) f (ε∞' n)

ε-exp-from-succ-is-continuous : (n : ℕ)
                              → is-continuous (𝓓 (succ n)) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                                 (ε-exp-from-succ n)
ε-exp-from-succ-is-continuous n = DCPO-∘₃-is-continuous₂ 𝓓∞ (𝓓 n) (𝓓 n) 𝓓∞
                                   (π∞' n) (ε∞' n)

ε-exp : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp zero     = ε-exp-from-succ 0 ∘ ε 0
ε-exp (succ n) = ε-exp-from-succ n

ε-exp-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp n)
ε-exp-is-continuous zero = ∘-is-continuous (𝓓 0) (𝓓 1) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                            (ε 0) (ε-exp-from-succ 0)
                            (ε-is-continuous 0) (ε-exp-from-succ-is-continuous 0)
ε-exp-is-continuous (succ n) = ε-exp-from-succ-is-continuous n

ε-exp-commutes-with-ε : (n : ℕ) → ε-exp (succ n) ∘ ε n ∼ ε-exp n
ε-exp-commutes-with-ε zero x = refl
ε-exp-commutes-with-ε (succ n) (f , c) =
 to-continuous-function-＝ 𝓓∞ 𝓓∞ γ
   where
    ε-exp₁ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
    ε-exp₁ = [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp (succ (succ n)) (ε (succ n) (f , c)) ⟩
    ε-exp₂ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
    ε-exp₂ = [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp (succ n) (f , c) ⟩
    γ : ε-exp₁ ∼ ε-exp₂
    γ σ = ε-exp₁ σ                                                ＝⟨ refl ⟩
          (ε∞ (succ n) ∘ ε n ∘ h) σ                               ＝⟨ e₁   ⟩
          (ε∞ (succ n) ∘ ε⁺ {n} {succ n} (≤-succ n) ∘ h) σ        ＝⟨ e₂   ⟩
          (ε∞ n ∘ h) σ                                            ＝⟨ refl ⟩
          (ε∞ n ∘ f ∘ π n ∘ π∞ (succ n)) σ                        ＝⟨ e₃ ⟩
          (ε∞ n ∘ f ∘ π⁺ {n} {succ n} (≤-succ n) ∘ π∞ (succ n)) σ ＝⟨ e₄ ⟩
          (ε∞ n ∘ f ∘ π∞ n) σ                                     ＝⟨ refl ⟩
          ε-exp₂ σ                                                ∎
     where
      h : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓 n ⟩
      h = f ∘ π n ∘ π∞ (succ n)
      e₁ = ap (ε∞ (succ n)) (ε-in-terms-of-ε⁺ n (h σ))
      e₂ = ε∞-commutes-with-εs n (succ n) (≤-succ n) (h σ)
      e₃ = ap (ε∞ n ∘ f) (π-in-terms-of-π⁺ n (π∞ (succ n) σ))
      e₄ = ap (ε∞ n ∘ f) (π∞-commutes-with-πs n (succ n) (≤-succ n) σ)

ε-exp-commutes-with-ε⁺ : (n m : ℕ) (l : n ≤ m) → ε-exp m ∘ ε⁺ {n} {m} l ∼ ε-exp n
ε-exp-commutes-with-ε⁺ n m l = commute-with-εs-lemma (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε-exp
                                ε-exp-commutes-with-ε n m l

open DcpoCocone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε-exp ε-exp-is-continuous ε-exp-commutes-with-ε⁺

ε-exp∞ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp∞ = colimit-mediating-arrow

ε-exp∞-is-continuous : is-continuous 𝓓∞ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε-exp∞
ε-exp∞-is-continuous = colimit-mediating-arrow-is-continuous

ε-exp∞' : DCPO[ 𝓓∞ , 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ]
ε-exp∞' = ε-exp∞ , ε-exp∞-is-continuous

\end{code}

The map ε-exp∞ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ is going to be the desired inverse of
π-exp∞.

\begin{code}

ε-exp-family : ⟨ 𝓓∞ ⟩ → ℕ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp-family σ n = ε-exp (succ n) (⦅ σ ⦆ (succ n))

ε-exp-family-is-directed : (σ : ⟨ 𝓓∞ ⟩)
                         → is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
ε-exp-family-is-directed σ = ∣ 0 ∣ , γ
 where
  γ : is-semidirected (underlying-order (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)) (ε-exp-family σ)
  γ n m = ∥∥-functor g h
   where
    δ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family σ)
    δ = colimit-family-is-directed σ
    h : ∃ k ꞉ ℕ , colimit-family σ (succ n) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k
                × colimit-family σ (succ m) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k
    h = semidirected-if-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family σ) δ
         (succ n) (succ m)
    g : (Σ k ꞉ ℕ , colimit-family σ (succ n) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k
                 × colimit-family σ (succ m) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k)
      → Σ k ꞉ ℕ , ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
                × ε-exp-family σ m ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
    g (k , lₙ , lₘ) = k , lₙ' , lₘ'
     where
      lₖ : colimit-family σ k ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
      lₖ = colimit-family-is-monotone σ k (succ k) (≤-succ k)
      lₙ' : ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
      lₙ' = transitivity (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
             (ε-exp-family σ n) (colimit-family σ k) (ε-exp-family σ k)
             lₙ lₖ
      lₘ' : ε-exp-family σ m ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
      lₘ' = transitivity (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
             (ε-exp-family σ m) (colimit-family σ k) (ε-exp-family σ k)
             lₘ lₖ

ε-exp∞-alt : (σ : ⟨ 𝓓∞ ⟩)
           → ε-exp∞ σ ＝ ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family-is-directed σ)
ε-exp∞-alt σ = antisymmetry (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp∞ σ) (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂) a b
 where
  δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family σ)
  δ₁ = colimit-family-is-directed σ
  δ₂ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
  δ₂ = ε-exp-family-is-directed σ
  a : ε-exp∞ σ ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂
  a = ∐-is-monotone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁ δ₂ γ
   where
    γ : (n : ℕ)
      → colimit-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ n
    γ n = colimit-family-is-monotone σ n (succ n) (≤-succ n)
  b : ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂ ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp∞ σ
  b = ∐-is-lowerbound-of-upperbounds (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂ (ε-exp∞ σ) γ
   where
    γ : is-upperbound (underlying-order (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞))
         (ε-exp∞ σ) (ε-exp-family σ)
    γ n = ∐-is-upperbound (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁ (succ n)

π-exp-family : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ℕ → ⟨ 𝓓∞ ⟩
π-exp-family φ n = ε∞ (succ n) (π-exp (succ n) φ)

\end{code}

In the code below we would like to write things as
 x ⊑⟨ 𝓓∞ ⟩[ u ]
 y ⊑⟨ 𝓓∞ ⟩[ v ]
 z ∎⟨ 𝓓∞ ⟩

However, Agda has trouble figuring out some implicit arguments. (I believe
because it can't 'see' the additional witnesses (of continuity, etc.) that the
underlying functions of x, y and z are equipped with.)

Not using the _⊑⟨_⟩[_] syntax in favour of using transitivity directly and
explicitly naming all its arguments solves the above problem, but it doesn't
read very well.

Instead, we solve the problem by noting that the order on 𝓓∞ is pointwise and
that therefore we are really proving that for every i : ℕ we have
 ⦅ x ⦆ i ⊑⟨ 𝓓 i ⟩[ u i ]
 ⦅ y ⦆ i ⊑⟨ 𝓓 i ⟩[ v i ]
 ⦅ z ⦆ i ∎⟨ 𝓓 i ⟩

\begin{code}

π-exp-family-is-directed : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩)
                         → is-Directed 𝓓∞ (π-exp-family φ)
π-exp-family-is-directed φ = ∣ 0 ∣ , γ
 where
  γ : is-semidirected (underlying-order 𝓓∞) (π-exp-family φ)
  γ n m = ∥∥-functor g h
   where
    σ : ⟨ 𝓓∞ ⟩
    σ = π-exp∞ φ
    δ : is-Directed 𝓓∞ (ε∞-family σ)
    δ = ε∞-family-is-directed σ
    h : ∃ k ꞉ ℕ , ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
                × ε∞-family σ (succ m) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
    h = semidirected-if-Directed 𝓓∞ (ε∞-family σ) δ (succ n) (succ m)
    g : (Σ k ꞉ ℕ , ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
                 × ε∞-family σ (succ m) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k)
      → Σ k ꞉ ℕ , π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ k
                × π-exp-family φ m ⊑⟨ 𝓓∞ ⟩ π-exp-family φ k
    g (k , lₙ , lₘ) = k , lₙ' , lₘ'
     where
      lₖ : ε∞-family σ k ⊑⟨ 𝓓∞ ⟩ ε∞-family σ (succ k)
      lₖ = ε∞-family-is-monotone σ k (succ k) (≤-succ k)
      lₙ' : π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ k
      lₙ' i =
       ⦅ π-exp-family φ n ⦆     i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ n) i ]
       ⦅ ε∞-family σ (succ n) ⦆ i ⊑⟨ 𝓓 i ⟩[ lₙ i ]
       ⦅ ε∞-family σ k        ⦆ i ⊑⟨ 𝓓 i ⟩[ lₖ i ]
       ⦅ ε∞-family σ (succ k) ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ k) i ]
       ⦅ π-exp-family φ k ⦆     i ∎⟨ 𝓓 i ⟩
      lₘ' : π-exp-family φ m ⊑⟨ 𝓓∞ ⟩ π-exp-family φ k
      lₘ' i =
       ⦅ π-exp-family φ m ⦆     i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ m) i ]
       ⦅ ε∞-family σ (succ m) ⦆ i ⊑⟨ 𝓓 i ⟩[ lₘ i ]
       ⦅ ε∞-family σ k        ⦆ i ⊑⟨ 𝓓 i ⟩[ lₖ i ]
       ⦅ ε∞-family σ (succ k) ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ k) i ]
       ⦅ π-exp-family φ k ⦆     i ∎⟨ 𝓓 i ⟩

π-exp∞-alt : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩)
           → π-exp∞ φ ＝ ∐ 𝓓∞ (π-exp-family-is-directed φ)
π-exp∞-alt φ = σ                              ＝⟨ ∐-of-ε∞s σ ⟩
               ∐ 𝓓∞ (ε∞-family-is-directed σ) ＝⟨ γ ⟩
               ∐ 𝓓∞ (π-exp-family-is-directed φ) ∎
 where
  σ : ⟨ 𝓓∞ ⟩
  σ = π-exp∞ φ
  γ : ∐ 𝓓∞ (ε∞-family-is-directed σ) ＝ ∐ 𝓓∞ (π-exp-family-is-directed φ)
  γ = antisymmetry 𝓓∞ (∐ 𝓓∞ δ₁) (∐ 𝓓∞ δ₂) a b
   where
    δ₁ : is-Directed 𝓓∞ (ε∞-family σ)
    δ₁ = ε∞-family-is-directed σ
    δ₂ : is-Directed 𝓓∞ (π-exp-family φ)
    δ₂ = π-exp-family-is-directed φ
    a : ∐ 𝓓∞ δ₁ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₂
    a = ∐-is-monotone 𝓓∞ δ₁ δ₂ h
     where
      h : (n : ℕ) → ε∞-family σ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ n
      h n i = ⦅ ε∞-family σ n        ⦆ i ⊑⟨ 𝓓 i ⟩[ ε∞-family-is-monotone σ n (succ n) (≤-succ n) i ]
              ⦅ ε∞-family σ (succ n) ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (ε∞-family σ (succ n)) i ]
              ⦅ π-exp-family φ n     ⦆ i ∎⟨ 𝓓 i ⟩
    b : ∐ 𝓓∞ δ₂ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₁
    b = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₂ (∐ 𝓓∞ δ₁) h
     where
      h : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₁) (π-exp-family φ)
      h n i = ⦅ π-exp-family φ n     ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ n) i ]
              ⦅ ε∞-family σ (succ n) ⦆ i ⊑⟨ 𝓓 i ⟩[ ∐-is-upperbound 𝓓∞ δ₁ (succ n) i ]
              ⦅ ∐ 𝓓∞ δ₁              ⦆ i ∎⟨ 𝓓 i ⟩

π-exp-family-is-monotone : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩) {n m : ℕ} → n ≤ m
                         → π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ m
π-exp-family-is-monotone φ {n} {m} l i =
 ⦅ π-exp-family φ n              ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ n) i ]
 ⦅ ε∞-family (π-exp∞ φ) (succ n) ⦆ i ⊑⟨ 𝓓 i ⟩[ u i ]
 ⦅ ε∞-family (π-exp∞ φ) (succ m) ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity 𝓓∞ (π-exp-family φ m) i ]
 ⦅ π-exp-family φ m              ⦆ i ∎⟨ 𝓓 i ⟩
  where
   u = ε∞-family-is-monotone (π-exp∞ φ) (succ n) (succ m) l

π-exp-family-is-monotone' : (φ ψ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩) {n : ℕ}
                          → φ ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ψ
                          → π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family ψ n
π-exp-family-is-monotone' φ ψ {n} l i =
 ⦅ π-exp-family φ n               ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
 ⦅ ε∞ (succ n) (π-exp (succ n) φ) ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
 ⦅ ε∞ (succ n) (π-exp (succ n) ψ) ⦆ i ⊑⟨ 𝓓 i ⟩[ u₃ i ]
 ⦅ π-exp-family ψ n               ⦆ i ∎⟨ 𝓓 i ⟩
  where
   u₁ = reflexivity 𝓓∞ (ε∞ (succ n) (π-exp (succ n) φ))
   u₂ = monotone-if-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ f φ ψ l
    where
     f : DCPO[ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ , 𝓓∞ ]
     f = DCPO-∘ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 (succ n)) 𝓓∞
          (π-exp (succ n) , π-exp-is-continuous (succ n))
          (ε∞' (succ n))
   u₃ = reflexivity 𝓓∞ (ε∞ (succ n) (π-exp (succ n) ψ))

ε-exp-family-is-monotone : (σ : ⟨ 𝓓∞ ⟩) {n m : ℕ} → n ≤ m
                         → ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ m
ε-exp-family-is-monotone σ {n} {m} l =
 colimit-family-is-monotone σ (succ n) (succ m) l

ε-exp-family-is-monotone' : (σ τ : ⟨ 𝓓∞ ⟩) {n : ℕ} → σ ⊑⟨ 𝓓∞ ⟩ τ
                          → ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family τ n
ε-exp-family-is-monotone' σ τ {n} l ρ i =
 ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp-family σ n ⟩ ρ                 ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
 ⦅ (ε∞ n ∘ [ 𝓓 n , 𝓓 n ]⟨ ⦅ σ ⦆ (succ n) ⟩ ∘ π∞ n) ρ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
 ⦅ (ε∞ n ∘ [ 𝓓 n , 𝓓 n ]⟨ ⦅ τ ⦆ (succ n) ⟩ ∘ π∞ n) ρ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₃ i ]
 ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp-family τ n ⟩ ρ                 ⦆ i ∎⟨ 𝓓 i ⟩
  where
   u₁ = reflexivity 𝓓∞ ([ 𝓓∞ , 𝓓∞ ]⟨ ε-exp-family σ n ⟩ ρ)
   u₂ = monotone-if-continuous (𝓓 n) 𝓓∞ (ε∞' n)
         ([ 𝓓 n , 𝓓 n ]⟨ ⦅ σ ⦆ (succ n) ⟩ (π∞ n ρ))
         ([ 𝓓 n , 𝓓 n ]⟨ ⦅ τ ⦆ (succ n) ⟩ (π∞ n ρ))
         (l (succ n) (π∞ n ρ))
   u₃ = reflexivity 𝓓∞ ([ 𝓓∞ , 𝓓∞ ]⟨ ε-exp-family τ n ⟩ ρ)

\end{code}

Finally, we have established enough material to prove that ε-exp∞ is the inverse
of π-exp∞.

\begin{code}

ε-exp∞-section-of-π-exp∞ : π-exp∞ ∘ ε-exp∞ ∼ id
ε-exp∞-section-of-π-exp∞ σ =
 π-exp∞ (ε-exp∞ σ)                                 ＝⟨ ap π-exp∞ (ε-exp∞-alt σ) ⟩
 π-exp∞ (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁)                       ＝⟨ e₁ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → (π-exp∞ ∘ ε-exp-family σ) n} δ₂   ＝⟨ ∐-family-＝ 𝓓∞ p δ₂ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → ∐ 𝓓∞ {ℕ} {λ m → f n m} (δ₃ n)} δ₄ ＝⟨ e₂ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → ε∞ n (⦅ σ ⦆ n)} δ₅                ＝⟨ (∐-of-ε∞s σ) ⁻¹ ⟩
 σ                                                 ∎
  where
   f : ℕ → ℕ → ⟨ 𝓓∞ ⟩
   f n m = π-exp-family (ε-exp-family σ n) m
   δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
   δ₁ = ε-exp-family-is-directed σ
   δ₂ : is-Directed 𝓓∞ (π-exp∞ ∘ ε-exp-family σ)
   δ₂ = image-is-directed' (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞' δ₁
   δ₃ : (n : ℕ) → is-Directed 𝓓∞ (π-exp-family (ε-exp-family σ n))
   δ₃ n = π-exp-family-is-directed (ε-exp-family σ n)
   p : π-exp∞ ∘ ε-exp-family σ ＝ λ n → ∐ 𝓓∞ (δ₃ n)
   p = dfunext fe (λ n → π-exp∞-alt (ε-exp-family σ n))
   δ₄ : is-Directed 𝓓∞ (λ n → ∐ 𝓓∞ (δ₃ n))
   δ₄ = transport (is-Directed 𝓓∞) p δ₂
   δ₅ : is-Directed 𝓓∞ (ε∞-family σ)
   δ₅ = ε∞-family-is-directed σ
   e₁ = continuous-∐-＝ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞' δ₁
   e₂ = antisymmetry 𝓓∞ (∐ 𝓓∞ δ₄) (∐ 𝓓∞ δ₅) l₁ l₂
    where
     r : (n : ℕ) → f n n ＝ ε∞-family σ (succ n)
     r n = ap (ε∞ (succ n)) γ
      where
       γ : π-exp (succ n) (ε-exp-family σ n) ＝ ⦅ σ ⦆ (succ n)
       γ = to-continuous-function-＝ (𝓓 n) (𝓓 n) ψ
        where
         σ' : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 n ⟩
         σ' = [ 𝓓 n , 𝓓 n ]⟨ ⦅ σ ⦆ (succ n) ⟩
         ψ : π∞ n ∘ ε∞ n ∘ σ' ∘ π∞ n ∘ ε∞ n ∼ σ'
         ψ x = (π∞ n ∘ ε∞ n ∘ σ' ∘ π∞ n ∘ ε∞ n) x ＝⟨ p₁ ⟩
               (σ' ∘ π∞ n ∘ ε∞ n) x               ＝⟨ p₂ ⟩
               σ' x                               ∎
          where
           p₁ = ε∞-section-of-π∞ (σ' (π∞ n (ε∞ n x)))
           p₂ = ap σ' (ε∞-section-of-π∞ x)
     l₁ : ∐ 𝓓∞ δ₄ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₅
     l₁ = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₄ (∐ 𝓓∞ δ₅) γ
      where
       γ : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₅) (λ n → ∐ 𝓓∞ (δ₃ n))
       γ n = ∐-is-lowerbound-of-upperbounds 𝓓∞ (δ₃ n) (∐ 𝓓∞ δ₅) ψ
        where
         ψ : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₅) (f n)
         ψ m i = ⦅ f n m                       ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
                 ⦅ f (n +' m) m                ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
                 ⦅ f (n +' m) (n +' m)         ⦆ i ⊑⟨ 𝓓 i ⟩[ u₃ i ]
                 ⦅ ε∞-family σ (succ (n +' m)) ⦆ i ⊑⟨ 𝓓 i ⟩[ u₄ i ]
                 ⦅ ∐ 𝓓∞ δ₅                     ⦆ i ∎⟨ 𝓓 i ⟩
          where
           u₁ = π-exp-family-is-monotone'
                 (ε-exp-family σ n) (ε-exp-family σ (n +' m))
                 (ε-exp-family-is-monotone σ (≤-+ n m))
           u₂ = π-exp-family-is-monotone (ε-exp-family σ (n +' m)) (≤-+' n m)
           u₃ = ＝-to-⊑ 𝓓∞ (r (n +' m))
           u₄ = ∐-is-upperbound 𝓓∞ δ₅ (succ (n +' m))
     l₂ : ∐ 𝓓∞ δ₅ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₄
     l₂ = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₅ (∐ 𝓓∞ δ₄) γ
      where
       γ : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₄) (ε∞-family σ)
       γ n i =
        ⦅ ε∞-family σ n        ⦆ i ⊑⟨ 𝓓 i ⟩[ u i                           ]
        ⦅ ε∞-family σ (succ n) ⦆ i ⊑⟨ 𝓓 i ⟩[ ＝-to-⊒ 𝓓∞ (r n) i             ]
        ⦅ f n n                ⦆ i ⊑⟨ 𝓓 i ⟩[ ∐-is-upperbound 𝓓∞ (δ₃ n) n i ]
        ⦅ ∐ 𝓓∞ (δ₃ n)          ⦆ i ⊑⟨ 𝓓 i ⟩[ ∐-is-upperbound 𝓓∞ δ₄ n i     ]
        ⦅ ∐ 𝓓∞ δ₄              ⦆ i ∎⟨ 𝓓 i ⟩
         where
          u = ε∞-family-is-monotone σ n (succ n) (≤-succ n)

π-exp∞-section-of-ε-exp∞ : ε-exp∞ ∘ π-exp∞ ∼ id
π-exp∞-section-of-ε-exp∞ φ =
 ε-exp∞ (π-exp∞ φ)                                ＝⟨ e₁ ⟩
 ε-exp∞ (∐ 𝓓∞ δ₁)                                 ＝⟨ e₂ ⟩
 ∐ 𝓔 {ℕ} {λ n → (ε-exp∞ ∘ π-exp-family φ) n} δ₂   ＝⟨ e₃ ⟩
 ∐ 𝓔 {ℕ} {λ n → ∐ 𝓔 {ℕ} {λ m → f' n m} (δ₃ n)} δ₄ ＝⟨ e₄ ⟩
 ∐ 𝓔 {ℕ} {λ n → f' n n} δ₅                        ＝⟨ e₅ ⟩
 ∐ 𝓔 {ℕ} {λ n → g' n n} δ₆                        ＝⟨ e₆ ⟩
 DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s                        ＝⟨ e₇ ⟩
 φ                                                ∎
  where
   𝓔 : DCPO {𝓤₁} {𝓤₁}
   𝓔 = 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞
   ϕ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
   ϕ = [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩
   f' : ℕ → ℕ → ⟨ 𝓔 ⟩
   f' n m = ε-exp-family (π-exp-family φ n) m
   f : ℕ → ℕ → ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
   f n m = [ 𝓓∞ , 𝓓∞ ]⟨ f' n m ⟩
   f'-mon : (n₁ n₂ m₁ m₂ : ℕ) → n₁ ≤ n₂ → m₁ ≤ m₂ → f' n₁ m₁ ⊑⟨ 𝓔 ⟩ f' n₂ m₂
   f'-mon n₁ n₂ m₁ m₂ lₙ lₘ σ i = ⦅ f n₁ m₁ σ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
                                  ⦅ f n₂ m₁ σ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
                                  ⦅ f n₂ m₂ σ ⦆ i ∎⟨ 𝓓 i ⟩
    where
     u₁ = ε-exp-family-is-monotone' (π-exp-family φ n₁) (π-exp-family φ n₂)
           (π-exp-family-is-monotone φ lₙ) σ
     u₂ = ε-exp-family-is-monotone (π-exp-family φ n₂) lₘ σ
   g' : ℕ → ℕ → ⟨ 𝓔 ⟩
   g' n m = DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ (ε∞π∞-family m) φ (ε∞π∞-family n)
   g : ℕ → ℕ → ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
   g n m = [ 𝓓∞ , 𝓓∞ ]⟨ g' n m ⟩
   g'-mon : (n₁ n₂ m₁ m₂ : ℕ) → n₁ ≤ n₂ → m₁ ≤ m₂ → g' n₁ m₁ ⊑⟨ 𝓔 ⟩ g' n₂ m₂
   g'-mon n₁ n₂ m₁ m₂ lₙ lₘ σ i = ⦅ g n₁ m₁ σ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
                                  ⦅ g n₂ m₁ σ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
                                  ⦅ g n₂ m₂ σ ⦆ i ∎⟨ 𝓓 i ⟩
    where
     u₁ = ε∞π∞-family-is-monotone lₙ ((ϕ ∘ ε∞ m₁ ∘ π∞ m₁) σ)
     u₂ = monotone-if-continuous 𝓓∞ 𝓓∞ (ε∞π∞-family n₂)
           ((ϕ ∘ ε∞ m₁ ∘ π∞ m₁) σ) ((ϕ ∘ ε∞ m₂ ∘ π∞ m₂) σ)
           (monotone-if-continuous 𝓓∞ 𝓓∞ φ
            (ε∞ m₁ (π∞ m₁ σ)) (ε∞ m₂ (π∞ m₂ σ))
            (ε∞π∞-family-is-monotone lₘ σ))
   q : (λ n → f' n n) ＝ (λ n → g' n n)
   q = dfunext fe γ
    where
     γ : (λ n → f' n n) ∼ (λ n → g' n n)
     γ n = to-continuous-function-＝ 𝓓∞ 𝓓∞ γ'
      where
       γ' : f n n ∼ g n n
       γ' σ =
        f n n σ                                                        ＝⟨ refl ⟩
        (ε∞ n ∘ [ 𝓓 n , 𝓓 n ]⟨ π∞ (succ n) (ε∞ (succ n) ψ) ⟩ ∘ π∞ n) σ ＝⟨ q'   ⟩
        (ε∞ n ∘ [ 𝓓 n , 𝓓 n ]⟨ ψ ⟩ ∘ π∞ n) σ                           ＝⟨ refl ⟩
        (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ n ∘ π∞ n) σ                              ＝⟨ refl ⟩
        g n n σ ∎
         where
          ψ : DCPO[ 𝓓 n , 𝓓 n ]
          ψ = DCPO-∘₃ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) φ (π∞' n)
          q' = ap (λ - → (ε∞ n ∘ [ 𝓓 n , 𝓓 n ]⟨ - ⟩ ∘ π∞ n) σ)
                (ε∞-section-of-π∞ ψ)
   s : ⟨ 𝓔 ⟩
   s = ∐ 𝓔 ε∞π∞-family-is-directed
   δ₁ = π-exp-family-is-directed φ
   δ₂ = image-is-directed' 𝓓∞ 𝓔 ε-exp∞' δ₁
   δ₃ : (n : ℕ) → is-Directed 𝓔 (ε-exp-family (π-exp-family φ n))
   δ₃ n = ε-exp-family-is-directed (π-exp-family φ n)
   p : ε-exp∞ ∘ π-exp-family φ ＝ (λ n → ∐ 𝓔 (δ₃ n))
   p = dfunext fe (λ n → ε-exp∞-alt (π-exp-family φ n))
   δ₄ : is-Directed 𝓔 (λ n → ∐ 𝓔 (δ₃ n))
   δ₄ = (transport (is-Directed 𝓔) p δ₂)
   δ₅ : is-Directed 𝓔 (λ n → f' n n)
   δ₅ = ∣ 0 ∣ , δ₅'
    where
     δ₅' : is-semidirected (underlying-order 𝓔) (λ n → f' n n)
     δ₅' n m = ∣ n +' m , uₙ  , uₘ ∣
      where
       uₙ : f' n n ⊑⟨ 𝓔 ⟩ f' (n +' m) (n +' m)
       uₙ = f'-mon n (n +' m) n (n +' m) (≤-+ n m) (≤-+ n m)
       uₘ : f' m m ⊑⟨ 𝓔 ⟩ f' (n +' m) (n +' m)
       uₘ = f'-mon m (n +' m) m (n +' m) (≤-+' n m) (≤-+' n m)
   δ₆ : is-Directed 𝓔 (λ n → g' n n)
   δ₆ = transport (is-Directed 𝓔) q δ₅
   e₁ = ap ε-exp∞ (π-exp∞-alt φ)
   e₂ = continuous-∐-＝ 𝓓∞ 𝓔 ε-exp∞' δ₁
   e₃ = ∐-family-＝ 𝓔 p δ₂
   e₅ = ∐-family-＝ 𝓔 q δ₅
   e₄ = antisymmetry 𝓔 (∐ 𝓔 δ₄) (∐ 𝓔 δ₅) l₁ l₂
    where
     l₁ : ∐ 𝓔 δ₄ ⊑⟨ 𝓔 ⟩ ∐ 𝓔 δ₅
     l₁ = ∐-is-lowerbound-of-upperbounds 𝓔 δ₄ (∐ 𝓔 δ₅) γ
      where
       γ : is-upperbound (underlying-order 𝓔) (∐ 𝓔 δ₅) (λ n → ∐ 𝓔 (δ₃ n))
       γ n = ∐-is-lowerbound-of-upperbounds 𝓔 (δ₃ n) (∐ 𝓔 δ₅) γ'
        where
         γ' : is-upperbound (underlying-order 𝓔) (∐ 𝓔 δ₅) (λ m → f' n m)
         γ' m = transitivity 𝓔 (f' n m) (f' (n +' m) (n +' m)) (∐ 𝓔 δ₅)
                 (f'-mon n (n +' m) m (n +' m) (≤-+ n m) (≤-+' n m))
                 (∐-is-upperbound 𝓔 δ₅ (n +' m))
     l₂ : ∐ 𝓔 δ₅ ⊑⟨ 𝓔 ⟩ ∐ 𝓔 δ₄
     l₂ = ∐-is-lowerbound-of-upperbounds 𝓔 δ₅ (∐ 𝓔 δ₄) γ
      where
       γ : is-upperbound (underlying-order 𝓔) (∐ 𝓔 δ₄) (λ n → f' n n)
       γ n = transitivity 𝓔 (f' n n) (∐ 𝓔 (δ₃ n)) (∐ 𝓔 δ₄)
              (∐-is-upperbound 𝓔 (δ₃ n) n)
              (∐-is-upperbound 𝓔 δ₄ n)
   e₇ = DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s ＝⟨ p₁ ⟩
        DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ ι φ ι ＝⟨ p₂ ⟩
        φ                         ∎
    where
     ι : DCPO[ 𝓓∞ , 𝓓∞ ]
     ι = id , id-is-continuous 𝓓∞
     p₁ = ap₂ (λ -₁ -₂ → DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ -₁ φ -₂) e e
      where
       e : s ＝ ι
       e = ∐-of-ε∞π∞s-is-id
     p₂ = to-continuous-function-＝ 𝓓∞ 𝓓∞ (λ σ → 𝓻𝓮𝒻𝓵 (ϕ σ))
   e₆ = antisymmetry 𝓔 (∐ 𝓔 δ₆) (DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s) l₁ l₂
    where
     s₁ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
     s₁ = [ 𝓓∞ , 𝓓∞ ]⟨ s ⟩
     l₁ : ∐ 𝓔 δ₆ ⊑⟨ 𝓔 ⟩ DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s
     l₁ = ∐-is-lowerbound-of-upperbounds 𝓔 δ₆ (DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s) γ
      where
       γ : is-upperbound (underlying-order 𝓔) (DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s)
            (λ n → g' n n)
       γ n σ i = ⦅ g n n σ                           ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
                 ⦅ (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ n ∘ π∞ n) σ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
                 ⦅ (s₁ ∘ ϕ) (ε∞ n (π∞ n σ))          ⦆ i ⊑⟨ 𝓓 i ⟩[ u₃ i ]
                 ⦅ (s₁ ∘ ϕ ∘ s₁) σ                   ⦆ i ∎⟨ 𝓓 i ⟩
        where
         δ : is-Directed 𝓓∞ (pointwise-family 𝓓∞ 𝓓∞ ε∞π∞-family
              ((ϕ ∘ ε∞ n ∘ π∞ n) σ))
         δ = pointwise-family-is-directed 𝓓∞ 𝓓∞ ε∞π∞-family
              ε∞π∞-family-is-directed ((ϕ ∘ ε∞ n ∘ π∞ n) σ)
         δ' : is-Directed 𝓓∞ (pointwise-family 𝓓∞ 𝓓∞ ε∞π∞-family σ)
         δ' = pointwise-family-is-directed 𝓓∞ 𝓓∞ ε∞π∞-family
               ε∞π∞-family-is-directed σ
         u₁ = reflexivity 𝓓∞ (g n n σ)
         u₂ = ∐-is-upperbound 𝓓∞ δ n
         u₃ = monotone-if-continuous 𝓓∞ 𝓓∞ (DCPO-∘ 𝓓∞ 𝓓∞ 𝓓∞ φ s)
               (ε∞ n (π∞ n σ)) (s₁ σ) (∐-is-upperbound 𝓓∞ δ' n)
     l₂ : DCPO-∘₃ 𝓓∞ 𝓓∞ 𝓓∞ 𝓓∞ s φ s ⊑⟨ 𝓔 ⟩ ∐ 𝓔 δ₆
     l₂ σ = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ ([ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ) γ
      where
       δ : is-Directed 𝓓∞ (pointwise-family 𝓓∞ 𝓓∞ ε∞π∞-family (ϕ (s₁ σ)))
       δ = pointwise-family-is-directed 𝓓∞ 𝓓∞ ε∞π∞-family
            ε∞π∞-family-is-directed (ϕ (s₁ σ))
       γ : is-upperbound (underlying-order 𝓓∞) ([ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ)
            (pointwise-family 𝓓∞ 𝓓∞ ε∞π∞-family (ϕ (s₁ σ)))
       γ n i =
        ⦅ (ε∞ n ∘ π∞ n ∘ ϕ ∘ s₁) σ ⦆ i ⊑⟨ 𝓓 i ⟩[ continuous-∐-⊑ 𝓓∞ 𝓓∞ h δ₁' i ]
        ⦅ ∐ 𝓓∞ δ₂'                 ⦆ i ⊑⟨ 𝓓 i ⟩[ γ₁ i ]
        ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ  ⦆ i ∎⟨ 𝓓 i ⟩
         where
          h : DCPO[ 𝓓∞ , 𝓓∞ ]
          h = DCPO-∘₃ 𝓓∞ 𝓓∞ (𝓓 n) 𝓓∞ φ (π∞' n) (ε∞' n)
          δ₁' : is-Directed 𝓓∞ (pointwise-family 𝓓∞ 𝓓∞ ε∞π∞-family σ)
          δ₁' = pointwise-family-is-directed 𝓓∞ 𝓓∞ ε∞π∞-family
                ε∞π∞-family-is-directed σ
          δ₂' : is-Directed 𝓓∞
                 (λ m → (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ m ∘ π∞ m) σ)
          δ₂' = image-is-directed' 𝓓∞ 𝓓∞ h δ₁'
          γ₁ : ∐ 𝓓∞ δ₂' ⊑⟨ 𝓓∞ ⟩ [ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ
          γ₁ = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₂'
                ([ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ) γ₂
           where
            γ₂ : is-upperbound (underlying-order 𝓓∞) ([ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ)
                  (λ m → (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ m ∘ π∞ m) σ)
            γ₂ m i = ⦅ (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ m ∘ π∞ m) σ ⦆ i ⊑⟨ 𝓓 i ⟩[ u₁ i ]
                     ⦅ g n m σ                           ⦆ i ⊑⟨ 𝓓 i ⟩[ u₂ i ]
                     ⦅ g (n +' m) m σ                    ⦆ i ⊑⟨ 𝓓 i ⟩[ u₃ i ]
                     ⦅ g (n +' m) (n +' m) σ             ⦆ i ⊑⟨ 𝓓 i ⟩[ u₄ i ]
                     ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ ∐ 𝓔 δ₆ ⟩ σ           ⦆ i ∎⟨ 𝓓 i ⟩
             where
              δ₃' : is-Directed 𝓓∞ (pointwise-family 𝓓∞ 𝓓∞ (λ k → g' k k) σ)
              δ₃' = pointwise-family-is-directed 𝓓∞ 𝓓∞ (λ k → g' k k) δ₆ σ
              u₁ = reflexivity 𝓓∞ (g n m σ)
              u₂ = g'-mon n (n +' m) m m (≤-+ n m) (≤-refl m) σ
              u₃ = g'-mon (n +' m) (n +' m) m (n +' m)
                    (≤-refl (n +' m)) (≤-+' n m) σ
              u₄ = ∐-is-upperbound 𝓓∞ δ₃' (n +' m)

\end{code}

Hence, D∞ is isomorphic (as a dcpo) to its self-exponential (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞).

\begin{code}

𝓓∞-isomorphic-to-its-self-exponential : 𝓓∞ ≃ᵈᶜᵖᵒ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
𝓓∞-isomorphic-to-its-self-exponential =
 ε-exp∞ , π-exp∞ , ε-exp∞-section-of-π-exp∞ , π-exp∞-section-of-ε-exp∞ ,
 ε-exp∞-is-continuous , π-exp∞-is-continuous

\end{code}

But actually we want D∞ to be a pointed dcpo and we want it to be isomorphic to
the pointed exponential (𝓓∞⊥ ⟹ᵈᶜᵖᵒ⊥ 𝓓∞⊥), which we prove now.

\begin{code}

π-is-strict : (n : ℕ) → is-strict (𝓓⊥ (succ n)) (𝓓⊥ n) (π n)
π-is-strict zero = refl
π-is-strict (succ n) = to-continuous-function-＝ (𝓓 n) (𝓓 n) γ
 where
  f' : ⟨ 𝓓 (succ (succ n)) ⟩
  f' = ⊥ (𝓓⊥ (succ (succ n)))
  f : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ n) ⟩
  f = [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ f' ⟩
  γ : [ 𝓓 n , 𝓓 n ]⟨ π (succ n) f' ⟩ ∼ [ 𝓓 n , 𝓓 n ]⟨ ⊥ (𝓓⊥ (succ n)) ⟩
  γ x = [ 𝓓 n , 𝓓 n ]⟨ π (succ n) f' ⟩ x   ＝⟨ refl ⟩
        (π n ∘ f ∘ ε n) x                  ＝⟨ refl ⟩
        π n (⊥ (𝓓⊥ (succ n)))              ＝⟨ IH ⟩
        [ 𝓓 n , 𝓓 n ]⟨ ⊥ (𝓓⊥ (succ n)) ⟩ x ∎
   where
    IH : π n (⊥ (𝓓⊥ (succ n))) ＝ ⊥ (𝓓⊥ n)
    IH = π-is-strict n

π⁺-is-strict-helper : (n m k : ℕ) (p : n +' k ＝ m)
                    → is-strict (𝓓⊥ m) (𝓓⊥ n) (π⁺-helper n m k p)
π⁺-is-strict-helper n n zero refl = refl
π⁺-is-strict-helper n m (succ k) refl =
 π⁺-helper n m (succ k) refl (⊥ (𝓓⊥ m))              ＝⟨ refl ⟩
 π⁺-helper n (n +' k) k refl (π (n +' k) (⊥ (𝓓⊥ m))) ＝⟨ q    ⟩
 π⁺-helper n (n +' k) k refl (⊥ (𝓓⊥ (n +' k)))       ＝⟨ IH   ⟩
 ⊥ (𝓓⊥ n)                                            ∎
  where
   q = ap (π⁺-helper n (n +' k) k refl) (π-is-strict (n +' k))
   IH = π⁺-is-strict-helper n (n +' k) k refl

π⁺-is-strict : (n m : ℕ) (l : n ≤ m) → is-strict (𝓓⊥ m) (𝓓⊥ n) (π⁺ l)
π⁺-is-strict n m l = π⁺-is-strict-helper n m k p
 where
  k : ℕ
  k = pr₁ (subtraction' n m l)
  p : n +' k ＝ m
  p = pr₂ (subtraction' n m l)

𝓓∞-has-least : has-least (underlying-order 𝓓∞)
𝓓∞-has-least = (σ⊥ , p) , q
 where
  σ⊥ : (n : ℕ) → ⟨ 𝓓 n ⟩
  σ⊥ n = ⊥ (𝓓⊥ n)
  p : (n m : ℕ) (l : n ≤ m) → π⁺ l (σ⊥ m) ＝ σ⊥ n
  p = π⁺-is-strict
  q : is-least (underlying-order 𝓓∞) (σ⊥ , p)
  q τ n = ⊥-is-least (𝓓⊥ n) (⦅ τ ⦆ n)

𝓓∞⊥ : DCPO⊥ {𝓤₁} {𝓤₁}
𝓓∞⊥ = 𝓓∞ , 𝓓∞-has-least

𝓓∞⊥-strict-isomorphic-to-its-self-exponential : 𝓓∞⊥ ≃ᵈᶜᵖᵒ⊥ (𝓓∞⊥ ⟹ᵈᶜᵖᵒ⊥ 𝓓∞⊥)
𝓓∞⊥-strict-isomorphic-to-its-self-exponential =
 ≃ᵈᶜᵖᵒ-to-≃ᵈᶜᵖᵒ⊥ 𝓓∞⊥ (𝓓∞⊥ ⟹ᵈᶜᵖᵒ⊥ 𝓓∞⊥) 𝓓∞-isomorphic-to-its-self-exponential

\end{code}

Of course, for the above to be interesting, we want 𝓓∞ to be nontrivial, i.e. it
has an element σ₀ such that σ₀ is not the least element, which we prove now.

\begin{code}

σ₀ : ⟨ 𝓓∞ ⟩
σ₀ = σ , p
 where
  x₀ : ⟨ 𝓓 0 ⟩
  x₀ = 𝟙 , id , 𝟙-is-prop
  σ : (n : ℕ) → ⟨ 𝓓 n ⟩
  σ n = ε⁺ {0} {n} ⋆ x₀
  p : (n m : ℕ) (l : n ≤ m) → π⁺ l (σ m) ＝ σ n
  p n m l = π⁺ {n} {m} l (ε⁺ {0} {m} ⋆ x₀)                  ＝⟨ e₁ ⟩
            (π⁺ {n} {m} l ∘ ε⁺ {n} {m} l ∘ ε⁺ {0} {n} ⋆) x₀ ＝⟨ e₂ ⟩
            ε⁺ {0} {n} ⋆ x₀                                 ∎
   where
    e₁ = ap (π⁺ {n} {m} l) ((ε⁺-comp ⋆ l x₀) ⁻¹)
    e₂ = ε⁺-section-of-π⁺ l (ε⁺ {0} {n} ⋆ x₀)

𝓓∞⊥-is-nontrivial : σ₀ ≠ ⊥ 𝓓∞⊥
𝓓∞⊥-is-nontrivial e = 𝟘-is-not-𝟙 (γ ⁻¹)
 where
  e₀ : ⦅ σ₀ ⦆ 0 ＝ ⊥ (𝓓⊥ 0)
  e₀ = ap (λ - → ⦅ - ⦆ 0) e
  γ : 𝟙 ＝ 𝟘
  γ = ap pr₁ e₀

\end{code}

Finally, we prove that 𝓓∞ is an algebraic dcpo. We use that our starting dcpo is
sup-complete and has a small compact basis, and that both these things are closed
under taking exponentials.

\begin{code}

open import DomainTheory.Basics.SupComplete pt fe 𝓤₀
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤₀
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤₀
open import DomainTheory.BasesAndContinuity.StepFunctions pt fe 𝓤₀
open import DomainTheory.Lifting.LiftingSetAlgebraic pt pe fe 𝓤₀

𝓓s-are-sup-complete : (n : ℕ) → is-sup-complete (𝓓 n)
𝓓s-are-sup-complete zero     = lifting-of-prop-is-sup-complete 𝟙-is-prop
𝓓s-are-sup-complete (succ n) = exponential-is-sup-complete (𝓓 n) (𝓓 n)
                                (𝓓s-are-sup-complete n)

𝓓∞-has-specified-small-compact-basis : has-specified-small-compact-basis 𝓓∞
𝓓∞-has-specified-small-compact-basis = 𝓓∞-has-small-compact-basis γ
 where
  γ : (n : ℕ) → has-specified-small-compact-basis (𝓓 n)
  γ zero     = 𝓛-has-specified-small-compact-basis (props-are-sets 𝟙-is-prop)
  γ (succ n) = exponential-has-specified-small-compact-basis
                (𝓓 n) (𝓓⊥ n)
                (locally-small-if-small-compact-basis
                  (𝓓 n) β β-is-compact-small-basis)
                B B β β β-is-compact-small-basis β-is-compact-small-basis
                (𝓓s-are-sup-complete n) pe
   where
    IH : has-specified-small-compact-basis (𝓓 n)
    IH = γ n
    B : 𝓤₀ ̇
    B = pr₁ IH
    β : B → ⟨ 𝓓 n ⟩
    β = pr₁ (pr₂ IH)
    β-is-compact-small-basis : is-small-compact-basis (𝓓 n) β
    β-is-compact-small-basis = pr₂ (pr₂ IH)

𝓓∞-is-algebraic-dcpo : is-algebraic-dcpo 𝓓∞
𝓓∞-is-algebraic-dcpo =
 is-algebraic-dcpo-if-unspecified-small-compact-basis 𝓓∞
  ∣ 𝓓∞-has-specified-small-compact-basis ∣

\end{code}
