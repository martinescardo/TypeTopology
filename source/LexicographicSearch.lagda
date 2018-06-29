Martin Escardo, 20-21 December 2012.

This module is mainly for use in the module SearchableOrdinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LexicographicSearch where

open import SpartanMLTT
open import LexicographicOrder
open import InfSearchable

sums-preserve-inf-searchability : ∀ {U V W T} {X : U ̇} {Y : X → V ̇}
  → (_≤_ : X → X → W ̇)
  → (_≼_ : {x : X} → Y x → Y x → T ̇)
  → inf-searchable _≤_
  → ((x : X) → inf-searchable (_≼_ {x}))
  → inf-searchable (lex-order _≤_ _≼_)
sums-preserve-inf-searchability {U} {V} {W} {T} {X} {Y} _≤_ _≼_ ε δ p =
 (x₀ , y₀) , (putative-root-lemma , (lower-bound-lemma , uborlb-lemma))
 where 
  lemma-next : (x : X) → Σ \(y₀ : Y x) → ((Σ \(y : Y x) → p(x , y) ≡ ₀) → p (x , y₀) ≡ ₀)
                                        × ((y : Y x) → p(x , y) ≡ ₀ → y₀ ≼ y)
                                        × ((l : Y x) → ((y : Y x) → p(x , y) ≡ ₀ → l ≼ y) → l ≼ y₀)
  lemma-next x = δ x (λ y → p(x , y))

  next : (x : X) → Y x
  next x = pr₁(lemma-next x)

  next-correctness : (x : X) → ((Σ \(y : Y x) → p(x , y) ≡ ₀) → p (x , next x) ≡ ₀)
                              × ((y : Y x) → p(x , y) ≡ ₀ → next x ≼ y)
                              × ((l : Y x) → ((y : Y x) → p(x , y) ≡ ₀ → l ≼ y) → l ≼ next x)
  next-correctness x = pr₂(lemma-next x)

  lemma-first : Σ \(x₀ : X) → ((Σ \(x : X) → p(x , next x) ≡ ₀) → p (x₀ , next x₀) ≡ ₀) 
                            × ((x : X) → p(x , next x) ≡ ₀ → x₀ ≤ x)
                            × ((m : X) → ((x : X) → p(x , next x) ≡ ₀ → m ≤ x) → m ≤ x₀)
  lemma-first = ε(λ x → p(x , next x))

  x₀ : X
  x₀ = pr₁ lemma-first

  first-correctness : ((Σ \(x : X) → p(x , next x) ≡ ₀) → p (x₀ , next x₀) ≡ ₀)
                     × ((x : X) → p(x , next x) ≡ ₀ → x₀ ≤ x)
                     × ((m : X) → ((x : X) → p(x , next x) ≡ ₀ → m ≤ x) → m ≤ x₀)
  first-correctness = pr₂ lemma-first

  y₀ : Y x₀
  y₀ = next x₀ 

  putative-root-lemma : (Σ \(t : (Σ \(x : X) → Y x)) → p t ≡ ₀) → p(x₀ , y₀) ≡ ₀
  putative-root-lemma ((x , y) , r) = pr₁ first-correctness (x , pr₁(next-correctness x) (y , r))

  _⊑_ : Σ Y → Σ Y → U ⊔ W ⊔ T ̇
  _⊑_ = lex-order _≤_ _≼_ 

  τ : {x x' : X} → x ≡ x' → Y x → Y x'
  τ = transport Y

  lower-bound-lemma : (t : (Σ \(x : X) → Y x)) → p t ≡ ₀ → (x₀ , y₀) ⊑ t
  lower-bound-lemma (x , y) r = ≤-lemma , ≼-lemma
   where
    f : p(x , next x) ≡ ₀ → x₀ ≤ x 
    f = pr₁ (pr₂ first-correctness) x
    ≤-lemma : x₀ ≤ x 
    ≤-lemma = f(pr₁(next-correctness x)(y , r))
    g : next x ≼ y
    g = pr₁ (pr₂(next-correctness x)) y r
    j : {x₀ x : X} (r : x₀ ≡ x) {y : Y x} → next x ≼ y → τ r (next x₀) ≼ y
    j refl = id
    ≼-lemma : (r : x₀ ≡ x) → τ r y₀ ≼ y
    ≼-lemma r = j r g


  uborlb-lemma : (n : Σ \(x : X) → Y x) → ((t : (Σ \(x : X) → Y x)) → p t ≡ ₀ → n ⊑ t) → n ⊑ (x₀ , y₀)
  uborlb-lemma (x , y) lower-bounder = ≤-lemma , ≼-lemma
   where
    f : ((x' : X) → p(x' , next x') ≡ ₀ → x ≤ x') → x ≤ x₀
    f = pr₂(pr₂ first-correctness) x
    ≤-lower-bounder : (x' : X)(y' : Y x') → p(x' , y') ≡ ₀ → x ≤ x'
    ≤-lower-bounder x' y' r' = pr₁(lower-bounder ((x' , y')) r')
    ≤-lemma : x ≤ x₀
    ≤-lemma = f(λ x' → ≤-lower-bounder x' (next x'))
    g :  ((y' : Y x) → p(x , y') ≡ ₀ → y ≼ y') → y ≼ next x
    g = pr₂(pr₂(next-correctness x)) y
    ≼-lower-bounder : (x' : X)(y' : Y x') → p(x' , y') ≡ ₀ → (r : x ≡ x') → τ r y ≼ y'
    ≼-lower-bounder x' y' r' = pr₂(lower-bounder ((x' , y')) r')
    j : {x₀ x : X} → (r : x ≡ x₀) → {y : Y x} → y ≼ next x → τ r y ≼ next x₀
    j refl = id
    ≼-lemma : (r : x ≡ x₀) → τ r y ≼ y₀
    ≼-lemma r = j r (g(λ y' r → ≼-lower-bounder x y' r refl))

\end{code}
