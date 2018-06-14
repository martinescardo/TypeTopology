Martin Escardo, 20-21 December 2012.

This module is mainly for use in the module SearchableOrdinals.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module LexicographicSearch where

open import SpartanMLTT
open import LexicographicOrder
open import InfSearchable

sums-preserve-inf-searchability : ∀ {U V} {X : U ̇} {Y : X → V ̇}
  → (R : bin-rel X) → (S : {x : X} → bin-rel(Y x))
  → inf-searchable X R → ((x : X) → inf-searchable (Y x) (S {x})) → inf-searchable (Σ Y) (lex-prod R S)
sums-preserve-inf-searchability {U} {V} {X} {Y} R S ε δ p =
 (x₀ , y₀) , (putative-root-lemma , (lower-bound-lemma , uborlb-lemma))
 where 
  lemma-next : (x : X) → Σ \(y₀ : Y x) → ((Σ \(y : Y x) → p(x , y) ≡ ₀) → p (x , y₀) ≡ ₀)
                                        × ((y : Y x) → p(x , y) ≡ ₀ → S y₀ y)
                                        × ((l : Y x) → ((y : Y x) → p(x , y) ≡ ₀ → S l y) → S l y₀)
  lemma-next x = δ x (λ y → p(x , y))

  next : (x : X) → Y x
  next x = pr₁(lemma-next x)

  next-correctness : (x : X) → ((Σ \(y : Y x) → p(x , y) ≡ ₀) → p (x , next x) ≡ ₀)
                              × ((y : Y x) → p(x , y) ≡ ₀ → S (next x) y)
                              × ((l : Y x) → ((y : Y x) → p(x , y) ≡ ₀ → S l y) → S l (next x))
  next-correctness x = pr₂(lemma-next x)

  lemma-first : Σ \(x₀ : X) → ((Σ \(x : X) → p(x , next x) ≡ ₀) → p (x₀ , next x₀) ≡ ₀) 
                            × ((x : X) → p(x , next x) ≡ ₀ → R x₀ x)
                            × ((m : X) → ((x : X) → p(x , next x) ≡ ₀ → R m x) → R m x₀)
  lemma-first = ε(λ x → p(x , next x))

  x₀ : X
  x₀ = pr₁ lemma-first

  first-correctness : ((Σ \(x : X) → p(x , next x) ≡ ₀) → p (x₀ , next x₀) ≡ ₀)
                     × ((x : X) → p(x , next x) ≡ ₀ → R x₀ x)
                     × ((m : X) → ((x : X) → p(x , next x) ≡ ₀ → R m x) → R m x₀)
  first-correctness = pr₂ lemma-first

  y₀ : Y x₀
  y₀ = next x₀ 

  putative-root-lemma : (Σ \(t : (Σ \(x : X) → Y x)) → p t ≡ ₀) → p(x₀ , y₀) ≡ ₀
  putative-root-lemma ((x , y) , r) = pr₁ first-correctness (x , pr₁(next-correctness x) (y , r))

  lower-bound-lemma : (t : (Σ \(x : X) → Y x)) → p t ≡ ₀ → lex-prod R S (x₀ , y₀) t
  lower-bound-lemma (x , y) r = R-lemma , S-lemma
   where
    φ : {x x' : X} → x ≡ x' → Y x → Y x'
    φ = transport Y
    f : p(x , next x) ≡ ₀ → R x₀ x 
    f = pr₁(pr₂ first-correctness) x
    R-lemma : R x₀ x 
    R-lemma = f(pr₁(next-correctness x)(y , r))
    g : S (next x) y
    g = pr₁(pr₂(next-correctness x)) y r
    j : {x₀ x : X} (r : x₀ ≡ x) {y : Y x} → S (next x) y → S (φ r (next x₀)) y
    j refl = id
    S-lemma : (r : x₀ ≡ x) → S (φ r y₀) y
    S-lemma r = j r g


  uborlb-lemma : (n : Σ \(x : X) → Y x) → ((t : (Σ \(x : X) → Y x)) → p t ≡ ₀ → lex-prod R S n t) → lex-prod R S n (x₀ , y₀)
  uborlb-lemma (x , y) lower-bounder = R-lemma , S-lemma
   where
    φ : {x x' : X} → x ≡ x' → Y x → Y x'
    φ = transport Y
    f : ((x' : X) → p(x' , next x') ≡ ₀ → R x x') → R x x₀
    f = pr₂(pr₂ first-correctness) x
    R-lower-bounder : (x' : X)(y' : Y x') → p(x' , y') ≡ ₀ → R x x'
    R-lower-bounder x' y' r' = pr₁(lower-bounder ((x' , y')) r')
    R-lemma : R x x₀
    R-lemma = f(λ x' → R-lower-bounder x' (next x'))
    g :  ((y' : Y x) → p(x , y') ≡ ₀ → S y y') → S y (next x)
    g = pr₂(pr₂(next-correctness x)) y
    S-lower-bounder : (x' : X)(y' : Y x') → p(x' , y') ≡ ₀ → (r : x ≡ x') → S (transport Y r y) y'
    S-lower-bounder x' y' r' = pr₂(lower-bounder ((x' , y')) r')
    j : {x₀ x : X} → (r : x ≡ x₀) → {y : Y x} → S y (next x) → S (φ r y) (next x₀)
    j refl = id
    S-lemma : (r : x ≡ x₀) → S (φ r y) y₀
    S-lemma r = j r (g(λ y' r → S-lower-bounder x y' r refl))
\end{code}
