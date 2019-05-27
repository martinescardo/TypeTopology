Tom de Jong & Martin Escardo, 27 May 2019.

 * Directed complete posets.
 * Continuous maps.
 * Function space.
 * Least fixed points.
 * Example: lifting, and the semantic counter-parts of the PCF constants.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-PropTrunc
open import SpartanMLTT

module DcpoFunctionSpace (pt : propositional-truncations-exist)
             (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
             (𝓥 : Universe) -- where the index set for directed completeness lives
       where

open PropositionalTruncation pt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import Dcpos pt fe 𝓥

[_,_]-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → [ 𝓓 , 𝓔 ] → [ 𝓓 , 𝓔 ] → 𝓤 ⊔ 𝓣' ̇
[ 𝓓 , 𝓔 ]-⊑ (f , _) (g , _) = ∀ d → f d ⊑⟨ 𝓔 ⟩ g d

pointwise-family : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) {I : 𝓥 ̇} (α : I → [ 𝓓 , 𝓔 ])
                 → ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
pointwise-family 𝓓 𝓔 α d i = underlying-function 𝓓 𝓔 (α i) d

pointwise-family-is-directed : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) {I : 𝓥 ̇}
                             (α : I → [ 𝓓 , 𝓔 ])
                             (δ : is-directed [ 𝓓 , 𝓔 ]-⊑ α)
                             (d : ⟨ 𝓓 ⟩)
                             → is-directed (underlying-order 𝓔) (pointwise-family 𝓓 𝓔 α d)
pointwise-family-is-directed 𝓓 𝓔 {I} α δ d i j = ∥∥-functor h (δ i j) where
 β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
 β = pointwise-family 𝓓 𝓔 α
 h : Σ (\k → [ 𝓓 , 𝓔 ]-⊑ (α i) (α k) × [ 𝓓 , 𝓔 ]-⊑ (α j) (α k))
     → Σ (\k → (β d i) ⊑⟨ 𝓔 ⟩ (β d k) × (β d j) ⊑⟨ 𝓔 ⟩ (β d k))
 h (k , l , m) = k , l d , m d

continuous-functions-sup : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) {I : 𝓥 ̇}
                         → (α : I → [ 𝓓 , 𝓔 ])
                         → is-directed [ 𝓓 , 𝓔 ]-⊑ α
                         → [ 𝓓 , 𝓔 ]
continuous-functions-sup 𝓓 𝓔 {I} α δ = f , c where
 β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
 β d = pointwise-family 𝓓 𝓔 α d
 ε : (d : ⟨ 𝓓 ⟩) → is-directed (underlying-order 𝓔) (β d)
 ε = pointwise-family-is-directed 𝓓 𝓔 α δ
 
 f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
 f d = ∐ 𝓔 {I} {β d} (ε d)
 c : is-continuous 𝓓 𝓔 f
 c J γ φ = u , v where
  u : (j : J) → f (γ j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
  u j = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (γ j)) (f (∐ 𝓓 φ)) r where
   r : (i : I) → pr₁ (α i) (γ j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
   r i = transitivity 𝓔 _ _ _ p q where
    p : pr₁ (α i) (γ j) ⊑⟨ 𝓔 ⟩ pr₁ (α i) (∐ 𝓓 φ)
    p = continuous-functions-are-monotone 𝓓 𝓔 (underlying-function 𝓓 𝓔 (α i))
        (continuity-of-function 𝓓 𝓔 (α i))  (γ j) (∐ 𝓓 φ) (∐-is-upperbound 𝓓 φ j)
    q : pr₁ (α i) (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
    q = ∐-is-upperbound 𝓔 (ε (∐ 𝓓 φ)) i
  v : (y : ⟨ 𝓔 ⟩)
    → ((j : J) → f (γ j) ⊑⟨ 𝓔 ⟩ y)
    → f (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ y
  v y l = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (∐ 𝓓 φ)) y r where
   r : (i : I) → β (∐ 𝓓 φ) i ⊑⟨ 𝓔 ⟩ y
   r i = transitivity 𝓔 _ _ _ p q where
    p : β (∐ 𝓓 φ) i ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
    p = ∐-is-upperbound 𝓔 (ε (∐ 𝓓 φ)) i
    q : f (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ y
    q = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (∐ 𝓓 φ)) y h where
     h : (i' : I) → β (∐ 𝓓 φ) i' ⊑⟨ 𝓔 ⟩ y
     h i' = is-sup-is-lowerbound-of-upperbounds (underlying-order 𝓔)
            (continuity-of-function 𝓓 𝓔 (α i') J γ φ) y w where
      w : (j : J) → pr₁ (α i') (γ j) ⊑⟨ 𝓔 ⟩ y
      w j = transitivity 𝓔 _ (f (γ j)) _ w₁ w₂ where
       w₁ : pr₁ (α i') (γ j) ⊑⟨ 𝓔 ⟩ (f (γ j))
       w₁ = ∐-is-upperbound 𝓔 (ε (γ j)) i'
       w₂ : f (γ j) ⊑⟨ 𝓔 ⟩ y
       w₂ = l j

DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'}
          → DCPO {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
DCPO[ 𝓓 , 𝓔 ] = [ 𝓓 , 𝓔 ] , [ 𝓓 , 𝓔 ]-⊑ , d where
 d : dcpo-axioms [ 𝓓 , 𝓔 ]-⊑
 d = s , p , r , t , a , c
  where
   s : is-set [ 𝓓 , 𝓔 ]
   s = subsets-of-sets-are-sets (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (is-continuous 𝓓 𝓔)
       (Π-is-set fe (λ (x : ⟨ 𝓓 ⟩) →  sethood 𝓔))
       (λ {f} → being-continuous-is-a-prop 𝓓 𝓔 f)
   p : (f g : [ 𝓓 , 𝓔 ]) → is-prop ([ 𝓓 , 𝓔 ]-⊑ f g)
   p f g = Π-is-prop fe (λ (x : ⟨ 𝓓 ⟩) → prop-valuedness 𝓔 (pr₁ f x) (pr₁ g x))
   r : (f : [ 𝓓 , 𝓔 ]) → [ 𝓓 , 𝓔 ]-⊑ f f
   r f x = reflexivity 𝓔 (pr₁ f x)
   t : (f g h : [ 𝓓 , 𝓔 ]) → [ 𝓓 , 𝓔 ]-⊑ f g → [ 𝓓 , 𝓔 ]-⊑ g h → [ 𝓓 , 𝓔 ]-⊑ f h
   t f g h l m x = transitivity 𝓔 (pr₁ f x) (pr₁ g x) (pr₁ h x) (l x) (m x)
   a : (f g : [ 𝓓 , 𝓔 ]) → [ 𝓓 , 𝓔 ]-⊑ f g → [ 𝓓 , 𝓔 ]-⊑ g f → f ≡ g
   a f g l m = to-Σ-≡ ((dfunext fe (λ d → antisymmetry 𝓔
                                          ((underlying-function 𝓓 𝓔 f) d)
                                          ((underlying-function 𝓓 𝓔 g) d)
                                          (l d) (m d))) ,
                                   being-continuous-is-a-prop 𝓓 𝓔
                                   (underlying-function 𝓓 𝓔 g)
                                   (transport (is-continuous 𝓓 𝓔)
                                     (pr₁ (pr₁ (fe (underlying-function 𝓓 𝓔 f)
                                                   (underlying-function 𝓓 𝓔 g)))
                                      (λ d₁ → _)) _ )
                                   (continuity-of-function 𝓓 𝓔 g))
   c : (I : _ ̇) (α : I → [ 𝓓 , 𝓔 ])
     → is-directed [ 𝓓 , 𝓔 ]-⊑ α → has-sup [ 𝓓 , 𝓔 ]-⊑ α
   c I α δ = (continuous-functions-sup 𝓓 𝓔 α δ) , u , v
    where
     u : (i : I) → [ 𝓓 , 𝓔 ]-⊑ (α i) (continuous-functions-sup 𝓓 𝓔 α δ)
     u i d = ∐-is-upperbound 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d) i
     v : (g : [ 𝓓 , 𝓔 ])
       → ((i : I) → [ 𝓓 , 𝓔 ]-⊑ (α i) g)
       → [ 𝓓 , 𝓔 ]-⊑ (continuous-functions-sup 𝓓 𝓔 α δ) g
     v g l d = ∐-is-lowerbound-of-upperbounds 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d)
               ((underlying-function 𝓓 𝓔 g) d) (λ (i : I) → l i d)

DCPO'[_,_] : DCPO {𝓤₁} {𝓤₀} → DCPO {𝓤₁} {𝓤₀} → DCPO {𝓥 ⁺} {𝓤₁}
DCPO'[_,_] = DCPO[_,_]

DCPO''[_,_] : DCPO {𝓤₁} {𝓤₁} → DCPO {𝓤₁} {𝓤₁} → DCPO {𝓥 ⁺} {𝓤₁}
DCPO''[_,_] = DCPO[_,_]

\end{code}
