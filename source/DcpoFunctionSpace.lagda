Tom de Jong & Martin Escardo, 27 May 2019.

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
open import NaturalsOrder

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
pointwise-family-is-directed 𝓓 𝓔 {I} α δ d =
 (is-directed-inhabited [ 𝓓 , 𝓔 ]-⊑ α δ) ,
 λ (i j : I) → ∥∥-functor (h i j) ((is-directed-order [ 𝓓 , 𝓔 ]-⊑ α δ) i j) where
  β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
  β = pointwise-family 𝓓 𝓔 α
  h : (i j : I) → Σ (\k → [ 𝓓 , 𝓔 ]-⊑ (α i) (α k) × [ 𝓓 , 𝓔 ]-⊑ (α j) (α k))
      → Σ (\k → (β d i) ⊑⟨ 𝓔 ⟩ (β d k) × (β d j) ⊑⟨ 𝓔 ⟩ (β d k))
  h i j (k , l , m) = k , l d , m d

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
    p = continuous-functions-are-monotone 𝓓 𝓔 (α i) (γ j) (∐ 𝓓 φ) (∐-is-upperbound 𝓓 φ j)
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

DCPO⊥[_,_] : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'}
          → DCPO⊥ {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
DCPO⊥[ 𝓓 , 𝓔 ] = DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , h where
 h : has-least ([ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ]-⊑)
 h = ((λ _ → the-least 𝓔) , constant-function-is-continuous ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ (the-least 𝓔)) ,
     λ g d → least-property 𝓔 (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g d)

module _
  (𝓓 : DCPO⊥ {𝓤} {𝓣})
  where

 iter : (n : ℕ) → ⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩ → ⟨ ⟪ 𝓓 ⟫ ⟩
 iter zero     f = the-least 𝓓
 iter (succ n) f = underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (iter n f)

 iter-is-monotone : (n : ℕ) → is-monotone ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter n)
 iter-is-monotone zero     f g l = least-property 𝓓 (iter zero g)
 iter-is-monotone (succ n) f g l = transitivity ⟪ 𝓓 ⟫
                                       (iter (succ n) f)
                                       (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ g (iter n f))
                                       (iter (succ n) g)
                                       (l (iter n f))
                                       (continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ g
                                        (iter n f)
                                        (iter n g)
                                        (iter-is-monotone n f g l))

 n-family : {I : 𝓥 ̇} (α : I → ⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩) (n : ℕ) → I → ⟨ ⟪ 𝓓 ⟫ ⟩
 n-family α n i = iter n (α i)

 n-family-is-directed : {I : 𝓥 ̇} (α : I → ⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩)
                      (δ : is-directed [ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]-⊑ α)
                      (n : ℕ) → is-Directed ⟪ 𝓓 ⟫ (n-family α n)
 n-family-is-directed {I} α δ n =
  is-Directed-inhabited ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ α δ , ε where
   ε : (i j : I) → ∃ (\(k : I) → (n-family α n i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k) ×
                                 (n-family α n j) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k))
   ε i j = ∥∥-functor h (is-Directed-order ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ α δ i j) where
    h : Σ (\(k : I) → (α i) ⊑⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩ (α k) ×
                      (α j) ⊑⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩ (α k))
        → Σ (\(k : I) → (n-family α n i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k) ×
                        (n-family α n j) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k))
    h (k , l , m) = k , (iter-is-monotone n (α i) (α k) l) , (iter-is-monotone n (α j) (α k) m)

 double-∐-lemma : {I : 𝓥 ̇} (α : I → ⟨ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟩)
                (δ : is-directed [ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]-⊑ α)
                (n : ℕ)
                → ∐ ⟪ 𝓓 ⟫ (pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α δ
                   (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))
                  ≡ ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))
 double-∐-lemma {I} α δ n = antisymmetry ⟪ 𝓓 ⟫ x y a b where
  ε : is-Directed ⟪ 𝓓 ⟫ (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α
       (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))
  ε = (pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α δ
       (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))
  φ : (n : ℕ) → is-Directed ⟪ 𝓓 ⟫ (n-family α n)
  φ n = n-family-is-directed α δ n

  x : ⟨ ⟪ 𝓓 ⟫ ⟩
  x = ∐ ⟪ 𝓓 ⟫ ε
  y : ⟨ ⟪ 𝓓 ⟫ ⟩
  y = ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))
  
  a : x ⊑⟨ ⟪ 𝓓 ⟫ ⟩ y
  a = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ ε y g where
   g : (i : I)
     → (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α (∐ ⟪ 𝓓 ⟫ (φ n)) i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ y
   g i = is-sup-is-lowerbound-of-upperbounds (underlying-order ⟪ 𝓓 ⟫) s y u where
    β : I → ⟨ ⟪ 𝓓 ⟫ ⟩
    β = underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i) ∘ (n-family α n)
    s : is-sup (underlying-order ⟪ 𝓓 ⟫) (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α (∐ ⟪ 𝓓 ⟫ (φ n)) i) β
    s = continuity-of-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i) I (n-family α n) (φ n)
    u : (j : I) → underlying-order ⟪ 𝓓 ⟫ (β j) y
    u j = ∥∥-rec (prop-valuedness ⟪ 𝓓 ⟫ (β j) y) v
           (is-Directed-order ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ α δ i j) where
     v : Σ (\(k : I) → [ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]-⊑ (α i) (α k) × [ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]-⊑ (α j) (α k)) →
           underlying-order ⟪ 𝓓 ⟫ (β j) y
     v (k , l , m) = transitivity ⟪ 𝓓 ⟫ (β j) (iter (succ n) (α k)) y p q where
      p : β j ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ n) (α k)
      p = transitivity ⟪ 𝓓 ⟫
          (β j)
          (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k) (iter n (α j)))
          (iter (succ n) (α k))
          p₀ p₁ where
       p₀ : β j ⊑⟨ ⟪ 𝓓 ⟫ ⟩ underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k) (iter n (α j))
       p₀ = l (iter n (α j))
       p₁ : underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k) (iter n (α j)) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ n) (α k)
       p₁ = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k)
            (iter n (α j))
            (iter n (α k))
            (iter-is-monotone n (α j) (α k) m)
      q : iter (succ n) (α k) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ y
      q = ∐-is-upperbound ⟪ 𝓓 ⟫ (φ (succ n)) k

  b : y ⊑⟨ ⟪ 𝓓 ⟫ ⟩ x
  b = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ (φ (succ n)) x h where
   h : (i : I) → (n-family α (succ n) i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ x
   h i = transitivity ⟪ 𝓓 ⟫ (n-family α (succ n) i)
          (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i) (∐ ⟪ 𝓓 ⟫ (φ n))) x p q where
    p : iter (succ n) (α i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i)
                                         (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
    p = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i)
         (iter n (α i))
         (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
         (∐-is-upperbound ⟪ 𝓓 ⟫ (φ n) i)
    q : (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i)
         (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))
        ⊑⟨ ⟪ 𝓓 ⟫ ⟩  x
    q = ∐-is-upperbound ⟪ 𝓓 ⟫ ε i

 iter-is-continuous : (n : ℕ) → is-continuous ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ ⟪ 𝓓 ⟫ (iter n)
 iter-is-continuous zero     I α δ = a , b where
  a : (i : I) → iter zero (α i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter zero (∐ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ {I} {α} δ)
  a i = least-property 𝓓 (iter zero (∐ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ {I} {α} δ))
  b : (u : ⟨ ⟪ 𝓓 ⟫ ⟩)
    → ((i : I) → iter zero (α i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ u)
    → iter zero (∐ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ {I} {α} δ) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ u
  b u l = least-property 𝓓 u
  
 iter-is-continuous (succ n) I α δ = γ where
  γ : is-sup (underlying-order ⟪ 𝓓 ⟫)
      (iter (succ n) (∐ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ δ)) (λ (j : I) → iter (succ n) (α j))
  γ = transport
      (λ - → is-sup (underlying-order ⟪ 𝓓 ⟫) - (λ (j : I) → iter (succ n) (α j)))
      (h ⁻¹) k where
   h = iter (succ n) s                                                          ≡⟨ refl ⟩
       underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ s (iter n s)                             ≡⟨ ap (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ s) e ⟩
       underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ s (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)) ≡⟨ refl ⟩
       ∐ ⟪ 𝓓 ⟫ (pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α δ
        (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))                                 ≡⟨ double-∐-lemma α δ n ⟩
       ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))                              ∎ where
    s = (∐ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ {I} {α} δ)
    e : iter n s ≡ ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)
    e = antisymmetry ⟪ 𝓓 ⟫ (iter n s) (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)) l m where
     IH : is-sup (underlying-order ⟪ 𝓓 ⟫) (iter n (∐ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ δ)) (λ (j : I) → iter n (α j))
     IH = iter-is-continuous n I α δ
     l : iter n s ⊑⟨ ⟪ 𝓓 ⟫ ⟩ ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)
     l = is-sup-is-lowerbound-of-upperbounds (underlying-order ⟪ 𝓓 ⟫) IH
         (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
         (∐-is-upperbound ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
     m : ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter n s
     m = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ (n-family-is-directed α δ n) (iter n s)
         (is-sup-is-upperbound (underlying-order ⟪ 𝓓 ⟫) IH)
   k : is-sup (underlying-order ⟪ 𝓓 ⟫)
       (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n)))
       (λ (j : I) → iter (succ n) (α j))
   k = ∐-is-sup ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))

 iter-c : ℕ → [ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ , ⟪ 𝓓 ⟫ ]
 iter-c n = iter n , iter-is-continuous n

 iter-is-ω-chain : (n : ℕ) → [ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ , ⟪ 𝓓 ⟫ ]-⊑ (iter-c n) (iter-c (succ n))
 iter-is-ω-chain zero     f = least-property 𝓓 (iter (succ zero) f)
 iter-is-ω-chain (succ n) f = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f
                              (iter n f)
                              (iter (succ n) f)
                              (iter-is-ω-chain n f)

 iter-increases : (n m : ℕ) → (n ≤ m) → [ ⟪ DCPO⊥[ 𝓓 , 𝓓 ] ⟫ , ⟪ 𝓓 ⟫ ]-⊑ (iter-c n) (iter-c m)
 iter-increases n zero l     f = transport (λ - → iter - f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter zero f)
                                 (unique-minimal n l ⁻¹)
                                 (reflexivity ⟪ 𝓓 ⟫ (iter zero f))
 iter-increases n (succ m) l f = h (≤-split n m l) where
  h : (n ≤ m) + (n ≡ succ m) → (iter n f) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ m) f
  h (inl l') = transitivity ⟪ 𝓓 ⟫ (iter n f) (iter m f) (iter (succ m) f)
               (iter-increases n m l' f)
               (iter-is-ω-chain m f)
  h (inr e)  = transport (λ - → iter - f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ m) f) (e ⁻¹)
               (reflexivity ⟪ 𝓓 ⟫ (iter (succ m) f))

module _
  (𝓓 : DCPO⊥ {𝓤} {𝓣})
  (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
  (𝓕 : DCPO⊥ {𝓦} {𝓦'}) -- 𝓦 ok?
  where

 ⦅K⦆ : [ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓓 ⟫ ] ]
 ⦅K⦆ = k , c where
  k : ⟨ ⟪ 𝓓 ⟫ ⟩ → ⟨ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓓 ⟫ ] ⟩
  k x = (λ _ → x) , (constant-function-is-continuous ⟪ 𝓔 ⟫ ⟪ 𝓓 ⟫ x)
  c : (I : 𝓥 ̇) (α : I → ⟨ ⟪ 𝓓 ⟫ ⟩) (δ : is-Directed ⟪ 𝓓 ⟫ α)
    → is-sup (underlying-order DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓓 ⟫ ])
      (k (∐ ⟪ 𝓓 ⟫ δ)) (λ (i : I) → k (α i))
  c I α δ = u , v where
   u : (i : I) (e : ⟨ ⟪ 𝓔 ⟫ ⟩) → α i ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (∐ ⟪ 𝓓 ⟫ δ)
   u i e = ∐-is-upperbound ⟪ 𝓓 ⟫ δ i
   v : (f : ⟨ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓓 ⟫ ] ⟩)
     → ((i : I) → [ ⟪ 𝓔 ⟫ , ⟪ 𝓓 ⟫ ]-⊑ (k (α i)) f)
     → (e : ⟨ ⟪ 𝓔 ⟫ ⟩) → ∐ ⟪ 𝓓 ⟫ δ ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (underlying-function ⟪ 𝓔 ⟫ ⟪ 𝓓 ⟫ f e)
   v f l e = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ δ (underlying-function ⟪ 𝓔 ⟫ ⟪ 𝓓 ⟫ f e)
             λ (i : I) → (l i) e

{-
 ⦅S⦆₀ : [ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] → [ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] → [ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ]
 ⦅S⦆₀ f g = (λ x → pr₁ (pr₁ f x) (pr₁ g x)) , c where
  c : is-continuous ⟪ 𝓓 ⟫ ⟪ 𝓕 ⟫ (λ x → pr₁ (pr₁ f x) (pr₁ g x))
  c I α δ = u , v where
   u : (i : I) → (pr₁ (pr₁ f (α i)) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ (pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (∐ ⟪ 𝓓 ⟫ δ)))
   u i = transitivity ⟪ 𝓕 ⟫
         (pr₁ (pr₁ f (α i)) (pr₁ g (α i)))
         (pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (α i)))
         (pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (∐ ⟪ 𝓓 ⟫ δ)))
         (l₁ (pr₁ g (α i)))
         (continuous-functions-are-monotone ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (α i)) (pr₁ g (∐ ⟪ 𝓓 ⟫ δ)) l₀) where
    l₀ : pr₁ g (α i) ⊑⟨ ⟪ 𝓔 ⟫ ⟩ pr₁ g (∐ ⟪ 𝓓 ⟫ δ)
    l₀ = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g (α i) (∐ ⟪ 𝓓 ⟫ δ) (∐-is-upperbound ⟪ 𝓓 ⟫ δ i)
    l₁ : [ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ]-⊑ (pr₁ f (α i)) (pr₁ f (∐ ⟪ 𝓓 ⟫ δ))
    l₁ = continuous-functions-are-monotone ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f (α i) (∐ ⟪ 𝓓 ⟫ δ) (∐-is-upperbound ⟪ 𝓓 ⟫ δ i)
   v : (y : ⟨ ⟪ 𝓕 ⟫ ⟩)
     → ((i : I) → (pr₁ (pr₁ f (α i)) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y)
     → (pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (∐ ⟪ 𝓓 ⟫ δ))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
   v y ineqs = {!!} where
    a : {!!}
    a = {!!}

    β : (i : I) → ⟨ ⟪ 𝓔 ⟫ ⟩
    β i = pr₁ g (α i)
    ε : is-Directed ⟪ 𝓔 ⟫ β
    ε = {!!}
    b : pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (∐ ⟪ 𝓔 ⟫ ε) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
    b = {!!}

    h₁ : (i : I) → (pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
    h₁ i = is-sup-is-lowerbound-of-upperbounds {!!} {!!} {!!} {!!}
    δ₀ : is-Directed {!!} (λ (i : I) → pr₁ f (α i))
    δ₀ = {!!}
    t : (i : I) → (pr₁ (∐ {!!} δ₀) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
    t i = ∐-is-lowerbound-of-upperbounds {!!} δ₀ {!!} (h₂ i)
     where
      h₂ : (i j : I) → (pr₁ (pr₁ f (α j)) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
      h₂ i j = ∥∥-rec (prop-valuedness ⟪ 𝓕 ⟫ (pr₁ (pr₁ f (α j)) (pr₁ g (α i))) y) r (is-Directed-order ⟪ 𝓓 ⟫ α δ i j) where
       r : Σ (\(k : I) → α i ⊑⟨ ⟪ 𝓓 ⟫ ⟩ α k × α j ⊑⟨ ⟪ 𝓓 ⟫ ⟩ α k)
         → (pr₁ (pr₁ f (α j)) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
       r (k , l , m ) = transitivity ⟪ 𝓕 ⟫
                        (pr₁ (pr₁ f (α j)) (pr₁ g (α i)))
                        (pr₁ (pr₁ f (α k)) (pr₁ g (α k)))
                        y
                        (transitivity ⟪ 𝓕 ⟫
                         (pr₁ (pr₁ f (α j)) (pr₁ g (α i)))
                         (pr₁ (pr₁ f (α k)) (pr₁ g (α i)))
                         (pr₁ (pr₁ f (α k)) (pr₁ g (α k)))
                         (s (pr₁ g (α i)))
                         (continuous-functions-are-monotone ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (α k)) (pr₁ g (α i)) (pr₁ g (α k))
                          (continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g (α i) (α k) l)))
                        (ineqs k) where
        s : [ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ]-⊑ (pr₁ f (α j)) (pr₁ f (α k))
        s = continuous-functions-are-monotone ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f (α j) (α k) m

 ⦅S⦆ : [ DCPO[ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] , DCPO[ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ] ]
 ⦅S⦆ = (λ f → (λ g → (λ x → pr₁ (pr₁ f x) (pr₁ g x)) , {!c₂!}) , {!c₁!}) , c₀ where
  c₀ : {!!}
  c₀ = {!!}
  c₁ : {!!}
  c₁ = {!!}
  c₂ : {!!}
  c₂ = {!!}
-}

\end{code}
