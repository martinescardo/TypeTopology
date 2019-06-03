Tom de Jong & Martin Escardo, 27 May 2019.

TO DO
*
*
*

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-PropTrunc
open import SpartanMLTT

module DcpoConstructions
       (pt : propositional-truncations-exist)
       (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

open PropositionalTruncation pt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open import NaturalsOrder
open import NaturalsAddition renaming (_+_ to _+'_)

\end{code}

We start by defining the dcpo of continuous functions. This is the exponential
(or internal hom) in the category of dcpos (hence, the notation ⟹ᵈᶜᵖᵒ).

\begin{code}

module DCPOConstructionsGeneral
       (𝓥 : Universe)
       where
 open import Dcpos pt fe 𝓥

 module _
  (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
  where

  _hom-⊑_ : DCPO[ 𝓓 , 𝓔 ] → DCPO[ 𝓓 , 𝓔 ] → 𝓤 ⊔ 𝓣' ̇
  (f , _) hom-⊑ (g , _) = ∀ d → f d ⊑⟨ 𝓔 ⟩ g d

  pointwise-family : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ]) → ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
  pointwise-family α d i = underlying-function 𝓓 𝓔 (α i) d

  pointwise-family-is-directed : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ])
                                 (δ : is-directed _hom-⊑_ α)
                                 (d : ⟨ 𝓓 ⟩)
                               → is-directed (underlying-order 𝓔)
                                 (pointwise-family α d)
  pointwise-family-is-directed {I} α δ d =
   (is-directed-inhabited _hom-⊑_ α δ) ,
   λ (i j : I) → ∥∥-functor (h i j) ((is-directed-order _hom-⊑_ α δ) i j)
    where
     β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
     β = pointwise-family α
     h : (i j : I) → Σ (\(k : I) → α i hom-⊑ α k × α j hom-⊑ α k)
         → Σ (\k → (β d i) ⊑⟨ 𝓔 ⟩ (β d k) × (β d j) ⊑⟨ 𝓔 ⟩ (β d k))
     h i j (k , l , m) = k , l d , m d

  continuous-functions-sup : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ])
                           → is-directed _hom-⊑_ α → DCPO[ 𝓓 , 𝓔 ]
  continuous-functions-sup {I} α δ = f , c
   where
    β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
    β d = pointwise-family α d
    ε : (d : ⟨ 𝓓 ⟩) → is-directed (underlying-order 𝓔) (β d)
    ε = pointwise-family-is-directed α δ
    f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
    f d = ∐ 𝓔 {I} {β d} (ε d)
    c : is-continuous 𝓓 𝓔 f
    c J γ φ = u , v
     where
      u : (j : J) → f (γ j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
      u j = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (γ j)) (f (∐ 𝓓 φ)) r
       where
        r : (i : I) → underlying-function 𝓓 𝓔 (α i) (γ j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
        r i = transitivity 𝓔
              (underlying-function 𝓓 𝓔 (α i) (γ j))
              (underlying-function 𝓓 𝓔 (α i) (∐ 𝓓 φ))
              (f (∐ 𝓓 φ)) p q
         where
          p : underlying-function 𝓓 𝓔 (α i) (γ j) ⊑⟨ 𝓔 ⟩
              underlying-function 𝓓 𝓔 (α i) (∐ 𝓓 φ)
          p = continuous-functions-are-monotone 𝓓 𝓔 (α i) (γ j) (∐ 𝓓 φ)
              (∐-is-upperbound 𝓓 φ j)
          q : underlying-function 𝓓 𝓔 (α i) (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
          q = ∐-is-upperbound 𝓔 (ε (∐ 𝓓 φ)) i
      v : (y : ⟨ 𝓔 ⟩)
        → ((j : J) → f (γ j) ⊑⟨ 𝓔 ⟩ y)
        → f (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ y
      v y l = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (∐ 𝓓 φ)) y r
       where
        r : (i : I) → β (∐ 𝓓 φ) i ⊑⟨ 𝓔 ⟩ y
        r i = transitivity 𝓔 (β (∐ 𝓓 φ) i) (f (∐ 𝓓 φ)) y p q
         where
          p : β (∐ 𝓓 φ) i ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
          p = ∐-is-upperbound 𝓔 (ε (∐ 𝓓 φ)) i
          q : f (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ y
          q = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (∐ 𝓓 φ)) y h
           where
            h : (i' : I) → β (∐ 𝓓 φ) i' ⊑⟨ 𝓔 ⟩ y
            h i' = is-sup-is-lowerbound-of-upperbounds (underlying-order 𝓔)
                   (continuity-of-function 𝓓 𝓔 (α i') J γ φ) y m
             where
              m : (j : J) → underlying-function 𝓓 𝓔 (α i') (γ j) ⊑⟨ 𝓔 ⟩ y
              m j = transitivity 𝓔
                    (underlying-function 𝓓 𝓔 (α i') (γ j)) (f (γ j)) y m₁ m₂
               where
                m₁ : underlying-function 𝓓 𝓔 (α i') (γ j) ⊑⟨ 𝓔 ⟩ (f (γ j))
                m₁ = ∐-is-upperbound 𝓔 (ε (γ j)) i'
                m₂ : f (γ j) ⊑⟨ 𝓔 ⟩ y
                m₂ = l j

 _⟹ᵈᶜᵖᵒ_ : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'}
         → DCPO {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 = DCPO[ 𝓓 , 𝓔 ] , _⊑_ , d
  where
   _⊑_ = 𝓓 hom-⊑ 𝓔
   d : dcpo-axioms _⊑_
   d = s , p , r , t , a , c
    where
     s : is-set DCPO[ 𝓓 , 𝓔 ]
     s = subsets-of-sets-are-sets (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (is-continuous 𝓓 𝓔)
         (Π-is-set fe (λ (x : ⟨ 𝓓 ⟩) →  sethood 𝓔))
         (λ {f} → being-continuous-is-a-prop 𝓓 𝓔 f)
     p : (f g : DCPO[ 𝓓 , 𝓔 ]) → is-prop (f ⊑ g)
     p (f , _) (g , _) = Π-is-prop fe
                         (λ (x : ⟨ 𝓓 ⟩) → prop-valuedness 𝓔 (f x) (g x))
     r : (f : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ f 
     r (f , _) x = reflexivity 𝓔 (f x)
     t : (f g h : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ g → g ⊑ h → f ⊑ h
     t (f , _) (g , _) (h , _) l m x = transitivity 𝓔 (f x) (g x) (h x)
                                       (l x) (m x)
     a : (f g : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ g → g ⊑ f → f ≡ g
     a f g l m =
      to-Σ-≡
       (dfunext fe
        (λ d → antisymmetry 𝓔
               ((underlying-function 𝓓 𝓔 f) d)
               ((underlying-function 𝓓 𝓔 g) d)
               (l d) (m d)) ,
       being-continuous-is-a-prop 𝓓 𝓔 (underlying-function 𝓓 𝓔 g) _
        (continuity-of-function 𝓓 𝓔 g))
     c : (I : _ ̇) (α : I → DCPO[ 𝓓 , 𝓔 ]) → is-directed _⊑_ α → has-sup _⊑_ α
     c I α δ = (continuous-functions-sup 𝓓 𝓔 α δ) , u , v
      where
       u : (i : I) → α i ⊑ continuous-functions-sup 𝓓 𝓔 α δ
       u i d = ∐-is-upperbound 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d) i
       v : (g : DCPO[ 𝓓 , 𝓔 ])
         → ((i : I) → α i ⊑ g)
         → continuous-functions-sup 𝓓 𝓔 α δ ⊑ g
       v (g , _) l d = ∐-is-lowerbound-of-upperbounds 𝓔
                       (pointwise-family-is-directed 𝓓 𝓔 α δ d)
                       (g d) (λ (i : I) → l i d)

 _⟹ᵈᶜᵖᵒ⊥_ : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'}
          → DCPO⊥ {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓔 = ⟪ 𝓓 ⟫ ⟹ᵈᶜᵖᵒ ⟪ 𝓔 ⟫ , h
  where
   h : has-least (underlying-order (⟪ 𝓓 ⟫ ⟹ᵈᶜᵖᵒ ⟪ 𝓔 ⟫))
   h = ((λ _ → the-least 𝓔) ,
       constant-function-is-continuous ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ (the-least 𝓔)) ,
       (λ g d → least-property 𝓔 (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g d))

\end{code}

Next is the construction of the least fixed point operator for dcpos with bottom.
At the end, we have to specialise to 𝓤₀-dcpos (directed completeness for the
lowest universe), because ℕ lives in 𝓤₀.

\begin{code}

 module _
   (𝓓 : DCPO⊥ {𝓤} {𝓣})
   where

  iter : (n : ℕ) → ⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩ → ⟨ ⟪ 𝓓 ⟫ ⟩
  iter zero     f = the-least 𝓓
  iter (succ n) f = underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (iter n f)

  iter-is-monotone : (n : ℕ) → is-monotone ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter n)
  iter-is-monotone zero     f g l = least-property 𝓓 (iter zero g)
  iter-is-monotone (succ n) f g l =
   transitivity ⟪ 𝓓 ⟫
    (iter (succ n) f)
    (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ g (iter n f))
    (iter (succ n) g)
    (l (iter n f))
    (continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ g (iter n f) (iter n g)
     (iter-is-monotone n f g l))

  n-family : {I : 𝓥 ̇} (α : I → ⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩) (n : ℕ) → I → ⟨ ⟪ 𝓓 ⟫ ⟩
  n-family α n i = iter n (α i)

  n-family-is-directed : {I : 𝓥 ̇} (α : I → ⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩)
                         (δ : is-Directed ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α)
                         (n : ℕ) → is-Directed ⟪ 𝓓 ⟫ (n-family α n)
  n-family-is-directed {I} α δ n = is-Directed-inhabited ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α δ , ε
   where
    ε : (i j : I) → ∃ (\(k : I) → (n-family α n i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k) ×
                                  (n-family α n j) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k))
    ε i j = ∥∥-functor h (is-Directed-order ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α δ i j)
     where
      h : Σ (\(k : I) → (α i) ⊑⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩ (α k) ×
                        (α j) ⊑⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩ (α k))
          → Σ (\(k : I) → (n-family α n i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k) ×
                          (n-family α n j) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ (n-family α n k))
      h (k , l , m) = k , (iter-is-monotone n (α i) (α k) l) ,
                      (iter-is-monotone n (α j) (α k) m)

  double-∐-lemma : {I : 𝓥 ̇} (α : I → ⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩)
                   (δ : is-Directed ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α)
                   (n : ℕ)
                 → ∐ ⟪ 𝓓 ⟫ (pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α δ
                    (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))
                   ≡ ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))
  double-∐-lemma {I} α δ n = antisymmetry ⟪ 𝓓 ⟫ x y a b
   where
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
    a = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ ε y g
     where
      g : (i : I)
        → (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α (∐ ⟪ 𝓓 ⟫ (φ n)) i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ y
      g i = is-sup-is-lowerbound-of-upperbounds (underlying-order ⟪ 𝓓 ⟫) s y u
       where
        β : I → ⟨ ⟪ 𝓓 ⟫ ⟩
        β = underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i) ∘ (n-family α n)
        s : is-sup (underlying-order ⟪ 𝓓 ⟫)
            (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α (∐ ⟪ 𝓓 ⟫ (φ n)) i) β
        s = continuity-of-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i) I (n-family α n) (φ n)
        u : (j : I) → underlying-order ⟪ 𝓓 ⟫ (β j) y
        u j = ∥∥-rec (prop-valuedness ⟪ 𝓓 ⟫ (β j) y) v
               (is-Directed-order ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ α δ i j)
                where
          v : Σ (\(k : I) → α i ⊑⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩ α k
                × α j ⊑⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟩ α k)
            → β j ⊑⟨ ⟪ 𝓓 ⟫ ⟩ y
          v (k , l , m) = transitivity ⟪ 𝓓 ⟫ (β j) (iter (succ n) (α k)) y p q
           where
            q : iter (succ n) (α k) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ y
            q = ∐-is-upperbound ⟪ 𝓓 ⟫ (φ (succ n)) k
            p : β j ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ n) (α k)
            p = transitivity ⟪ 𝓓 ⟫
                (β j)
                (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k) (iter n (α j)))
                (iter (succ n) (α k))
                p₀ p₁
             where
              p₀ : β j ⊑⟨ ⟪ 𝓓 ⟫ ⟩ underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k)
                                   (iter n (α j))
              p₀ = l (iter n (α j))
              p₁ : underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k) (iter n (α j))
                   ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ n) (α k)
              p₁ = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α k)
                   (iter n (α j))
                   (iter n (α k))
                   (iter-is-monotone n (α j) (α k) m)

    b : y ⊑⟨ ⟪ 𝓓 ⟫ ⟩ x
    b = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ (φ (succ n)) x h
     where
      h : (i : I) → (n-family α (succ n) i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ x
      h i = transitivity ⟪ 𝓓 ⟫ (n-family α (succ n) i)
             (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i) (∐ ⟪ 𝓓 ⟫ (φ n))) x p q
       where
        p : iter (succ n) (α i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i)
                                            (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
        p = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i)
             (iter n (α i))
             (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
             (∐-is-upperbound ⟪ 𝓓 ⟫ (φ n) i)
        q : (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ (α i)
             (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))
            ⊑⟨ ⟪ 𝓓 ⟫ ⟩ x
        q = ∐-is-upperbound ⟪ 𝓓 ⟫ ε i

  iter-is-continuous : (n : ℕ) → is-continuous ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter n)
  iter-is-continuous zero     I α δ = a , b
   where
    a : (i : I) → iter zero (α i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩
                  iter zero (∐ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ {I} {α} δ)
    a i = least-property 𝓓 (iter zero (∐ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ {I} {α} δ))
    b : (u : ⟨ ⟪ 𝓓 ⟫ ⟩)
      → ((i : I) → iter zero (α i) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ u)
      → iter zero (∐ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ {I} {α} δ) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ u
    b u l = least-property 𝓓 u 
  iter-is-continuous (succ n) I α δ = γ
   where
    γ : is-sup (underlying-order ⟪ 𝓓 ⟫)
        (iter (succ n) (∐ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ δ)) (iter (succ n) ∘ α)
    γ = transport
        (λ - → is-sup (underlying-order ⟪ 𝓓 ⟫) - (iter (succ n) ∘ α)) (h ⁻¹) k
     where
      k : is-sup (underlying-order ⟪ 𝓓 ⟫)
          (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n)))
          (iter (succ n) ∘ α)
      k = ∐-is-sup ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))
      h = iter (succ n) s                                                          ≡⟨ refl ⟩
          underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ s (iter n s)                             ≡⟨ ap (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ s) e ⟩
          underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ s (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)) ≡⟨ refl ⟩
          ∐ ⟪ 𝓓 ⟫ (pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ α δ
           (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)))                                 ≡⟨ double-∐-lemma α δ n ⟩
          ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ (succ n))                              ∎
       where
        s = (∐ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ {I} {α} δ)
        e : iter n s ≡ ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)
        e = antisymmetry ⟪ 𝓓 ⟫ (iter n s) (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)) l m
         where
          IH : is-sup (underlying-order ⟪ 𝓓 ⟫) (iter n (∐ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ δ))
               (iter n ∘ α)
          IH = iter-is-continuous n I α δ
          l : iter n s ⊑⟨ ⟪ 𝓓 ⟫ ⟩ ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n)
          l = is-sup-is-lowerbound-of-upperbounds (underlying-order ⟪ 𝓓 ⟫) IH
              (∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
              (∐-is-upperbound ⟪ 𝓓 ⟫ (n-family-is-directed α δ n))
          m : ∐ ⟪ 𝓓 ⟫ (n-family-is-directed α δ n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter n s
          m = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ (n-family-is-directed α δ n) (iter n s)
              (is-sup-is-upperbound (underlying-order ⟪ 𝓓 ⟫) IH)

  iter-c : ℕ → DCPO[ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]
  iter-c n = iter n , iter-is-continuous n

  iter-is-ω-chain : (n : ℕ) → (iter-c n) ⊑⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟹ᵈᶜᵖᵒ ⟪ 𝓓 ⟫ ⟩
                              (iter-c (succ n))
  iter-is-ω-chain zero     f = least-property 𝓓 (iter (succ zero) f)
  iter-is-ω-chain (succ n) f = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f
                               (iter n f)
                               (iter (succ n) f)
                               (iter-is-ω-chain n f)

  iter-increases : (n m : ℕ) → (n ≤ m)
                 → (iter-c n) ⊑⟨ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟹ᵈᶜᵖᵒ ⟪ 𝓓 ⟫ ⟩ (iter-c m)
  iter-increases n zero l     f = transport (λ - → iter - f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter zero f)
                                  (unique-minimal n l ⁻¹)
                                  (reflexivity ⟪ 𝓓 ⟫ (iter zero f))
  iter-increases n (succ m) l f = h (≤-split n m l)
   where
    h : (n ≤ m) + (n ≡ succ m) → (iter n f) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ m) f
    h (inl l') = transitivity ⟪ 𝓓 ⟫ (iter n f) (iter m f) (iter (succ m) f)
                 (iter-increases n m l' f)
                 (iter-is-ω-chain m f)
    h (inr e)  = transport (λ - → iter - f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter (succ m) f) (e ⁻¹)
                 (reflexivity ⟪ 𝓓 ⟫ (iter (succ m) f))

module DCPOConstructions₀
       where
 open DCPOConstructionsGeneral 𝓤₀
 open import Dcpos pt fe 𝓤₀
 module _
        (𝓓 : DCPO⊥ {𝓤} {𝓣})
        where

  iter-is-directed : is-directed (λ F G → ∀ f → F f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ G f) (iter 𝓓) 
  iter-is-directed = ∣ zero ∣ , δ
   where
    δ : (i j : ℕ) → ∃ (\(k : ℕ) →
             ((f : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]) → iter 𝓓 i f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter 𝓓 k f)
             ×
             ((f : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]) → iter 𝓓 j f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter 𝓓 k f))
    δ i j = ∣ i +' j , l , m ∣
     where
      l : (f : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]) → iter 𝓓 i f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter 𝓓 (i +' j) f
      l = iter-increases 𝓓 i (i +' j)
          (cosubtraction i (i +' j) (j , (addition-commutativity j i)))
      m : (f : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]) → iter 𝓓 j f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ iter 𝓓 (i +' j) f
      m = iter-increases 𝓓 j (i +' j) (cosubtraction j (i +' j) (i , refl))

  μ : DCPO[ ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ]
  μ = continuous-functions-sup ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) iter-is-directed

  μ-gives-a-fixed-point : (f : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ])
                        → underlying-function ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ μ f
                          ≡ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f
                            (underlying-function ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ μ f))
  μ-gives-a-fixed-point fc = antisymmetry ⟪ 𝓓 ⟫ (ν fc) (f (ν fc)) l m
   where
    ν : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ] → ⟨ ⟪ 𝓓 ⟫ ⟩
    ν = underlying-function ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ μ
    f : ⟨ ⟪ 𝓓 ⟫ ⟩ → ⟨ ⟪ 𝓓 ⟫ ⟩
    f = underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ fc
    δ : is-directed (underlying-order ⟪ 𝓓 ⟫)
     (pointwise-family ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) fc)
    δ = pointwise-family-is-directed ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓)
        iter-is-directed fc

    l : ν fc ⊑⟨ ⟪ 𝓓 ⟫ ⟩ f (ν fc)
    l = ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫ δ (f (ν fc)) h
     where
      h : (n : ℕ) → iter 𝓓 n fc ⊑⟨ ⟪ 𝓓 ⟫ ⟩ f (ν fc)
      h zero     = least-property 𝓓 (f (ν fc))
      h (succ n) = continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ fc
                   (iter 𝓓 n fc)
                   (ν fc)
                   (∐-is-upperbound ⟪ 𝓓 ⟫ δ n)

    m : f (ν fc) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ ν fc
    m = is-sup-is-lowerbound-of-upperbounds (underlying-order ⟪ 𝓓 ⟫)
        (continuity-of-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ fc ℕ α δ) (ν fc) k
     where
      α : ℕ → ⟨ ⟪ 𝓓 ⟫ ⟩
      α = pointwise-family ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓) fc
      k : (n : ℕ) → underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ fc (α n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ ν fc
      k n = transitivity ⟪ 𝓓 ⟫
            (f (α n)) (α (succ n)) (ν fc)
            p q
       where
        p : underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ fc (α n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ α (succ n)
        p = reflexivity ⟪ 𝓓 ⟫ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ fc (α n))
        q : α (succ n) ⊑⟨ ⟪ 𝓓 ⟫ ⟩ ν fc
        q = ∐-is-upperbound ⟪ 𝓓 ⟫ δ (succ n)

  μ-gives-lowerbound-of-fixed-points : (f : DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓓 ⟫ ])
                                       (d : ⟨ ⟪ 𝓓 ⟫ ⟩)
                                     → underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f d
                                       ⊑⟨ ⟪ 𝓓 ⟫ ⟩ d
                                     → (underlying-function ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ μ) f
                                       ⊑⟨ ⟪ 𝓓 ⟫ ⟩ d
  μ-gives-lowerbound-of-fixed-points f d l =
   ∐-is-lowerbound-of-upperbounds ⟪ 𝓓 ⟫
   (pointwise-family-is-directed ⟪ 𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓓 ⟫ ⟪ 𝓓 ⟫ (iter-c 𝓓)
    iter-is-directed f)
   d g
    where
     g : (n : ℕ) → iter 𝓓 n f ⊑⟨ ⟪ 𝓓 ⟫ ⟩ d
     g zero     = least-property 𝓓 d
     g (succ n) = transitivity ⟪ 𝓓 ⟫
                  (iter 𝓓 (succ n) f) (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f d) d
                  (continuous-functions-are-monotone ⟪ 𝓓 ⟫ ⟪ 𝓓 ⟫ f (iter 𝓓 n f) d (g n))
                  l
{-

module _
  (𝓓 : DCPO⊥ {𝓤} {𝓣})
  (𝓔 : DCPO⊥ {𝓤'} {𝓣'})
  (𝓕 : DCPO⊥ {𝓦} {𝓦'})
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

 ⦅S⦆₀ : [ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] → [ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] → [ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ]
 ⦅S⦆₀ f g = (λ x → pr₁ (pr₁ f x) (pr₁ g x)) , c
  where
   c : is-continuous ⟪ 𝓓 ⟫ ⟪ 𝓕 ⟫ (λ x → pr₁ (pr₁ f x) (pr₁ g x))
   c I α δ = u , v
    where
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
     v y ineqs = γ
      where
       γ : pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (pr₁ g (∐ ⟪ 𝓓 ⟫ δ)) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
       γ = transport (λ - → pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) - ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y) e₀ γ₀
        where
         e₀ : ∐ ⟪ 𝓔 ⟫ (image-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g δ) ≡ pr₁ g (∐ ⟪ 𝓓 ⟫ δ)
         e₀ = (continuous-function-∐-≡ ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g δ) ⁻¹
         ε₀ : is-Directed ⟪ 𝓔 ⟫ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g ∘ α)
         ε₀ = image-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g δ
         γ₀ : (pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (∐ ⟪ 𝓔 ⟫ ε₀)) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
         γ₀ = transport (λ - → - ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y) e₁ γ₁
          where
           e₁ : ∐ ⟪ 𝓕 ⟫ (image-is-directed ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) ε₀) ≡ pr₁ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) (∐ ⟪ 𝓔 ⟫ ε₀)
           e₁ = (continuous-function-∐-≡ ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) ε₀) ⁻¹
           ε₁ : is-Directed ⟪ 𝓕 ⟫
                (underlying-function ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) ∘ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g ∘ α))
           ε₁ = image-is-directed ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ)) ε₀
           γ₁ : (∐ ⟪ 𝓕 ⟫ ε₁) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
           γ₁ = ∐-is-lowerbound-of-upperbounds ⟪ 𝓕 ⟫ ε₁ y γ₂
            where
             γ₂ : (i : I)
                → (underlying-function ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f (∐ ⟪ 𝓓 ⟫ δ))) (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g (α i)) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
             γ₂ i = transport (λ - → (underlying-function ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ -) (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ g (α i)) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y ) e₂ γ₃
              where
               ε₂ : is-Directed DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] (underlying-function ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f ∘ α)
               ε₂ = image-is-directed ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f δ
               e₂ : ∐ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ε₂ ≡ pr₁ f (∐ ⟪ 𝓓 ⟫ δ)
               e₂ = (continuous-function-∐-≡ ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f δ) ⁻¹
               γ₃ : pr₁ (∐ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] {I} {pr₁ f ∘ α} ε₂) (pr₁ g (α i)) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
               γ₃ = ∐-is-lowerbound-of-upperbounds ⟪ 𝓕 ⟫ (pointwise-family-is-directed ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f ∘ α) ε₂ (pr₁ g (α i))) y h
                where
                 h : (j : I) → (pr₁ (pr₁ f (α j)) (pr₁ g (α i))) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ y
                 h j = ∥∥-rec (prop-valuedness ⟪ 𝓕 ⟫ (pr₁ (pr₁ f (α j)) (pr₁ g (α i))) y) r (is-Directed-order ⟪ 𝓓 ⟫ α δ i j)
                  where
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

 ⦅S⦆₁ : [ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] → [ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ]
 ⦅S⦆₁ f = (⦅S⦆₀ f) , c
  where
   c : is-continuous DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] (⦅S⦆₀ f)
   c I α δ = u , v
    where
     u : (i : I) (d : ⟨ ⟪ 𝓓 ⟫ ⟩) → pr₁ (⦅S⦆₀ f (α i)) d ⊑⟨ ⟪ 𝓕 ⟫ ⟩ pr₁ (⦅S⦆₀ f (∐ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] {I} {α} δ)) d
     u i d = continuous-functions-are-monotone ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (pr₁ f d) (pr₁ (α i) d) (pr₁ (∐ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] {I} {α} δ) d)
             (∐-is-upperbound ⟪ 𝓔 ⟫ (pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ α δ d) i)
     v : (g : ⟨ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ⟩)
       → ((i : I) → underlying-order DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] (⦅S⦆₀ f (α i)) g)
       → (d : ⟨ ⟪ 𝓓 ⟫ ⟩) → pr₁ (⦅S⦆₀ f (∐ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] {I} {α} δ)) d ⊑⟨ ⟪ 𝓕 ⟫ ⟩ pr₁ g d
     v g l d = transport (λ - → - ⊑⟨ ⟪ 𝓕 ⟫ ⟩ pr₁ g d) e s
      where
       ε : is-Directed ⟪ 𝓔 ⟫ (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ α d)
       ε = pointwise-family-is-directed ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ α δ d
       e : ∐ ⟪ 𝓕 ⟫ (image-is-directed ⟪ 𝓔 ⟫ (pr₁ 𝓕) (pr₁ f d) ε) ≡ pr₁ (⦅S⦆₀ f (∐ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] {I} {α} δ)) d
       e = (continuous-function-∐-≡ ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ ((underlying-function ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f) d) ε) ⁻¹
       φ : is-Directed ⟪ 𝓕 ⟫ (underlying-function ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ (underlying-function ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f d)
           ∘ (pointwise-family ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ α d))
       φ = image-is-directed ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ ((underlying-function ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] f) d) ε
       s : ∐ ⟪ 𝓕 ⟫ φ ⊑⟨ ⟪ 𝓕 ⟫ ⟩ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓕 ⟫ g) d
       s = ∐-is-lowerbound-of-upperbounds ⟪ 𝓕 ⟫ φ (underlying-function ⟪ 𝓓 ⟫ ⟪ 𝓕 ⟫ g d)
           (λ (i : I) → l i d)

 ⦅S⦆ : [ DCPO[ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] , DCPO[ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ] ]
 ⦅S⦆ = ⦅S⦆₁ , c
  where
   c : is-continuous DCPO[ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] DCPO[ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ] ⦅S⦆₁
   c I α δ = u , v
    where
     u : (i : I) (g : [ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ]) (d : ⟨ ⟪ 𝓓 ⟫ ⟩)
       → pr₁ (pr₁ (α i) d) (pr₁ g d) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ pr₁ (pr₁ (∐ DCPO[ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] {I} {α} δ) d) (pr₁ g d)
     u i g d = ∐-is-upperbound ⟪ 𝓕 ⟫ (pointwise-family-is-directed ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ β ε (pr₁ g d)) i
      where
       β : I → ⟨ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ⟩
       β = pointwise-family ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] α d
       ε : is-Directed DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] β
       ε = pointwise-family-is-directed ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] α δ d
     v : (f : ⟨ DCPO[ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ] ⟩)
       → ((i : I) → underlying-order DCPO[ DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ] , DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓕 ⟫ ] ] (⦅S⦆₁ (α i)) f)
       → (g : [ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ]) (d : ⟨ ⟪ 𝓓 ⟫ ⟩) → pr₁ (pr₁ (∐ DCPO[ ⟪ 𝓓 ⟫ , DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] ] {I} {α} δ) d) (pr₁ g d) ⊑⟨ ⟪ 𝓕 ⟫ ⟩ (pr₁ (pr₁ f g) d)
     v f l g d = ∐-is-lowerbound-of-upperbounds ⟪ 𝓕 ⟫ ε (pr₁ (pr₁ f g) d) (λ (i : I) → l i g d)
      where
       ε : is-Directed ⟪ 𝓕 ⟫ (λ (i : I) → pr₁ (pr₁ (⦅S⦆₁ (α i)) g) d)
       ε = pointwise-family-is-directed ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ β φ (pr₁ g d)
        where
         β : I → [ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ]
         β i = pr₁ (α i) d
         φ : is-Directed DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] β
         φ = pointwise-family-is-directed ⟪ 𝓓 ⟫ DCPO[ ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] α δ d

-}
\end{code}


