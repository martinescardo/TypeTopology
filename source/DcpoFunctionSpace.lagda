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

[_,_]-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) → [ 𝓓 , 𝓔 ] → [ 𝓓 , 𝓔 ] → 𝓤 ⊔ 𝓣' ̇
[ 𝓓 , 𝓔 ]-⊑ (f , _) (g , _) = ∀ d → f d ⊑⟨ 𝓔 ⟩ g d

continuous-functions-sup : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) {I : 𝓥 ̇}
                         → (α : I → [ 𝓓 , 𝓔 ])
                         → is-directed [ 𝓓 , 𝓔 ]-⊑ α
                         → [ 𝓓 , 𝓔 ]
continuous-functions-sup 𝓓 𝓔 {I} α δ = f , c where
 β : (d : ⟨ 𝓓 ⟩) (i : I) → ⟨ 𝓔 ⟩
 β d i = pr₁ (α i) d
 ε : (d : ⟨ 𝓓 ⟩) → is-directed (underlying-order 𝓔) (β d)
 ε d i j = ∥∥-functor h (δ i j) where
  h : Σ (\k → [ 𝓓 , 𝓔 ]-⊑ (α i) (α k) × [ 𝓓 , 𝓔 ]-⊑ (α j) (α k))
      → Σ (\k → (β d i) ⊑⟨ 𝓔 ⟩ (β d k) × (β d j) ⊑⟨ 𝓔 ⟩ (β d k))
  h (k , l , m) = k , l d , m d
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


{-
DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → DCPO {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
DCPO[ (D  , _⊑_   , (s  , p  , r  , t  , a  , c )) ,
      (D' , _⊑'_  , (s' , p' , r' , t' , a' , c')) ] = D'' , _⊑''_ , s'' , p'' , r'' , t'' , a'' , c''
 where
  𝓓 : DCPO {{!𝓤!}} {{!𝓣!}}
  𝓓 = (D  , _⊑_   , (s  , p  , r  , t  , a  , c ))
  𝓔 : DCPO {{!𝓤'!}} {{!𝓣'!}}
  𝓔 = (D' , _⊑'_   , (s'  , p'  , r'  , t'  , a'  , c' ))
  D'' = Σ \(f : D → D') → is-continuous 𝓓 𝓔 f
  _⊑''_ : D'' → D'' → {!𝓤 ⊔ 𝓣'!} ̇
  (f , _) ⊑'' (g , _) = ∀ x → f x ⊑' g x
  s'' : is-set D''
  s'' = subsets-of-sets-are-sets (D → D') (is-continuous 𝓓 𝓔) (Π-is-set (fe {!𝓤!} {!𝓤'!}) (λ (x : D) → s')) λ {f} → being-continuous-is-a-prop 𝓓 𝓔 f
  p'' : (f g : D'') → is-prop (f ⊑'' g)
  p'' f g = Π-is-prop (fe {!𝓤!} {!𝓣'!}) (λ (x : D) → p' (pr₁ f x) (pr₁ g x))
  r'' : (f : D'') → f ⊑'' f
  r'' f x = r' (pr₁ f x)
  t'' : (f g h : D'') → f ⊑'' g → g ⊑'' h → f ⊑'' h
  t'' f g h l m x = t' (pr₁ f x) (pr₁ g x) (pr₁ h x) (l x) (m x)
  a'' : (f g : D'') → f ⊑'' g → g ⊑'' f → f ≡ g
  a'' f g l m = to-Σ-≡ (dfunext (fe {!𝓤!} {!𝓤'!}) (λ x → a' (pr₁ f x) (pr₁ g x) (l x) (m x)) ,
                        being-continuous-is-a-prop 𝓓 𝓔 (pr₁ g)
                             (transport (is-continuous 𝓓 𝓔) _ (pr₂ f)) (pr₂ g))
  c'' : (I : _ ̇) (α : I → D'') →
          is-directed _⊑''_ α → has-sup _⊑''_ α
  c'' I α δ = ((λ x → ∐ 𝓔 (λ i → pr₁ (α i) x) (ε x)) , φ-is-continuous) , γ
   where
    blah : (i : I) → is-continuous 𝓓 𝓔 (pr₁ (α i))
    blah = λ i → pr₂ (α i)
    ε : (x : D) → is-directed _⊑'_ (λ i → pr₁ (α i) x)
    ε  x i j = ∥∥-functor h (δ i j)
     where
      h : (Σ \(k : I) → (α i ⊑'' α k) × (α j ⊑'' α k))
        → Σ \(k : I) → (pr₁ (α i) x ⊑' pr₁ (α k) x) × (pr₁ (α j) x ⊑' pr₁ (α k) x)
      h (k , l , m) = k , (l x) , (m x)
    φ : D → D'
    φ x = ∐ 𝓔 (λ i → pr₁ (α i) x) (ε x)
    φ-is-monotone : is-monotone 𝓓 𝓔 φ
    φ-is-monotone = {!!}
    φ-is-continuous : is-continuous 𝓓 𝓔 φ
    φ-is-continuous J β κ = h , fine
     where
      h : (i j : J) → ∃ \(k : J) → (φ (β i) ⊑' φ (β k)) × (φ (β j) ⊑' φ (β k))
      h i j = ∥∥-functor g (κ i j)
       where
        g : (Σ \(k : J) → (β i ⊑ β k) × (β j ⊑ β k)) → Σ (\(k : J) → (φ (β i) ⊑' φ (β k)) × (φ (β j) ⊑' φ (β k)))
        g (k , l , m) = k , φ-is-monotone (β i) (β k) l , φ-is-monotone (β j) (β k) m
      fine : φ (∐ 𝓓 β κ) ≡ ∐ 𝓔 (λ x → φ (β x)) h
      fine = φ (∐ 𝓓 β κ) ≡⟨ refl ⟩
             ∐ 𝓔 (λ i → pr₁ (α i) (∐ 𝓓 β κ) ) (ε (∐ 𝓓 β κ)) ≡⟨ ap (λ - → {!∐ 𝓔 (λ i → -) (ε (∐ 𝓓 β κ))!}) {!!} ⟩
             {!∐ 𝓔 (λ i → ?) (ε (∐ 𝓓 β κ))!} ≡⟨ {!!} ⟩
             ∐ 𝓔 (λ x → φ (β x)) h ∎
    γ : is-sup _⊑''_ (φ , φ-is-continuous) α
    γ = {!!}

DCPO'[_,_] : DCPO {𝓤₁} {𝓤₀} → DCPO {𝓤₁} {𝓤₀} → DCPO {𝓥 ⁺} {𝓤₁}
DCPO'[_,_] = DCPO[_,_]

DCPO''[_,_] : DCPO {𝓤₁} {𝓤₁} → DCPO {𝓤₁} {𝓤₁} → DCPO {𝓥 ⁺} {𝓤₁}
DCPO''[_,_] = DCPO[_,_]
-}

\end{code}
