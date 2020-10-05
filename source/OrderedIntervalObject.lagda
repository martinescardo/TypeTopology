\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-PropTrunc

module OrderedIntervalObject (fe : FunExt) (pt : propositional-truncations-exist) where

open import Escardo-Simpson-LICS2001 fe
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import DiscreteAndSeparated hiding (_♯_)
open import TotallySeparated

\end{code}


\begin{code}

record is-ordered (io : Interval-object 𝓤) : 𝓤₁ ⊔ 𝓤 ̇ where

\end{code}


\begin{code}

  open Interval-object io
  
  ⊕-commutative : commutative _⊕_
  ⊕-commutative = pr₁ (pr₂ (pr₂ mpaa))

  M : (ℕ → 𝕀) → 𝕀
  M = pr₁ (ia)

\end{code}


\begin{code}
  
  field
    _<_ : 𝕀 → 𝕀 → 𝓤₀ ̇
    <-prop-valued : {x y : 𝕀} → is-prop (x < y)
  
  _≮_ : 𝕀 → 𝕀 → 𝓤₀ ̇
  x ≮ y = ¬ (x < y)
  
  field
    u<v : u < v
    <-⊕ᵣ    : {x y z : 𝕀} → y < z → (x ⊕ y) < (x ⊕ z)
    <-⊕ᵣ'   : {x y z : 𝕀} → (x ⊕ y) < (x ⊕ z) → y < z
    <-⊕ₘ    : {x : 𝕀} {a : ℕ → 𝕀} → ((n : ℕ) → x < a n) → x < M a
    <-⊕ₘ'   : {x : 𝕀} {a : ℕ → 𝕀} → ((n : ℕ) → a n < x) → M a < x

  field
    <-irreflexive : {x     : 𝕀} → x ≮ x
    <-asymmetric  : {x y   : 𝕀} → x < y → y ≮ x
    <-transitive  : {x y z : 𝕀} → x < y → y < z → x < z
    <-connected   : {x y   : 𝕀} → x ≮ y → y ≮ x → x ≡ y
    <-decidable   : {x y   : 𝕀} → (x < y) + (x ≮ y)
    <-comparison  : {x y z : 𝕀} → x < z → (x < y) + (y < z)


  <-⊕ₗ : {x y z : 𝕀} → x < z → (x ⊕ y) < (z ⊕ y)
  <-⊕ₗ {x} {y} {z} x<z = transport (_< (z ⊕ y)) ⊕-commutative
                          (transport ((y ⊕ x) <_) ⊕-commutative (<-⊕ᵣ x<z))
                          
  <-⊕₂ : {x y z w : 𝕀} → x < z → y < w → (x ⊕ y) < (z ⊕ w)
  <-⊕₂ {x} {y} {z} {w} x<z y<w = <-transitive (<-⊕ᵣ y<w) (<-⊕ₗ x<z)

  <-⊕ₗ' : {x y z : 𝕀} → (x ⊕ y) < (z ⊕ y) → x < z
  <-⊕ₗ' {x} {y} {z} x⊕y<z⊕y = <-⊕ᵣ' (transport (_< (y ⊕ z)) ⊕-commutative
                                    (transport ((x ⊕ y) <_) ⊕-commutative x⊕y<z⊕y))

\end{code}


\begin{code}

  _≤_  : 𝕀 → 𝕀 → 𝓤₀ ̇  
  x ≤  y = y ≮ x

  ≤-trichotomous : {x y : 𝕀} → x < y + y ≤ x
  ≤-trichotomous = <-decidable

  ≤-reflexive : {x : 𝕀} → x ≤ x
  ≤-reflexive = <-irreflexive

  _≤'_ : 𝕀 → 𝕀 → 𝓤 ̇
  x ≤' y = {z : 𝕀} → z < x → z < y

  _≤''_ : 𝕀 → 𝕀 → 𝓤 ̇
  x ≤'' y = {z : 𝕀} → y < z → x < z

  ≤→≤' : {x y : 𝕀} → x ≤ y → x ≤' y
  ≤→≤' x≤y z<x = Cases (<-comparison z<x) id (λ y<x → 𝟘-elim (x≤y y<x))

  ≤'→≤ : {x y : 𝕀} → x ≤' y → x ≤ y
  ≤'→≤ x≤'y y<x = <-irreflexive (x≤'y y<x)

  ≤→≤'' : {x y : 𝕀} → x ≤ y → x ≤'' y
  ≤→≤'' x≤y y<z = Cases (<-comparison y<z) (λ y<x → 𝟘-elim (x≤y y<x)) id

  ≤''→≤ : {x y : 𝕀} → x ≤'' y → x ≤ y
  ≤''→≤ x≤''y y<x = <-irreflexive (x≤''y y<x)

  ≤'→≤'' : {x y : 𝕀} → x ≤' y → x ≤'' y
  ≤'→≤'' = ≤→≤'' ∘ ≤'→≤

  ≤''→≤' : {x y : 𝕀} → x ≤'' y → x ≤' y
  ≤''→≤' = ≤→≤' ∘ ≤''→≤

  ≤-⊕ᵣ : {x y z : 𝕀} → y ≤ z → (x ⊕ y) ≤ (x ⊕ z)
  ≤-⊕ᵣ y≤z x⊕z<x⊕y = y≤z (<-⊕ᵣ' x⊕z<x⊕y)

  ≤-⊕ₗ : {x y z : 𝕀} → x ≤ z → (x ⊕ y) ≤ (z ⊕ y)
  ≤-⊕ₗ y≤z x⊕z<x⊕y = y≤z (<-⊕ₗ' x⊕z<x⊕y)

  ≤-trans : {x y z : 𝕀} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans x≤y y≤z z<x = x≤y (Cases (<-comparison z<x) (λ z<y → 𝟘-elim (y≤z z<y)) id)

  <≤-trans : {x y z : 𝕀} → x < y → y ≤ z → x < z
  <≤-trans x<y y≤z = Cases (<-comparison x<y) id (λ z<y → 𝟘-elim (y≤z z<y))

  ≤<-trans : {x y z : 𝕀} → x ≤ y → y < z → x < z
  ≤<-trans x≤y y<z = Cases (<-comparison y<z) (λ y<x → 𝟘-elim (x≤y y<x)) id

  ≤-⊕₂ : {x y z w : 𝕀} → x ≤ z → y ≤ w → (x ⊕ y) ≤ (z ⊕ w)
  ≤-⊕₂ {x} {y} {z} {w} x≤z y≤w = ≤-trans (≤-⊕ᵣ y≤w) (≤-⊕ₗ x≤z)

  ≤-⊕ₘ : {x : 𝕀} {a : ℕ → 𝕀} → ((n : ℕ) → x ≤ a n) → x ≤ M a
  ≤-⊕ₘ {x} {a} f = ≤'→≤ (λ z<x → <-⊕ₘ (λ n → <≤-trans z<x (f n)))

  ≤-⊕ₘ' : {x : 𝕀} {a : ℕ → 𝕀} → ((n : ℕ) → a n ≤ x) → M a ≤ x
  ≤-⊕ₘ' {x} {a} f = ≤''→≤ (λ x<z → <-⊕ₘ' (λ n → ≤<-trans (f n) x<z))

  ≤-prop-valued : {x y : 𝕀} → is-prop (x ≤ y)
  ≤-prop-valued = ¬-is-prop (fe 𝓤₀ 𝓤₀)


\end{code}


\begin{code}

  open Apartness pt
  open propositional-truncations-exist pt

  _♯_ : 𝕀 → 𝕀 → 𝓤₀ ̇
  x ♯ y = (x < y) + (y < x)

  ♯-prop-valued : is-prop-valued _♯_
  ♯-prop-valued x y = +-is-prop <-prop-valued <-prop-valued <-asymmetric
  
  ♯-irreflexive : is-irreflexive _♯_
  ♯-irreflexive x x♯x = <-irreflexive (Cases x♯x id id)
  
  ♯-symmetric : is-symmetric _♯_
  ♯-symmetric x y x♯y = Cases x♯y inr inl

  ♯-cotransitive' : {x y z : 𝕀} → x ♯ y → (x ♯ z) + (y ♯ z)
  ♯-cotransitive' x♯y
    = Cases x♯y (λ x<y → Cases (<-comparison x<y)
                  (λ x<z → inl (inl x<z))
                  (λ z<y → inr (inr z<y)))
                (λ y<x → Cases (<-comparison y<x)
                  (λ y<z → inr (inl y<z))
                  (λ z<y → inl (inr z<y)))

  ♯-cotransitive : is-cotransitive _♯_
  ♯-cotransitive x y z x♯y = ∣ ♯-cotransitive' x♯y ∣

  ♯-apartness : is-apartness _♯_
  ♯-apartness = ♯-prop-valued , ♯-irreflexive , ♯-symmetric , ♯-cotransitive

  ♯-tight : is-tight _♯_
  ♯-tight x y ¬x♯y = <-connected (λ x<y → 𝟘-elim (¬x♯y (inl x<y)))
                                 (λ y<x → 𝟘-elim (¬x♯y (inr y<x)))

  𝕀-is-separated : is-separated 𝕀
  𝕀-is-separated = tight-is-separated _♯_ ♯-apartness ♯-tight

\end{code}


\begin{code}

  <-irreflexive' : {x y : 𝕀} → x < y → x ≢ y
  <-irreflexive' {x} {.x} x<x refl = <-irreflexive x<x
