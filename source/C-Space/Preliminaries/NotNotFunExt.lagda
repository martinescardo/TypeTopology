Chuangjie Xu 2013 (ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Space.Preliminaries.NotNotFunExt (dnfe : ¬¬ (DN-funext 𝓤₀ 𝓤₀)) where

fe : {X : Set} {Y : X → Set}
   → {f g : (x : X) → Y x}
   → f ∼ g → ¬¬ (f ＝ g)
fe e u = dnfe (λ z → u (z e))


fe² : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → (y : Y x) → Set} →
      {f g : (x : X) → (y : Y x) → Z x y}
    → (∀ x y → f x y ＝ g x y) → ¬¬ (f ＝ g)
fe² {X} {Y} {Z} {f} {g} exy = goal
 where
  F G : (w : Σ \(x : X) → Y x) → Z (pr₁ w) (pr₂ w)
  F (x , y) = f x y
  G (x , y) = g x y
  Exy : (w : Σ \(x : X) → Y x) → F w ＝ G w
  Exy (x , y) = exy x y
  E : ¬¬ (F ＝ G)
  E = fe Exy
  goal : ¬¬ (f ＝ g) 
  goal = ¬¬-functor (ap (λ φ x y → φ(x , y))) E


fe³ : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → Y x → Set}
      {W : (x : X) → (y : Y x) → Z x y → Set}
      {f g : (x : X) → (y : Y x) → (z : Z x y) → W x y z}
    → (∀ x y z → f x y z ＝ g x y z) → ¬¬ (f ＝ g)
fe³ {X} {Y} {Z} {W} {f} {g} exyz = goal
 where
  F G : (w : Σ \(x : X) → Σ \(y : Y x) → Z x y) → W (pr₁ w) (pr₁(pr₂ w)) (pr₂(pr₂ w))
  F (x , y , z) = f x y z
  G (x , y , z) = g x y z
  Exyz : (w : Σ \(x : X) → Σ \(y : Y x) → Z x y) → F w ＝ G w
  Exyz (x , y , z) = exyz x y z
  E : ¬¬ (F ＝ G)
  E = fe Exyz
  goal : ¬¬ (f ＝ g)
  goal = ¬¬-functor (ap (λ φ x y z → φ(x , y , z))) E


fe⁴ : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → Y x → Set}
      {W : (x : X) → (y : Y x) → Z x y → Set}
      {U : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → Set}
      {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w}
    → (∀ x y z w → f x y z w ＝ g x y z w) → ¬¬ (f ＝ g)
fe⁴ {X} {Y} {Z} {W} {U} {f} {g} ex = goal
 where
  Ω : Set
  Ω = Σ \(x : X) → Σ \(y : Y x) → Σ \(z : Z x y) → W x y z
  F G : (ω : Ω) → U (pr₁ ω) (pr₁(pr₂ ω)) (pr₁(pr₂(pr₂ ω))) (pr₂(pr₂(pr₂ ω)))
  F (x , y , z , w) = f x y z w
  G (x , y , z , w) = g x y z w
  Ex : (ω : Ω) → F ω ＝ G ω
  Ex (x , y , z , w) = ex x y z w
  E : ¬¬ (F ＝ G)
  E = fe Ex
  goal : ¬¬ (f ＝ g)
  goal = ¬¬-functor (ap (λ φ x y z w → φ(x , y , z , w))) E


fe⁵ : {X : Set}
      {Y : X → Set}
      {Z : (x : X) → Y x → Set}
      {W : (x : X) → (y : Y x) → Z x y → Set}
      {U : (x : X) → (y : Y x) → (z : Z x y) → W x y z → Set}
      {V : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → U x y z w → Set}
      {f g : (x : X) → (y : Y x) → (z : Z x y) → (w : W x y z) → (u : U x y z w)
           → V x y z w u}
    → (∀ x y z w u → f x y z w u ＝ g x y z w u) → ¬¬ (f ＝ g)
fe⁵ {X} {Y} {Z} {W} {U} {V} {f} {g} ex = goal
 where
  Ω : Set
  Ω = Σ \(x : X) → Σ \(y : Y x) → Σ \(z : Z x y) → Σ \(w : W x y z) → U x y z w
  F G : (ω : Ω) → V (pr₁ ω) (pr₁(pr₂ ω)) (pr₁(pr₂(pr₂ ω))) (pr₁(pr₂(pr₂(pr₂ ω)))) (pr₂(pr₂(pr₂(pr₂ ω))))
  F (x , y , z , w , u) = f x y z w u
  G (x , y , z , w , u) = g x y z w u
  Ex : (ω : Ω) → F ω ＝ G ω
  Ex (x , y , z , w , u) = ex x y z w u
  E : ¬¬ (F ＝ G)
  E = fe Ex
  goal : ¬¬ (f ＝ g)
  goal = ¬¬-functor (ap (λ φ x y z w u → φ(x , y , z , w , u))) E

\end{code}
