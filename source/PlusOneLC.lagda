Martin Escardo, 21 March 2018, 1st December 2019.

We prove the known (constructive) fact that

  X + 𝟙 ≃ Y + 𝟙 → X ≃ Y.

The new proof from 1st December 2019 is extracted from the module
UF-Factorial and doesn't use function extensionality. The old proof
from 21 March 2018 is included at the end.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PlusOneLC where

open import SpartanMLTT
open import UF-Equiv
open import Plus-Properties
open import UF-Retracts
open import Swap
open import DiscreteAndSeparated

+𝟙-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇}
               → (X + 𝟙 {𝓦} ≃ Y + 𝟙 {𝓣})
               → X ≃ Y
+𝟙-cancellable {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} (φ , i) = qinveq f' (g' , η' , ε')
 where
  z₀ : X + 𝟙
  z₀ = inr ⋆

  t₀ : Y + 𝟙
  t₀ = inr ⋆

  j : is-isolated z₀
  j = new-point-is-isolated

  k : is-isolated (φ z₀)
  k = equivs-preserve-isolatedness φ i z₀ j

  l : is-isolated t₀
  l = new-point-is-isolated

  s : Y + 𝟙 → Y + 𝟙
  s = swap (φ z₀) t₀ k l

  f : X + 𝟙 → Y + 𝟙
  f = s ∘ φ

  p : f z₀ ≡ t₀
  p = swap-equation₀ (φ z₀) t₀ k l

  g : Y + 𝟙 → X + 𝟙
  g = inverse φ i ∘ s

  h : s ∘ s ∼ id
  h = swap-involutive (φ z₀) t₀ k l

  η : g ∘ f ∼ id
  η z = inverse φ i (s (s (φ z))) ≡⟨ ap (inverse φ i) (h (φ z)) ⟩
        inverse φ i (φ z)         ≡⟨ inverses-are-retractions φ i z ⟩
        z                         ∎

  ε : f ∘ g ∼ id
  ε t = s (φ (inverse φ i (s t))) ≡⟨ ap s (inverses-are-sections φ i (s t)) ⟩
        s (s t)                   ≡⟨ h t ⟩
        t                         ∎

  f' : X → Y
  f' x = pr₁ (inl-preservation f p (sections-are-lc f (g , η)) x)

  a : (x : X) → f (inl x) ≡ inl (f' x)
  a x = pr₂ (inl-preservation f p (sections-are-lc f (g , η)) x)

  q = g t₀     ≡⟨ ap g (p ⁻¹) ⟩
      g (f z₀) ≡⟨ η z₀ ⟩
      inr ⋆    ∎

  g' : Y → X
  g' y = pr₁ (inl-preservation g q (sections-are-lc g (f , ε)) y)

  b : (y : Y) → g (inl y) ≡ inl (g' y)
  b y = pr₂ (inl-preservation g q (sections-are-lc g (f , ε)) y)

  η' : (x : X) → g' (f' x) ≡ x
  η' x = inl-lc (inl (g' (f' x)) ≡⟨ (b (f' x))⁻¹ ⟩
                 g (inl (f' x))  ≡⟨ (ap g (a x))⁻¹ ⟩
                 g (f (inl x))   ≡⟨ η (inl x) ⟩
                 inl x           ∎)

  ε' : (y : Y) → f' (g' y) ≡ y
  ε' y = inl-lc (inl (f' (g' y)) ≡⟨ (a (g' y))⁻¹ ⟩
                 f (inl (g' y))  ≡⟨ (ap f (b y))⁻¹ ⟩
                 f (g (inl y))   ≡⟨ ε (inl y) ⟩
                 inl y           ∎)

\end{code}

The old version from 21 March 2018, which uses function
extensionality:

\begin{code}

_∖_ : (X : 𝓤 ̇ ) (a : X) → 𝓤 ̇
X ∖ a = Σ x ꞉ X , x ≢ a

open import UF-FunExt

module old (fe : FunExt) where

 open import UF-Base
 open import UF-Subsingletons-FunExt

 add-and-remove-point : {X : 𝓤 ̇ } →  X ≃ (X + 𝟙) ∖ (inr ⋆)
 add-and-remove-point {𝓤} {X} = qinveq f (g , ε , η)
  where
   f : X → (X + 𝟙 {𝓤}) ∖ inr ⋆
   f x = (inl x , +disjoint)

   g : (X + 𝟙) ∖ inr ⋆ → X
   g (inl x , u) = x
   g (inr ⋆ , u) = 𝟘-elim (u refl)

   η : f ∘ g ∼ id
   η (inl x , u) = to-Σ-≡' (negations-are-props (fe 𝓤 𝓤₀) _ _)
   η (inr ⋆ , u) = 𝟘-elim (u refl)

   ε : g ∘ f ∼ id
   ε x = refl

 remove-points : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → qinv f → (a : X) → X ∖ a ≃ Y ∖ (f a)
 remove-points {𝓤} {𝓥} {X} {Y} f (g , ε , η) a = qinveq f' (g' , ε' , η')
  where
   f' : X ∖ a → Y ∖ (f a)
   f' (x , u) = (f x , λ (p : f x ≡ f a) → u ((ε x)⁻¹ ∙ ap g p ∙ ε a))

   g' : Y ∖ (f a) → X ∖ a
   g' (y , v) = (g y , λ (p : g y ≡ a) → v ((η y) ⁻¹ ∙ ap f p))

   ε' : g' ∘ f' ∼ id
   ε' (x , _) = to-Σ-≡ (ε x , negations-are-props (fe 𝓤 𝓤₀) _ _)

   η' : f' ∘ g' ∼ id
   η' (y , _) = to-Σ-≡ (η y , negations-are-props (fe 𝓥 𝓤₀) _ _)

 add-one-and-remove-isolated-point : {Y : 𝓥 ̇ } (z : Y + 𝟙) → is-isolated z → ((Y + 𝟙) ∖ z) ≃ Y
 add-one-and-remove-isolated-point {𝓥} {Y} (inl b) i = qinveq f (g , ε , η)
  where
   f : (Y + 𝟙) ∖ (inl b) → Y
   f (inl y , u) = y
   f (inr ⋆ , u) = b

   g' : (y : Y) → decidable (inl b ≡ inl y) → (Y + 𝟙) ∖ (inl b)
   g' y (inl p) = (inr ⋆ , +disjoint')
   g' y (inr u) = (inl y , contrapositive (_⁻¹) u)

   g : Y → (Y + 𝟙) ∖ (inl b)
   g y = g' y (i (inl y))

   ε : g ∘ f ∼ id
   ε (inl y , u) = to-Σ-≡ (p , negations-are-props (fe 𝓥 𝓤₀) _ _)
    where
     φ : (p : inl b ≡ inl y) (q : i (inl y) ≡ inl p) → i (inl y) ≡ inr (≢-sym u)
     φ p q = 𝟘-elim (u (p ⁻¹))
     ψ : (v : inl b ≢ inl y) (q : i (inl y) ≡ inr v) → i (inl y) ≡ inr (≢-sym u)
     ψ v q = q ∙ ap inr (negations-are-props (fe 𝓥 𝓤₀) _ _)
     h : i (inl y) ≡ inr (≢-sym u)
     h = equality-cases (i (inl y)) φ ψ
     p : pr₁ (g' y (i (inl y))) ≡ inl y
     p = ap (pr₁ ∘ (g' y)) h
   ε (inr ⋆ , u) = equality-cases (i (inl b)) φ ψ
    where
     φ : (p : inl b ≡ inl b) → i (inl b) ≡ inl p → g (f (inr ⋆ , u)) ≡ (inr ⋆ , u)
     φ p q = r ∙ to-Σ-≡ (refl , negations-are-props (fe 𝓥 𝓤₀) _ _)
      where
       r : g b ≡ (inr ⋆ , +disjoint')
       r = ap (g' b) q
     ψ : (v : inl b ≢ inl b) → i (inl b) ≡ inr v → g (f (inr ⋆ , u)) ≡ (inr ⋆ , u)
     ψ v q = 𝟘-elim (v refl)

   η : f ∘ g ∼ id
   η y = equality-cases (i (inl y)) φ ψ
    where
     φ : (p : inl b ≡ inl y) → i (inl y) ≡ inl p → f (g' y (i (inl y))) ≡ y
     φ p q = ap (λ - → f (g' y -)) q ∙ inl-lc p
     ψ : (u : inl b ≢ inl y) → i (inl y) ≡ inr u → f (g' y (i (inl y))) ≡ y
     ψ _ = ap ((λ d → f (g' y d)))

 add-one-and-remove-isolated-point {𝓥} {Y} (inr ⋆) _ = ≃-sym add-and-remove-point

 +𝟙-cancellable' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X + 𝟙) ≃ (Y + 𝟙) → X ≃ Y
 +𝟙-cancellable' {𝓤} {𝓥} {X} {Y} (φ , e) =
    X                  ≃⟨ add-and-remove-point ⟩
   (X + 𝟙) ∖ inr ⋆     ≃⟨ remove-points φ (equivs-are-qinvs φ e) (inr ⋆) ⟩
   (Y + 𝟙) ∖ φ (inr ⋆) ≃⟨ add-one-and-remove-isolated-point
                           (φ (inr ⋆))
                           (equivs-preserve-isolatedness φ e (inr ⋆)
                             new-point-is-isolated) ⟩
    Y                  ■

\end{code}

Added 16th April 2021.

\begin{code}

open import UF-Subsingletons-FunExt

remove-and-add-isolated-point : funext 𝓤 𝓤₀
                              → {X : 𝓤 ̇ } (x₀ : X)
                              → is-isolated x₀
                              → X ≃ (X ∖ x₀ + 𝟙 {𝓥})
remove-and-add-isolated-point fe {X} x₀ ι = qinveq f (g , ε , η)
 where
  ϕ : (x : X) → decidable (x₀ ≡ x) → X ∖ x₀ + 𝟙
  ϕ x (inl p) = inr ⋆
  ϕ x (inr ν) = inl (x , (λ (p : x ≡ x₀) → ν (p ⁻¹)))

  f : X → X ∖ x₀ + 𝟙
  f x = ϕ x (ι x)

  g : X ∖ x₀ + 𝟙 → X
  g (inl (x , _)) = x
  g (inr ⋆) = x₀

  η' : (y : X ∖ x₀ + 𝟙) (d : decidable (x₀ ≡ g y)) → ϕ (g y) d ≡ y
  η' (inl (x , ν)) (inl q) = 𝟘-elim (ν (q ⁻¹))
  η' (inl (x , ν)) (inr _) = ap (λ - → inl (x , -)) (negations-are-props fe _ _)
  η' (inr ⋆) (inl p)       = refl
  η' (inr ⋆) (inr ν)       = 𝟘-elim (ν refl)

  η : f ∘ g ∼ id
  η y = η' y (ι (g y))

  ε' : (x : X) (d : decidable (x₀ ≡ x)) → g (ϕ x d) ≡ x
  ε' x (inl p) = p
  ε' x (inr ν) = refl

  ε : g ∘ f ∼ id
  ε x = ε' x (ι x)

\end{code}
