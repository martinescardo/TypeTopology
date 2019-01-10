Martin Escardo 7th November 2018.

(Strong) 'Monad' structure on 𝓛.
(Again the proofs are simplified by the use of SIP.)

Constructions:

\begin{code}

open import SpartanMLTT

module LiftingMonad
        (𝓣 : Universe)
       where

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

open import Lifting 𝓣
open import LiftingIdentityViaSIP 𝓣

𝓛̇ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓛 X → 𝓛 Y
𝓛̇ f (P , φ , i) = P , f ∘ φ , i

_♯ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → 𝓛 Y) → (𝓛 X → 𝓛 Y)
_♯ f (P , φ , i) = (Σ \(p : P) → is-defined (f (φ p))) ,
                    (λ σ → value (f (φ (pr₁ σ))) (pr₂ σ)) ,
                    Σ-is-prop i (λ p → being-defined-is-a-prop (f (φ p)))

μ : {X : 𝓤 ̇} → 𝓛 (𝓛 X) → 𝓛 X
μ = id ♯

\end{code}

Laws:

\begin{code}

𝓛̇-id : {X : 𝓤 ̇} → 𝓛̇ id ≡ id
𝓛̇-id {𝓤} {X} = refl {𝓤 ⊔ (𝓣 ⁺)} {𝓛 X → 𝓛 X}

𝓛̇-∘ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (f : X → Y) (g : Y → Z)
     → 𝓛̇ (g ∘ f) ≡ 𝓛̇ g ∘ 𝓛̇ f
𝓛̇-∘ f g = refl

η-natural : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → η ∘ f ≡ 𝓛̇ f ∘ η
η-natural f = refl

μ-natural : {X : 𝓤 ̇} {Y : 𝓤 ̇} (f : X → Y) → 𝓛̇ f ∘ μ ∼ μ ∘ 𝓛̇ (𝓛̇ f)
μ-natural f _ = refl

𝓛-unit-right : {X : 𝓤 ̇} (l : 𝓛 X) → μ (𝓛̇ η l) ⋍ l
𝓛-unit-right (P , φ , i) = e , refl
 where
  e : P × 𝟙 ≃ P
  e = 𝟙-rneutral

𝓛-unit-left : {X : 𝓤 ̇} (l : 𝓛 X) → μ (η l) ⋍ l
𝓛-unit-left (P , φ) = e , refl
 where
  e : 𝟙 × P ≃ P
  e = 𝟙-lneutral

𝓛-assoc : {X : 𝓤 ̇} (l : 𝓛 (𝓛 (𝓛 X))) → μ (μ l) ⋍ μ (𝓛̇ μ l)
𝓛-assoc (P , φ) = Σ-assoc , refl

\end{code}

Strength:

\begin{code}

𝓛-σ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → X × 𝓛 Y → 𝓛 (X × Y)
𝓛-σ (x , m) = 𝓛̇ (λ y → (x , y)) m

𝓛-τ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → 𝓛 X × Y → 𝓛 (X × Y)
𝓛-τ (l , y) = 𝓛̇ (λ x → (x , y)) l

𝓛-comm : {X : 𝓤 ̇} {Y : 𝓥 ̇} {l : 𝓛 X × 𝓛 Y}
       → μ (𝓛̇ 𝓛-σ (𝓛-τ l)) ⋍· μ (𝓛̇ 𝓛-τ (𝓛-σ l))
𝓛-comm = ×-comm , (λ z → refl)

𝓛-m : {X : 𝓤 ̇} {Y : 𝓥 ̇} → 𝓛 X × 𝓛 Y → 𝓛 (X × Y)
𝓛-m (l , m) = ((λ x → curry 𝓛-σ x m)♯) l

\end{code}

TODO. Write down and prove the strength laws.

Or we can use the Kleisli-triple presentation of the monad, but the
proofs / constructions are essentially the same:

\begin{code}

Kleisli-Law₀ : {X : 𝓤 ̇} (l : 𝓛 X) → (η ♯) l ⋍ l
Kleisli-Law₀ (P , φ) = 𝟙-rneutral , refl

Kleisli-Law₁ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓛 Y) (x : X) → (f ♯) (η x) ⋍ f x
Kleisli-Law₁ f x = 𝟙-lneutral , refl

Kleisli-Law₂ : {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓣 ̇} (f : X → 𝓛 Y) (g : Y → 𝓛 Z) (l : 𝓛 X)
             → (g ♯ ∘ f ♯) l ⋍ ((g ♯ ∘ f)♯) l
Kleisli-Law₂ f g l = Σ-assoc , refl

𝓛̇' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓛 X → 𝓛 Y
𝓛̇' f = (η ∘ f)♯

𝓛̇-agreement : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (l : 𝓛 X)
             → 𝓛̇' f l ⋍· 𝓛̇ f l
𝓛̇-agreement {𝓤} {𝓥} {X} {Y} f (P , i , φ) = 𝟙-rneutral , λ _ → refl

\end{code}
