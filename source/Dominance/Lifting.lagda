Martin Escardo, January 2018, May 2020
Jonathan Sterling, June 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Dominance.Definition
open import MLTT.Spartan
open import UF.Base
open import UF.SIP
open import UF.Univalence
open import UF.FunExt
open import UF.Equiv-FunExt
open import UF.Equiv hiding (_≅_; ≅-refl)
open import UF.EquivalenceExamples
open import UF.UA-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import W.Type

import UF.PairFun as PairFun

module
 Dominance.Lifting
  {𝓣 𝓚 : Universe}
  (𝓣-ua : is-univalent 𝓣)
  (d : 𝓣 ̇ → 𝓚 ̇)
  (isd : is-dominance d)
 where

 D : Dominance
 D = (d , isd)

 module _ {𝓥} where
  L : (X : 𝓥 ̇) → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ̇
  L X = Σ P ꞉ 𝓣 ̇ , (P → X) × d P

  is-defined : {X : 𝓥 ̇} → L X → 𝓣 ̇
  is-defined (P , (ϕ , dP)) = P

  _↓ = is-defined

  ↓-is-dominant : {X : 𝓥 ̇} → (x̃ : L X) → is-dominant D (x̃ ↓)
  ↓-is-dominant (P , (ϕ , dP)) = dP

  value : {X : 𝓥 ̇} → (x̃ : L X) → x̃ ↓ → X
  value (P , (ϕ , dP)) = ϕ


 module _ {𝓥 : _} {X : 𝓥 ̇} where
  open sip

  fam-str : (P : 𝓣 ̇) → 𝓣 ⊔ 𝓥 ̇
  fam-str P = P → X

  fam-sns-data : SNS fam-str (𝓣 ⊔ 𝓥)
  fam-sns-data = ι , ρ , θ
   where
    ι : (u v : Σ fam-str) → ⟨ u ⟩ ≃ ⟨ v ⟩ → 𝓣 ⊔ 𝓥 ̇
    ι (P , u) (Q , v) (f , _) = u ＝ v ∘ f

    ρ : (u : Σ fam-str) → ι u u (≃-refl ⟨ u ⟩)
    ρ _ = refl

    h : {P : 𝓣 ̇} {u v : fam-str P} → canonical-map ι ρ u v ∼ -id (u ＝ v)
    h refl = refl

    θ : {P : 𝓣 ̇} (u v : fam-str P) → is-equiv (canonical-map ι ρ u v)
    θ u v = equiv-closed-under-∼ _ _ (id-is-equiv (u ＝ v)) h

  fam-≅ : (u v : Σ fam-str) → 𝓣 ⊔ 𝓥 ̇
  fam-≅ (P , u) (Q , v) =
   Σ f ꞉ (P → Q) , is-equiv f × (u ＝ v ∘ f)

  characterization-of-fam-＝ : (u v : Σ fam-str) → (u ＝ v) ≃ fam-≅ u v
  characterization-of-fam-＝ = characterization-of-＝ 𝓣-ua fam-sns-data

  _≅_ : L X → L X → 𝓣 ⊔ 𝓥 ̇
  (P , u , dP) ≅ (Q , v , dQ) =
   Σ f ꞉ P ↔ Q , u ∼ v ∘ pr₁ f

  ≅-refl : (u : L X) → u ≅ u
  ≅-refl u = (id , id) , λ _ → refl

  module _ (𝓣𝓥-fe : funext 𝓣 𝓥) where
   ＝-to-≅ : (u v : L X) → (u ＝ v) ≃ (u ≅ v)
   ＝-to-≅ u v =
    (u ＝ v)
     ≃⟨ step1 u v ⟩
    fam-≅ (u ↓ , value u) (v ↓ , value v)
     ≃⟨ step2 ⟩
    (Σ f ꞉ (u ↓ → v ↓) , (v ↓ → u ↓) × value u ∼ value v ∘ f)
     ≃⟨ ≃-sym Σ-assoc ⟩
    u ≅ v ■

    where
     open sip-with-axioms

     u↓-is-prop = dominant-types-are-props D (u ↓) (↓-is-dominant u)
     v↓-is-prop = dominant-types-are-props D (v ↓) (↓-is-dominant v)
     𝓣-fe = univalence-gives-funext 𝓣-ua

     step1 =
      characterization-of-＝-with-axioms 𝓣-ua
       fam-sns-data
       (λ P u → d P)
       (λ P _ → being-dominant-is-prop D P)

     step2 =
      PairFun.pair-fun-equiv
       (≃-refl (u ↓ → v ↓))
       (λ f →
        PairFun.pair-fun-equiv
         (logically-equivalent-props-are-equivalent
          (being-equiv-is-prop' 𝓣-fe 𝓣-fe 𝓣-fe 𝓣-fe f)
          (Π-is-prop 𝓣-fe (λ _ → u↓-is-prop))
          (inverse f)
          (logically-equivalent-props-give-is-equiv
           u↓-is-prop
           v↓-is-prop
           f))
         (λ _ → ≃-funext 𝓣𝓥-fe (value u) (value v ∘ f)))

   ＝-to-≅-refl : (u : L X) → eqtofun (＝-to-≅ u u) refl ＝ ≅-refl u
   ＝-to-≅-refl _ = refl

   L-ext : {u v : L X} → u ≅ v → u ＝ v
   L-ext = back-eqtofun (＝-to-≅ _ _)

 η : {𝓥 : _} {X : 𝓥 ̇} → X → L X
 η x = 𝟙 , (λ _ → x) , 𝟙-is-dominant D

 _⇀_ : {𝓥 𝓦 : _} → 𝓥 ̇ → 𝓦 ̇ → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ⊔ 𝓦 ̇
 X ⇀ Y = X → L Y

 module _ {𝓥 𝓦 : _} {X : 𝓥 ̇} {Y : 𝓦 ̇} where
  extension : (X ⇀ Y) → (L X → L Y)
  extension f (P , (φ , dP)) = (Q , (γ , dQ))
   where
    Q : 𝓣 ̇
    Q = Σ p ꞉ P , f (φ p) ↓

    dQ : is-dominant D Q
    dQ = dominant-closed-under-Σ D P (_↓ ∘ f ∘ φ) dP (↓-is-dominant ∘ f ∘ φ)

    γ : Q → Y
    γ (p , def) = value (f (φ p)) def

  _♯ : (X ⇀ Y) → (L X → L Y)
  f ♯ = extension f

 _<<<_
  : {𝓥 𝓦 𝓣 : _} {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓣 ̇}
  → (Y ⇀ Z) → (X ⇀ Y) → (X ⇀ Z)
 g <<< f = g ♯ ∘ f

 μ : {𝓥 : _} {X : 𝓥 ̇} → L (L X) → L X
 μ = extension id

 module _ {𝓥} {X : 𝓥 ̇} (𝓣𝓥-fe : funext 𝓣 𝓥) where
  kleisli-law₀ : extension (η {𝓥} {X}) ∼ id
  kleisli-law₀ u =
   L-ext 𝓣𝓥-fe (α , λ _ → refl)
   where
    α : u ↓ × 𝟙 ↔ u ↓
    α = pr₁ , (_, ⋆)

 module _ {𝓥 𝓦} {X : 𝓥 ̇} {Y : 𝓦 ̇} (𝓣𝓦-fe : funext 𝓣 𝓦) where
  kleisli-law₁ : (f : X ⇀ Y) → extension f ∘ η ∼ f
  kleisli-law₁ f u =
   L-ext 𝓣𝓦-fe (α , λ _ → refl)
   where
    α : 𝟙 × f u ↓ ↔ f u ↓
    α = pr₂ , (⋆ ,_)

 module _ {𝓥 𝓦 𝓧} {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓧 ̇} (𝓣𝓧-fe : funext 𝓣 𝓧) where
  kleisli-law₂ : (f : X ⇀ Y) (g : Y ⇀ Z) → (g ♯ ∘ f)♯ ∼ g ♯ ∘ f ♯
  kleisli-law₂ f g x =
   L-ext 𝓣𝓧-fe (α , λ _ → refl)
   where
    α : (((g ♯) ∘ f) ♯) x ↓ ↔ ((g ♯) ∘ (f ♯)) x ↓
    pr₁ α (p , q , r) = (p , q) , r
    pr₂ α ((p , q) , r) = p , q , r


\end{code}

TODO: state and prove the naturality of all the monad components, define both
algebras for the endofunctor and for the monad, recall the results of Joyal and
Moerdijk on monads and algebras with successor, etc.

We can define carrier of the initial lift algebra using a W-type.

\begin{code}

 module Initial-Lift-Algebra where
  ω : 𝓣 ⁺ ⊔ 𝓚 ̇
  ω = W (dominant-prop D) pr₁

\end{code}
