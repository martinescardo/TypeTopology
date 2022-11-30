Martin Escardo, January 2018, May 2020

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import Dominance.Definition
open import MLTT.Spartan
open import UF.Base
open import UF.SIP
open import UF.Univalence
open import UF.FunExt
open import UF.Equiv-FunExt
open import UF.Equiv hiding (_≅_)
open import UF.UA-FunExt
open import UF.Subsingletons-FunExt
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

  is-dominant-is-defined : {X : 𝓥 ̇} → (x̃ : L X) → is-dominant D (is-defined x̃)
  is-dominant-is-defined (P , (ϕ , dP)) = dP

  value : {X : 𝓥 ̇} → (x̃ : L X) → is-defined x̃ → X
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

  L-≅ : L X → L X → 𝓣 ⊔ 𝓥 ̇
  L-≅ (P , u , dP) (Q , v , dQ) =
    Σ f ꞉ P ⇔ Q , u ∼ v ∘ pr₁ f

  -- TODO: move or find in library
  Σ-assoc
   : {𝓥 𝓦 𝓧 : _} {A : 𝓥 ̇} {B : A → 𝓦 ̇} {C : (x : A) → B x → 𝓧 ̇}
   → (Σ xy ꞉ Σ B , C (pr₁ xy) (pr₂ xy)) ≃ (Σ x ꞉ A , Σ y ꞉ B x , C x y)
  pr₁ Σ-assoc ((x , y) , z) = x , (y , z)
  pr₁ (pr₁ (pr₂ Σ-assoc)) (x , y , z) = (x , y) , z
  pr₂ (pr₁ (pr₂ Σ-assoc)) _ = refl
  pr₁ (pr₂ (pr₂ Σ-assoc)) (x , y , z) = (x , y) , z
  pr₂ (pr₂ (pr₂ Σ-assoc)) _ = refl


  ＝-to-L-≅ : (𝓣𝓥-fe : funext 𝓣 𝓥) → (u v : L X) → (u ＝ v) ≃ L-≅ u v
  ＝-to-L-≅ 𝓣𝓥-fe u v =
   (u ＝ v) ≃⟨ step1 u v ⟩
   fam-≅ (P , value u) (Q , value v) ≃⟨ step2 ⟩
   (Σ f ꞉ (P → Q) , (Q → P) × value u ∼ value v ∘ f) ≃⟨ ≃-sym Σ-assoc ⟩
   L-≅ u v ■
   where
    open sip-with-axioms
    P = is-defined u
    Q = is-defined v

    P-is-prop = dominant-types-are-props D P (is-dominant-is-defined u)
    Q-is-prop = dominant-types-are-props D Q (is-dominant-is-defined v)

    𝓣-fe = univalence-gives-funext 𝓣-ua

    step1 =
     characterization-of-＝-with-axioms 𝓣-ua
      fam-sns-data
      (λ P u → d P)
      (λ P _ → being-dominant-is-prop D P)

    step2 =
     PairFun.pair-fun-equiv
      (≃-refl (P → Q))
      (λ f →
       PairFun.pair-fun-equiv
        (logically-equivalent-props-are-equivalent
         (being-equiv-is-prop' 𝓣-fe 𝓣-fe 𝓣-fe 𝓣-fe f)
         (Π-is-prop 𝓣-fe (λ _ → P-is-prop))
         (inverse f)
         (logically-equivalent-props-give-is-equiv
          P-is-prop
          Q-is-prop
          f))
        (λ _ → ≃-funext 𝓣𝓥-fe (value u) (value v ∘ f)))

  L-ext : (𝓣𝓥-fe : funext 𝓣 𝓥) {u v : L X} → L-≅ u v → u ＝ v
  L-ext 𝓣𝓥-fe = back-eqtofun (＝-to-L-≅ 𝓣𝓥-fe _ _)


 η : {𝓥 : _} {X : 𝓥 ̇} → X → L X
 η x = 𝟙 , (λ _ → x) , 𝟙-is-dominant D

 _⇀_ : {𝓥 𝓦 : _} → 𝓥 ̇ → 𝓦 ̇ → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ⊔ 𝓦 ̇
 X ⇀ Y = X → L Y

 module _ {𝓥 𝓦 : _} {X : 𝓥 ̇} {Y : 𝓦 ̇} where
  extension : (X ⇀ Y) → (L X → L Y)
  extension f (P , (φ , dP)) = (Q , (γ , dQ))
   where
    Q : 𝓣 ̇
    Q = Σ p ꞉ P , is-defined (f (φ p))

    dQ : is-dominant D Q
    dQ =
     dominant-closed-under-Σ D
      P
      (is-defined ∘ f ∘ φ)
      dP
      (is-dominant-is-defined ∘ f ∘ φ)

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

 module _ {𝓥} (𝓣𝓥-fe : funext 𝓣 𝓥) where
  kleisli-law₀ : {X : 𝓥 ̇} → extension (η {𝓥} {X}) ∼ id
  kleisli-law₀ {X} u =
   L-ext 𝓣𝓥-fe (α , λ _ → refl)
   where
    α : is-defined u × 𝟙 ⇔ is-defined u
    α = pr₁ , (λ x → x , ⋆)

 module _ {𝓥 𝓦} (𝓣𝓦-fe : funext 𝓣 𝓦) where
  kleisli-law₁ : {X : 𝓥 ̇} {Y : 𝓦 ̇} (f : X ⇀ Y) → extension f ∘ η ∼ f
  kleisli-law₁ {X} {Y} f u =
   L-ext 𝓣𝓦-fe (α , λ _ → refl)
   where
    α : 𝟙 × is-defined (f u) ⇔ is-defined (f u)
    α = pr₂ , (λ p → ⋆ , p)

 module _ {𝓥 𝓦 𝓧} (𝓣𝓧-fe : funext 𝓣 𝓧) where
  kleisli-law₂
   : {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓧 ̇} (f : X ⇀ Y) (g : Y ⇀ Z)
   → (g ♯ ∘ f)♯ ∼ g ♯ ∘ f ♯
  kleisli-law₂ f g x =
   L-ext 𝓣𝓧-fe (α , λ _ → refl)
   where
    α : is-defined ((((g ♯) ∘ f) ♯) x) ⇔ is-defined (((g ♯) ∘ (f ♯)) x)
    pr₁ α (p , q , r) = (p , q) , r
    pr₂ α ((p , q) , r) = p , q , r

\end{code}
