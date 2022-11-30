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

 Fam-structure : {𝓥 : _} (X : 𝓥 ̇) (P : 𝓣 ̇) → 𝓣 ⊔ 𝓥 ̇
 Fam-structure X P = P → X

 L : {𝓥 : _} (X : 𝓥 ̇) → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ̇
 L X = Σ P ꞉ 𝓣 ̇ , (P → X) × d P

 _⇀_ : ∀ {𝓥 𝓦} → 𝓥 ̇ → 𝓦 ̇ → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ⊔ 𝓦 ̇
 X ⇀ Y = X → L Y

 is-defined : ∀ {𝓥} {X : 𝓥 ̇} → L X → 𝓣 ̇
 is-defined (P , (ϕ , isdp)) = P

 is-dominant-is-defined : ∀ {𝓥} {X : 𝓥 ̇ } → (x̃ : L X) → is-dominant D (is-defined x̃)
 is-dominant-is-defined (P , (ϕ , isdp)) = isdp

 value : ∀ {𝓥} {X : 𝓥 ̇} → (x̃ : L X) → is-defined x̃ → X
 value (P , (ϕ , isdp)) = ϕ

 module _ {𝓥 : _} {X : 𝓥 ̇} where
  open sip

  Fam-sns-data : SNS (Fam-structure X) (𝓣 ⊔ 𝓥)
  Fam-sns-data = ι , ρ , θ
   where
    ι : (u v : Σ (Fam-structure X)) → ⟨ u ⟩ ≃ ⟨ v ⟩ → 𝓣 ⊔ 𝓥 ̇
    ι (P , u) (Q , v) (f , _) =
     u ＝ v ∘ f

    ρ : (u : Σ (Fam-structure X)) → ι u u (≃-refl ⟨ u ⟩)
    ρ (P , u) = refl

    h : {P : 𝓣 ̇} {u v : Fam-structure X P} → canonical-map ι ρ u v ∼ -id (u ＝ v)
    h refl = refl

    θ : {P : 𝓣 ̇} (u v : Fam-structure X P) → is-equiv (canonical-map ι ρ u v)
    θ u v = equiv-closed-under-∼ _ _ (id-is-equiv (u ＝ v)) h

  Fam-≅ : (u v : Σ (Fam-structure X)) → 𝓣 ⊔ 𝓥 ̇
  Fam-≅ (P , u) (Q , v) =
   Σ f ꞉ (P → Q) , is-equiv f × (u ＝ v ∘ f)

  characterization-of-Fam-＝ : (u v : Σ (Fam-structure X)) → (u ＝ v) ≃ Fam-≅ u v
  characterization-of-Fam-＝ = characterization-of-＝ 𝓣-ua Fam-sns-data

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
   Fam-≅ (P , value u) (Q , value v) ≃⟨ step2 ⟩
   (Σ f ꞉ (P → Q) , (Q → P) × value u ∼ value v ∘ f) ≃⟨ ≃-sym Σ-assoc ⟩
   L-≅ u v ■
   where
    open sip-with-axioms
    P = is-defined u
    Q = is-defined v

    P-is-prop = dominant-types-are-props (d , isd) P (is-dominant-is-defined u)
    Q-is-prop = dominant-types-are-props (d , isd) Q (is-dominant-is-defined v)

    𝓣-fe = univalence-gives-funext 𝓣-ua

    step1 =
     characterization-of-＝-with-axioms 𝓣-ua
      Fam-sns-data
      (λ P u → d P)
      (λ P _ → being-dominant-is-prop (d , isd) P)

    step2 =
     PairFun.pair-fun-equiv
      (≃-refl (P → Q))
      (λ f →
       PairFun.pair-fun-equiv
        (logically-equivalent-props-are-equivalent
         (being-equiv-is-prop' 𝓣-fe 𝓣-fe 𝓣-fe 𝓣-fe f)
         (Π-is-prop 𝓣-fe (λ _ → P-is-prop))
         (λ f-equiv q → inverse f f-equiv q)
         (λ g →
          logically-equivalent-props-give-is-equiv
           P-is-prop
           Q-is-prop
           f
           g))
        (λ f-equiv → ≃-funext 𝓣𝓥-fe (value u) (value v ∘ f)))

  L-ext : (𝓣𝓥-fe : funext 𝓣 𝓥) {u v : L X} → L-≅ u v → u ＝ v
  L-ext 𝓣𝓥-fe = back-eqtofun (＝-to-L-≅ 𝓣𝓥-fe _ _)


 η : ∀ {𝓥} {X : 𝓥 ̇} → X → L X
 η x = 𝟙 , (λ _ → x) , 𝟙-is-dominant D

 extension : ∀ {𝓥 𝓦} {X : 𝓥 ̇} {Y : 𝓦 ̇} → (X ⇀ Y) → (L X → L Y)
 extension {𝓥} {𝓦} {X} {Y} f (P , (φ , isdp)) = (Q , (γ , isdq))
  where
   Q : 𝓣 ̇
   Q = Σ p ꞉ P , is-defined (f (φ p))

   isdq : is-dominant D Q
   isdq =
    dominant-closed-under-Σ D
     P
     (λ p → is-defined (f (φ p)))
     isdp
     (λ p → is-dominant-is-defined (f (φ p)))

   γ : Q → Y
   γ (p , def) = value (f (φ p)) def

 _♯ : ∀ {𝓥 𝓦} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X ⇀ Y) → (L X → L Y)
 f ♯ = extension f

 _◌_
  : ∀ {𝓥 𝓦 𝓣} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } {Z : 𝓣 ̇ }
  → (Y ⇀ Z) → (X ⇀ Y) → (X ⇀ Z)
 g ◌ f = g ♯ ∘ f

 LL : {𝓥 : _} (X : 𝓥 ̇) → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ̇
 LL X = L (L X)

 μ : ∀ {𝓥} {X : 𝓥 ̇ } → LL X → L X
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
