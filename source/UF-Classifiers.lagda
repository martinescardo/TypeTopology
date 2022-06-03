Martin Escardo 8th May 2020.

An old version of this file is at UF-Classifiers-Old.

This version is ported from the Midlands Graduate School 2019 lecture notes

 https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
 https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes


   * Map classifier
   * Embedding classifier
   * Retraction classifier
   * Surjection classifier

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-Classifiers where

open import SpartanMLTT
open import UF-Base
open import UF-Embeddings
open import UF-Equiv
open import UF-Univalence
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Powerset hiding (𝕋)
open import UF-EquivalenceExamples
open import UF-Retracts

_/_ : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 / Y = Σ X ꞉ 𝓤 ̇ , (X → Y)

χ : (Y : 𝓤 ̇ ) → 𝓤 / Y  → (Y → 𝓤 ̇ )
χ Y (X , f) = fiber f

is-map-classifier : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-map-classifier 𝓤 = (Y : 𝓤 ̇ ) → is-equiv (χ Y)

𝕋 : (Y : 𝓤 ̇ ) → (Y → 𝓤 ̇ ) → 𝓤 / Y
𝕋 Y A = Σ A , pr₁

χη : is-univalent 𝓤
   → (Y : 𝓤 ̇ ) (σ : 𝓤 / Y) → 𝕋 Y (χ Y σ) ≡ σ
χη ua Y (X , f) = r
 where
  e : Σ (fiber f) ≃ X
  e = total-fiber-is-domain f

  p : Σ (fiber f) ≡ X
  p = eqtoid ua (Σ (fiber f)) X e

  observation : ⌜ e ⌝⁻¹ ≡ (λ x → f x , x , refl)
  observation = refl

  q = transport (λ - → - → Y) p pr₁ ≡⟨ transport-is-pre-comp' ua e pr₁ ⟩
      pr₁ ∘ ⌜ e ⌝⁻¹                 ≡⟨ refl ⟩
      f                             ∎

  r : (Σ (fiber f) , pr₁) ≡ (X , f)
  r = to-Σ-≡ (p , q)

χε : is-univalent 𝓤
   → funext 𝓤 (𝓤 ⁺)
   → (Y : 𝓤 ̇ ) (A : Y → 𝓤 ̇ ) → χ Y (𝕋 Y A) ≡ A
χε ua fe Y A = dfunext fe γ
 where
  f : ∀ y → fiber pr₁ y → A y
  f y ((y , a) , refl) = a
  g : ∀ y → A y → fiber pr₁ y
  g y a = (y , a) , refl
  η : ∀ y σ → g y (f y σ) ≡ σ
  η y ((y , a) , refl) = refl
  ε : ∀ y a → f y (g y a) ≡ a
  ε y a = refl
  γ : ∀ y → fiber pr₁ y ≡ A y
  γ y = eqtoid ua _ _ (qinveq (f y) (g y , η y , ε y))

universes-are-map-classifiers : is-univalent 𝓤
                              → funext 𝓤 (𝓤 ⁺)
                              → is-map-classifier 𝓤
universes-are-map-classifiers ua fe Y = qinvs-are-equivs (χ Y)
                                         (𝕋 Y , χη ua Y , χε ua fe Y)

map-classification : is-univalent 𝓤
                   → funext 𝓤 (𝓤 ⁺)
                   → (Y : 𝓤 ̇ ) → 𝓤 / Y ≃ (Y → 𝓤 ̇ )
map-classification ua fe Y = χ Y , universes-are-map-classifiers ua fe Y

_/[_]_ : (𝓤 : Universe) → (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
𝓤 /[ P ] Y = Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , ((y : Y) → P (fiber f y))

χ-special : (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ ) → 𝓤 /[ P ] Y  → (Y → Σ P)
χ-special P Y (X , f , φ) y = fiber f y , φ y

is-special-map-classifier : (𝓤 ̇ → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-special-map-classifier {𝓤} P = (Y : 𝓤 ̇ ) → is-equiv (χ-special P Y)

mc-gives-sc : is-map-classifier 𝓤
            → (P : 𝓤 ̇ → 𝓥 ̇ ) → is-special-map-classifier P
mc-gives-sc {𝓤} s P Y = γ
 where
  e = (𝓤 /[ P ] Y)                               ≃⟨ a ⟩
      (Σ σ ꞉ 𝓤 / Y , ((y : Y) → P ((χ Y) σ y)))  ≃⟨ b ⟩
      (Σ A ꞉ (Y → 𝓤 ̇ ), ((y : Y) → P (A y)))     ≃⟨ c ⟩
      (Y → Σ P)                                  ■
   where
    a = ≃-sym Σ-assoc
    b = Σ-change-of-variable (λ A → Π (P ∘ A)) (χ Y) (s Y)
    c = ≃-sym ΠΣ-distr-≃

  observation : χ-special P Y ≡ ⌜ e ⌝
  observation = refl

  γ : is-equiv (χ-special P Y)
  γ = ⌜⌝-is-equiv e

χ-special-is-equiv : is-univalent 𝓤
                   → funext 𝓤 (𝓤 ⁺)
                   → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                   → is-equiv (χ-special P Y)
χ-special-is-equiv {𝓤} ua fe P Y = mc-gives-sc (universes-are-map-classifiers ua fe) P Y

special-map-classifier : is-univalent 𝓤
                       → funext 𝓤 (𝓤 ⁺)
                       → (P : 𝓤 ̇ → 𝓥 ̇ ) (Y : 𝓤 ̇ )
                       → 𝓤 /[ P ] Y ≃ (Y → Σ P)
special-map-classifier {𝓤} ua fe P Y = χ-special P Y , χ-special-is-equiv ua fe P Y

Ω-is-subtype-classifier : Univalence
                        → (Y : 𝓤 ̇ ) → Subtypes Y ≃ (Y → Ω 𝓤)
Ω-is-subtype-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                  (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
                                  is-subsingleton

subtypes-form-set : Univalence → (Y : 𝓤 ̇ ) → is-set (Subtypes Y)
subtypes-form-set {𝓤} ua Y = equiv-to-set
                              (Ω-is-subtype-classifier ua Y)
                              (powersets-are-sets' ua)

retractions-into : 𝓤 ̇ → 𝓤 ⁺ ̇
retractions-into {𝓤} Y = Σ X ꞉ 𝓤 ̇ , Y ◁ X

pointed-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
pointed-types 𝓤 = Σ X ꞉ 𝓤 ̇ , X

retraction-classifier : Univalence
                      → (Y : 𝓤 ̇ ) → retractions-into Y ≃ (Y → pointed-types 𝓤)
retraction-classifier {𝓤} ua Y =
 retractions-into Y                                              ≃⟨ i ⟩
 ((𝓤 /[ id ] Y))                                                 ≃⟨ ii ⟩
 (Y → pointed-types 𝓤)                                           ■
 where
  i  = ≃-sym (Σ-cong (λ X → Σ-cong (λ f → ΠΣ-distr-≃)))
  ii = special-map-classifier (ua 𝓤)
        (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
        id Y

module surjection-classifier
         (ua : Univalence)
       where

  open import UF-PropTrunc

  module _ (pt : propositional-truncations-exist) where

   open PropositionalTruncation pt public
   open import UF-ImageAndSurjection
   open ImageAndSurjection pt public

   surjections-into : 𝓤 ̇ → 𝓤 ⁺ ̇
   surjections-into {𝓤} Y = Σ X ꞉ 𝓤 ̇ , X ↠ Y

   inhabited-types : (𝓤 : Universe) → 𝓤 ⁺ ̇
   inhabited-types 𝓤 = Σ X ꞉ 𝓤 ̇ , ∥ X ∥

   surjection-classifier : Univalence
                         → (Y : 𝓤 ̇ )
                         → surjections-into Y ≃ (Y → inhabited-types 𝓤)
   surjection-classifier {𝓤} ua = special-map-classifier (ua 𝓤)
                                   (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
                                   ∥_∥

\end{code}
