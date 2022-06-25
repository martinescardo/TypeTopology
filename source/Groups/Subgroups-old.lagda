--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

DO NOT USE. This is for documentation purpose only.  The code below
arises from an attempt to re-implement the subgroups code as developed
in UF-SIP-Exammples, but using embeddings from the get go. However it
proved to be faster to simply repurpose the subgroups submodule in
UF-SIP-Examples to use the Groups.lagda file. This is done in
subgroups.lagda.



{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import SpartanMLTT
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Univalence
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt
open import UF-Classifiers
open import UF-PropTrunc
open import UF-ImageAndSurjection
open import Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement
-- open import Groups.triv
-- open import Groups.kernel
-- open import Groups.image
open import Groups.homomorphisms

module Groups.subgroups-old
       (ua : Univalence)
       (pt : propositional-truncations-exist) where

fe : ∀ {𝓥} {𝓦} → funext 𝓥 𝓦
fe {𝓥} {𝓦} = univalence-gives-funext' 𝓥 𝓦 (ua 𝓥) (ua (𝓥 ⊔ 𝓦))


pe : ∀ {𝓥} → propext 𝓥
pe {𝓥} = univalence-gives-propext (ua 𝓥)


open ImageAndSurjection pt
open PropositionalTruncation pt

module _ {𝓤 : Universe}{G : Group 𝓤} where

  private
    _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
    _·_ = multiplication G

    e : ⟨ G ⟩
    e = unit G

  is-subgroup : (X : 𝓤 ̇) (h : X ↪ ⟨ G ⟩) → 𝓤 ̇
  is-subgroup X h = e ∈image i 
                  × ((x y : ⟨ G ⟩) → x ∈image i → y ∈image i → (x · y) ∈image i)
                  × ((x : ⟨ G ⟩) → x ∈image i → (inv G x) ∈image i)
    where
      i : X → ⟨ G ⟩
      i = etofun h

  subgroup-has-unit : {X : 𝓤 ̇} {h : X ↪ ⟨ G ⟩}
                    → is-subgroup X h → e ∈image (etofun h)
  subgroup-has-unit = pr₁
  
  subgroup-has-inv : {X : 𝓤 ̇} {h : X ↪ ⟨ G ⟩}
                   → is-subgroup X h
                   → ((x : ⟨ G ⟩) → x ∈image (etofun h) → (inv G x) ∈image (etofun h))
  subgroup-has-inv = pr₂ ∘ pr₂

  Subgroups : 𝓤 ⁺ ̇
  Subgroups = Σ 𝕏 ꞉ (Subtypes ⟨ G ⟩) , is-subgroup (pr₁ 𝕏) (pr₂ 𝕏)
      
  ⟪_⟫ : Subgroups → Subtypes ⟨ G ⟩
  ⟪_⟫ = pr₁

  Subgroups₁ : 𝓤 ⁺ ̇
  Subgroups₁ = Σ X ꞉ 𝓤 ̇ , Σ h ꞉ X ↪ ⟨ G ⟩ , is-subgroup X h

  ⟪_⟫₁ : Subgroups₁ → Subtypes ⟨ G ⟩
  ⟪ X , h , i ⟫₁ = X , h

  Subgroups→Subgroups₁ : Subgroups → Subgroups₁
  Subgroups→Subgroups₁ ((X , h) , i) = X , (h , i)

  Subgroups₁→Subgroups : Subgroups₁ → Subgroups
  Subgroups₁→Subgroups (X , (h , i)) = (X , h) , i

  Subgroups-from-to : Subgroups₁→Subgroups ∘ Subgroups→Subgroups₁ ∼ id
  Subgroups-from-to = λ  _ → refl

  Subgroups-to-from : Subgroups→Subgroups₁ ∘ Subgroups₁→Subgroups ∼ id
  Subgroups-to-from = λ _ → refl

  subgroup-to-domain : (H : Subgroups) → 𝓤 ̇
  subgroup-to-domain = pr₁ ∘ pr₁

  subgroup-to-fun : (H : Subgroups) → pr₁ (pr₁ H) → ⟨ G ⟩
  subgroup-to-fun H = pr₁ (pr₂ (pr₁ H))

  subgroup-to-embedding : (H : Subgroups) → is-embedding (subgroup-to-fun H)
  subgroup-to-embedding H = pr₂ (pr₂ (pr₁ H))
  
  being-subgroup-is-prop : (X : 𝓤 ̇) (h : X ↪ ⟨ G ⟩)
                         → is-prop (is-subgroup X h)
  being-subgroup-is-prop X (i , em) = ×-is-prop (being-in-the-image-is-prop e i)
                                         (×-is-prop
                                           (Π-is-prop fe
                                             (λ x → Π-is-prop fe
                                               (λ y → Π-is-prop fe
                                                 ((λ u → Π-is-prop fe
                                                   ((λ v → being-in-the-image-is-prop (multiplication G x y) i)))))))
                                           (Π-is-prop fe
                                             (λ x → (Π-is-prop fe
                                               ((λ u → being-in-the-image-is-prop (inv G x) i))))))

  ⟪⟫-is-embedding : is-embedding ⟪_⟫
  ⟪⟫-is-embedding = pr₁-is-embedding (λ 𝕏 → being-subgroup-is-prop (pr₁ 𝕏) (pr₂ 𝕏))

  ap-⟪⟫ : (H K : Subgroups) → H ≡ K → ⟪ H ⟫ ≡ ⟪ K ⟫
  ap-⟪⟫ H K = ap ⟪_⟫

  ap-⟪⟫-is-equiv : (H K : Subgroups) → is-equiv (ap-⟪⟫ H K)
  ap-⟪⟫-is-equiv = embedding-embedding' ⟪_⟫ (⟪⟫-is-embedding)

  subgroups-form-a-set : is-set Subgroups
  subgroups-form-a-set {H} {K} = equiv-to-prop
                                   ((ap-⟪⟫ H K) , ap-⟪⟫-is-equiv H K)
                                   (subtypes-form-set ua ⟨ G ⟩)

  subgroup-equality : (H K : Subgroups)
                    → (H ≡ K) ≃ ((x : ⟨ G ⟩) → (x ∈image (subgroup-to-fun H)) ⇔ (x ∈image (subgroup-to-fun K)))
  subgroup-equality H K = γ
    where
      X Y : 𝓤 ̇
      X = subgroup-to-domain H
      Y = subgroup-to-domain K

      h : X → ⟨ G ⟩
      h = subgroup-to-fun H

      is-h : is-embedding h
      is-h = subgroup-to-embedding H

      k : Y → ⟨ G ⟩
      k = subgroup-to-fun K

      is-k : is-embedding k
      is-k = subgroup-to-embedding K

      f : H ≡ K → ((x : ⟨ G ⟩) → (x ∈image h) ⇔ (x ∈image k))
      f p x = (transport (λ _ → x ∈image _) p) , transport (λ _ → x ∈image _) (p ⁻¹)
      
      g : ((x : ⟨ G ⟩) → (x ∈image h) ⇔ (x ∈image k)) → H ≡ K
      g = inverse (ap-⟪⟫ H K) (ap-⟪⟫-is-equiv H K) ∘ l
        where
          l : ((x : ⟨ G ⟩) → (x ∈image h) ⇔ (x ∈image k)) → ⟪ H ⟫ ≡ ⟪ K ⟫
          l φ = to-Σ-≡ (p , to-Σ-≡ ({!!} , {!!}))
            where
              α' : (x : ⟨ G ⟩) → (x ∈image h) ≡ (x ∈image k)
              α' x = pe (being-in-the-image-is-prop x h)
                       (being-in-the-image-is-prop x k)
                       (lr-implication (φ x))
                       (rl-implication (φ x))

              α : (x : ⟨ G ⟩) → (x ∈image h) ≃ (x ∈image k)
              α x = logically-equivalent-props-are-equivalent
                     (being-in-the-image-is-prop x h)
                     (being-in-the-image-is-prop x k)
                     (lr-implication (φ x))
                     (rl-implication (φ x))

              ζ : image h ≃ image k
              pr₁ ζ = NatΣ (λ x → lr-implication (φ x))
              pr₂ ζ = NatΣ-equiv (λ x → x ∈image h)
                                 (λ x → x ∈image k)
                                 (λ x → lr-implication (φ x))
                                 λ x → pr₂ (α x)

              ξ : X ≃ Y
              ξ = X       ≃⟨ (corestriction h) , η ⟩
                  image h ≃⟨ ζ ⟩
                  image k ≃⟨ ≃-sym ((corestriction k) , η') ⟩
                  Y ■
                    where
                      η : is-equiv (corestriction h)
                      η = corestriction-of-embedding-is-equivalence h (subgroup-to-embedding H)
                      η' : is-equiv (corestriction k)
                      η' = corestriction-of-embedding-is-equivalence k (subgroup-to-embedding K)

              p : X ≡ Y
              p = eqtoid (ua 𝓤) X Y ξ

      γ : (H ≡ K) ≃ ((x : ⟨ G ⟩) → (x ∈image h) ⇔ (x ∈image k))
      γ = logically-equivalent-props-are-equivalent
            subgroups-form-a-set
            (Π-is-prop fe (λ x → ×-is-prop
                             (Π-is-prop fe (λ _ → being-in-the-image-is-prop x k))
                             (Π-is-prop fe (λ _ → being-in-the-image-is-prop x h))))
            f g


