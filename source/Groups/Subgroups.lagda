--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

This only exists to use the subgroups code from UF-SIP-Examples with
Groups interface. The code is almost literally imported from the
subgroup module in UF-SIP-Examples with minor adaptations, since the
interface defined by Groups is different. This relies on the proof
that the group axioms, as defined in Groups, form a proposition,
defined in the file Groups.Groups-supplement.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import SpartanMLTT
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Powerset
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Univalence
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt
open import UF-Classifiers

open import Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement
open import Groups.Homomorphisms

module Groups.Subgroups
       (𝓤 : Universe)
       (ua : Univalence) where


fe : ∀ {𝓥} {𝓦} → funext 𝓥 𝓦
fe {𝓥} {𝓦} = univalence-gives-funext' 𝓥 𝓦 (ua 𝓥) (ua (𝓥 ⊔ 𝓦))

module _ (G : Group 𝓤) where

  private
    _·_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
    _·_ = multiplication G

    e : ⟨ G ⟩
    e = unit G

    infixl 42 _·_

  group-closed : (⟨ G ⟩ → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
  group-closed 𝓐 = 𝓐 (unit G)
                 × ((x y : ⟨ G ⟩) → 𝓐 x → 𝓐 y → 𝓐 (x · y))
                 × ((x : ⟨ G ⟩) → 𝓐 x → 𝓐 (inv G x))

  Subgroups : 𝓤 ⁺ ̇
  Subgroups = Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A)

  ⟪_⟫ : Subgroups → 𝓟 ⟨ G ⟩
  ⟪ A , u , c , ι ⟫ = A

  being-group-closed-subset-is-prop : (A : 𝓟 ⟨ G ⟩)
                                    → is-prop (group-closed (_∈ A))
  being-group-closed-subset-is-prop A = ×-is-prop
                                            (∈-is-prop A (unit G))
                                         (×-is-prop
                                            (Π-is-prop fe
                                               (λ x → Π-is-prop fe
                                               (λ y → Π-is-prop fe
                                               (λ _ → Π-is-prop fe
                                               (λ _ → ∈-is-prop A (x · y))))))
                                            (Π-is-prop fe
                                               (λ x → Π-is-prop fe
                                               (λ _ → ∈-is-prop A (inv G x)))))

  ⟪⟫-is-embedding : is-embedding ⟪_⟫
  ⟪⟫-is-embedding = pr₁-is-embedding being-group-closed-subset-is-prop

  ap-⟪⟫ : (S T : Subgroups) → S ≡ T → ⟪ S ⟫ ≡ ⟪ T ⟫
  ap-⟪⟫ S T = ap ⟪_⟫

  ap-⟪⟫-is-equiv : (S T : Subgroups) → is-equiv (ap-⟪⟫ S T)
  ap-⟪⟫-is-equiv = embedding-embedding' ⟪_⟫ ⟪⟫-is-embedding

  subgroups-form-a-set : is-set Subgroups
  subgroups-form-a-set {S} {T} = equiv-to-prop
                                  (ap-⟪⟫ S T , ap-⟪⟫-is-equiv S T)
                                  (powersets-are-sets' ua)

  subgroup-equality : (S T : Subgroups)
                    → (S ≡ T)
                    ≃ ((x : ⟨ G ⟩) → (x ∈ ⟪ S ⟫) ⇔ (x ∈ ⟪ T ⟫))

  subgroup-equality S T = γ
   where
    f : S ≡ T → (x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫
    f p x = transport (λ - → x ∈ ⟪ - ⟫) p , transport (λ - → x ∈ ⟪ - ⟫) (p ⁻¹)

    h : ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫) → ⟪ S ⟫ ≡ ⟪ T ⟫
    h φ = subset-extensionality' ua α β
     where
      α : ⟪ S ⟫ ⊆ ⟪ T ⟫
      α x = lr-implication (φ x)

      β : ⟪ T ⟫ ⊆ ⟪ S ⟫
      β x = rl-implication (φ x)

    g : ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫) → S ≡ T
    g = inverse (ap-⟪⟫ S T) (ap-⟪⟫-is-equiv S T) ∘ h

    γ : (S ≡ T) ≃ ((x : ⟨ G ⟩) → x ∈ ⟪ S ⟫ ⇔ x ∈ ⟪ T ⟫)
    γ = logically-equivalent-props-are-equivalent
         subgroups-form-a-set
         (Π-is-prop fe
           (λ x → ×-is-prop
                   (Π-is-prop fe (λ _ → ∈-is-prop ⟪ T ⟫ x))
                   (Π-is-prop fe (λ _ → ∈-is-prop ⟪ S ⟫ x)))) f g

  T : 𝓤 ̇ → 𝓤 ̇
  T X = Σ _·_  ꞉ group-structure X , group-axioms X _·_

  module _ {X : 𝓤 ̇ } (h : X → ⟨ G ⟩) (e : is-embedding h) where

   private
    h-lc : left-cancellable h
    h-lc = embeddings-are-lc h e

   having-group-closed-fiber-is-prop : is-prop (group-closed (fiber h))
   having-group-closed-fiber-is-prop = being-group-closed-subset-is-prop
                                        (λ x → (fiber h x , e x))

   at-most-one-homomorphic-structure : is-prop (Σ τ ꞉ T X , is-hom (X , τ) G h)
   at-most-one-homomorphic-structure ((_*_ , gaxiom) , pmult) ((_*'_ , gaxiom') , pmult')
     = to-subtype-≡ (λ τ → being-hom-is-prop fe ((X , τ)) G h) δ
    where
     τ τ' : T X
     τ  = _*_ , gaxiom
     τ' = _*'_ , gaxiom'

     p : _*_ ≡ _*'_
     p = dfunext fe (λ x → dfunext fe (λ y → h-lc ( h (x * y)  ≡⟨ pmult ⟩
                                                    h x · h y  ≡⟨ pmult' ⁻¹ ⟩ 
                                                    h (x *' y) ∎)))
     δ : τ ≡ τ'
     δ = to-subtype-≡ (λ _ → group-axioms-is-prop fe X _) p

   group-closed-fiber-gives-homomorphic-structure : funext 𝓤 𝓤
                                                  → group-closed (fiber h)
                                                  → (Σ τ ꞉ T X , is-hom (X , τ) G h)

   group-closed-fiber-gives-homomorphic-structure fe (unitc , mulc , invc) = τ , i
    where
     φ : (x : X) → fiber h (h x)
     φ x = (x , 𝓻𝓮𝒻𝓵 (h x))

     unitH : X
     unitH = fiber-point unitc

     _*_ : X → X → X
     x * y = fiber-point (mulc (h x) (h y) (φ x) (φ y))

     invH : X → X
     invH x = fiber-point (invc (h x) (φ x))

     pmul : (x y : X) → h (x * y) ≡ h x · h y
     pmul x y = fiber-identification (mulc (h x) (h y) (φ x) (φ y))

     punit : h unitH ≡ unit G
     punit = fiber-identification unitc

     pinv : (x : X) → h (invH x) ≡ inv G (h x)
     pinv x = fiber-identification (invc (h x) (φ x))

     unitH-left : (x : X) → unitH * x ≡ x
     unitH-left x = h-lc (h (unitH * x) ≡⟨ pmul unitH x ⟩
                          h unitH · h x ≡⟨ ap (_· h x) punit ⟩
                          unit G · h x  ≡⟨ unit-left G (h x) ⟩
                          h x           ∎)

     unitH-right : (x : X) → x * unitH ≡ x
     unitH-right x = h-lc (h (x * unitH) ≡⟨ pmul x unitH ⟩
                           h x · h unitH ≡⟨ ap (h x ·_) punit ⟩
                           h x · unit G  ≡⟨ unit-right G (h x) ⟩
                           h x           ∎)

     assocH : (x y z : X) → ((x * y) * z) ≡ (x * (y * z))
     assocH x y z = h-lc (h ((x * y) * z)   ≡⟨ pmul (x * y) z ⟩
                          h (x * y) · h z   ≡⟨ ap (_· h z) (pmul x y) ⟩
                          (h x · h y) · h z ≡⟨ assoc G (h x) (h y) (h z) ⟩
                          h x · (h y · h z) ≡⟨ (ap (h x ·_) (pmul y z))⁻¹ ⟩
                          h x · h (y * z)   ≡⟨ (pmul x (y * z))⁻¹ ⟩
                          h (x * (y * z))   ∎)

     group-axiomH : (x : X) → Σ x' ꞉ X , (x' * x ≡ unitH) × (x * x' ≡ unitH)
     group-axiomH x = invH x , h-lc (h (invH x * x)    ≡⟨ pmul (invH x) x ⟩
                                     h (invH x) · h x  ≡⟨ ap (_· h x) (pinv x) ⟩
                                     inv G (h x) · h x ≡⟨ inv-left G (h x)  ⟩
                                     unit G            ≡⟨ punit ⁻¹ ⟩
                                     h unitH ∎) ,

                               h-lc (h (x * invH x)    ≡⟨ pmul x (invH x) ⟩
                                     h x · h (invH x)  ≡⟨ ap (h x ·_) (pinv x) ⟩
                                     h x · inv G (h x) ≡⟨ inv-right G (h x) ⟩
                                     unit G            ≡⟨ punit ⁻¹ ⟩
                                     h unitH ∎) 

     j : is-set X
     j = subtypes-of-sets-are-sets h h-lc (group-is-set G)

     τ : T X
     τ = _*_ , (j , (assocH , unitH , (unitH-left , (unitH-right , group-axiomH))))


     i : is-hom (X , τ) G h
     i {x} {y} = pmul x y


   homomorphic-structure-gives-group-closed-fiber : (Σ τ ꞉ T X , is-hom (X , τ) G h)
                                                  → group-closed (fiber h)

   homomorphic-structure-gives-group-closed-fiber ((_*_ , gaxiom) , pmult) = (unitc , mulc , invc)
    where
     H : Group 𝓤
     H = X , (_*_ , gaxiom)

     unitH : X
     unitH = pr₁ (pr₂ (pr₂ gaxiom))

     unitc : fiber h (unit G)
     unitc = unitH , (homs-preserve-unit H G h pmult)


     mulc : ((x y : ⟨ G ⟩) → fiber h x → fiber h y → fiber h (x · y))
     mulc x y (a , p) (b , q) = (a * b) ,
                                (h (a * b) ≡⟨ pmult {a} {b} ⟩
                                 h a · h b ≡⟨ ap₂ (λ - -' → - · -') p q ⟩
                                 x · y     ∎)

     invc : ((x : ⟨ G ⟩) → fiber h x → fiber h (inv G x))
     invc x (a , p) = inv H a ,
                      (h (inv H a) ≡⟨ homs-preserve-invs H G h pmult a ⟩
                       inv G (h a) ≡⟨ ap (inv G) p ⟩
                       inv G x     ∎)


   fiber-structure-lemma : funext 𝓤 𝓤
                         → group-closed (fiber h)
                         ≃ (Σ τ ꞉ T X , is-hom (X , τ) G h)

   fiber-structure-lemma fe = logically-equivalent-props-are-equivalent
                               having-group-closed-fiber-is-prop
                               at-most-one-homomorphic-structure
                               (group-closed-fiber-gives-homomorphic-structure fe)
                               homomorphic-structure-gives-group-closed-fiber


  characterization-of-the-type-of-subgroups : Subgroups ≃ (Σ H ꞉ Group 𝓤
                                                         , Σ h ꞉ (⟨ H ⟩ → ⟨ G ⟩)
                                                         , is-embedding h
                                                         × is-hom H G h)
  characterization-of-the-type-of-subgroups =

   Subgroups                                                                           ≃⟨ i ⟩
   (Σ A ꞉ 𝓟 ⟨ G ⟩ , group-closed (_∈ A))                                                ≃⟨ ii ⟩
   (Σ (X , h , e) ꞉ Subtypes ⟨ G ⟩ , group-closed (fiber h))                             ≃⟨ iii ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , group-closed (fiber h))                          ≃⟨ iv ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ (h , e) ꞉ X ↪ ⟨ G ⟩ , Σ τ ꞉ T X , is-hom (X , τ) G h)                   ≃⟨ v ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ h ꞉ (X → ⟨ G ⟩) , Σ e ꞉ is-embedding h , Σ τ ꞉ T X , is-hom (X , τ) G h) ≃⟨ vi ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ h ꞉ (X → ⟨ G ⟩) , Σ τ ꞉ T X , Σ e ꞉ is-embedding h , is-hom (X , τ) G h) ≃⟨ vii ⟩
   (Σ X ꞉ 𝓤 ̇ , Σ τ ꞉ T X , Σ h ꞉ (X → ⟨ G ⟩) , is-embedding h × is-hom (X , τ) G h)       ≃⟨ viii ⟩
   (Σ H ꞉ Group 𝓤 , Σ h ꞉ (⟨ H ⟩ → ⟨ G ⟩) , is-embedding h × is-hom H G h)                  ■

      where
       φ : Subtypes ⟨ G ⟩ → 𝓟 ⟨ G ⟩
       φ = χ-special is-prop ⟨ G ⟩

       j : is-equiv φ
       j = χ-special-is-equiv (ua 𝓤) fe is-prop ⟨ G ⟩

       i    = ≃-refl Subgroups
       ii   = ≃-sym (Σ-change-of-variable (λ (A : 𝓟 ⟨ G ⟩) → group-closed (_∈ A)) φ j)
       iii  = Σ-assoc
       iv   = Σ-cong (λ X → Σ-cong (λ (h , e) → fiber-structure-lemma h e fe))
       v    = Σ-cong (λ X → Σ-assoc)
       vi   = Σ-cong (λ X → Σ-cong (λ h → Σ-flip))
       vii  = Σ-cong (λ X → Σ-flip)
       viii = ≃-sym Σ-assoc


  induced-group : Subgroups → Group 𝓤
  induced-group S = pr₁ (⌜ characterization-of-the-type-of-subgroups ⌝ S)

\end{code}
