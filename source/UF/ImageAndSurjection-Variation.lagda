Martin Escardo and Tom de Jong, October 2021

Modified from UF.ImageAndSurjection.lagda to add the parameter F.

We use F to control the universe where propositional truncations live.
For more comments and explanations, see the original files.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module UF.ImageAndSurjection-Variation (F : Universe → Universe) where

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Hedberg
open import UF.PropTrunc-Variation F
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties

module ImageAndSurjection (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _∈image_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y → (X → Y) → F (𝓤 ⊔ 𝓥) ̇
 y ∈image f = ∃ x ꞉ domain f , f x ＝ y

 being-in-the-image-is-prop : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (y : Y) (f : X → Y)
                            → is-prop (y ∈image f)
 being-in-the-image-is-prop y f = ∃-is-prop

 image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → F (𝓤 ⊔ 𝓥) ⊔ 𝓥 ̇
 image f = Σ y ꞉ codomain f , y ∈image f

 restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → image f → Y
 restriction f (y , _) = y

 restriction-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → is-embedding (restriction f)
 restriction-embedding f = pr₁-is-embedding (λ y → ∥∥-is-prop)

 corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
               → X → image f
 corestriction f x = f x , ∣ x , refl ∣

 wconstant-maps-to-sets-have-propositional-images : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ }
                                                  → is-set Y
                                                  → (f : X → Y)
                                                  → wconstant f
                                                  → is-prop (image f)
 wconstant-maps-to-sets-have-propositional-images X s f c (y , p) (y' , p') =
  to-Σ-＝ (∥∥-rec s (λ u → ∥∥-rec s (λ v → h u v) p') p ,
          ∥∥-is-prop _ p')
   where
    h : (Σ x ꞉ X , f x ＝ y) → (Σ x' ꞉ X , f x' ＝ y') → y ＝ y'
    h (x , e) (x' , e') = y    ＝⟨ e ⁻¹ ⟩
                          f x  ＝⟨ c x x' ⟩
                          f x' ＝⟨ e' ⟩
                          y'   ∎

 wconstant-map-to-set-truncation-of-domain-map' : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ }
                                                → is-set Y
                                                 → (f : X → Y)
                                                → wconstant f
                                                → ∥ X ∥ → image f
 wconstant-map-to-set-truncation-of-domain-map' X s f c =
  ∥∥-rec
  (wconstant-maps-to-sets-have-propositional-images X s f c)
  (corestriction f)

 wconstant-map-to-set-truncation-of-domain-map : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ }
                                               → is-set Y
                                               → (f : X → Y)
                                               → wconstant f
                                                 → ∥ X ∥ → Y
 wconstant-map-to-set-truncation-of-domain-map X s f c =
  restriction f ∘ wconstant-map-to-set-truncation-of-domain-map' X s f c

 wconstant-map-to-set-factors-through-truncation-of-domain : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ }
                                                             (s : is-set Y)
                                                             (f : X → Y)
                                                             (c : wconstant f)
                                                           → f ∼ (wconstant-map-to-set-truncation-of-domain-map X s f c) ∘ ∣_∣
 wconstant-map-to-set-factors-through-truncation-of-domain X s f c = γ
  where
   g : ∥ X ∥ → image f
   g = wconstant-map-to-set-truncation-of-domain-map' X s f c
   p : is-prop (image f)
   p = wconstant-maps-to-sets-have-propositional-images X s f c
   γ : (x : X) → f x ＝ restriction f (g ∣ x ∣)
   γ x = f x                               ＝⟨ refl ⟩
         restriction f (corestriction f x) ＝⟨ ap (restriction f)
                                              (p (corestriction f x) (g ∣ x ∣)) ⟩
         restriction f (g ∣ x ∣)           ∎

 is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → F (𝓤 ⊔ 𝓥) ⊔ 𝓥 ̇
 is-surjection f = ∀ y → ∃ x ꞉ domain f , f x ＝ y

 _↠_ : 𝓤 ̇ → 𝓥 ̇ → F (𝓤 ⊔ 𝓥) ⊔ 𝓤 ⊔ 𝓥 ̇
 X ↠ Y = Σ f ꞉ (X → Y) , is-surjection f

 image-is-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (f : X → Y)
              → is-set Y
              → is-set (image f)
 image-is-set f i = subsets-of-sets-are-sets _
                     (λ y → y ∈image f) i
                     (being-in-the-image-is-prop _ f)

 vv-equiv-iff-embedding-and-surjection  :  {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                        → is-vv-equiv f ↔ is-embedding f × is-surjection f
 vv-equiv-iff-embedding-and-surjection f = g , h
  where
   g : is-vv-equiv f → is-embedding f × is-surjection f
   g i = (λ y → pr₁ (pr₁ the-singletons-are-the-inhabited-propositions (i y))) ,
         (λ y → pr₂ (pr₁ the-singletons-are-the-inhabited-propositions (i y)))

   h : is-embedding f × is-surjection f → is-vv-equiv f
   h (e , s) = λ y → pr₂ the-singletons-are-the-inhabited-propositions (e y , s y)

 surjective-embeddings-are-vv-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     → is-embedding f → is-surjection f → is-vv-equiv f
 surjective-embeddings-are-vv-equivs f e s = pr₂ (vv-equiv-iff-embedding-and-surjection f) (e , s)

 surjective-embeddings-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-embedding f → is-surjection f → is-equiv f
 surjective-embeddings-are-equivs f e s = vv-equivs-are-equivs f (surjective-embeddings-are-vv-equivs f e s)

 corestriction-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                             → is-surjection (corestriction f)
 corestriction-is-surjection f (y , s) = ∥∥-functor g s
  where
   g : (Σ x ꞉ domain f , f x ＝ y) → Σ x ꞉ domain f , corestriction f x ＝ (y , s)
   g (x , p) = x , to-Σ-＝ (p , ∥∥-is-prop _ _)

 pt-is-surjection : {X : 𝓤 ̇ } → is-surjection (λ (x : X) → ∣ x ∣)
 pt-is-surjection t = ∥∥-rec ∥∥-is-prop (λ x → ∣ x , ∥∥-is-prop (∣ x ∣) t ∣) t


 NatΣ-is-surjection : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                    → ((x : X) → is-surjection (ζ x))
                    → is-surjection (NatΣ ζ)
 NatΣ-is-surjection A B ζ i (x , b) = γ
  where
   δ : (Σ a ꞉ A x , ζ x a ＝ b)
     → Σ (x' , a) ꞉ Σ A , (x' , ζ x' a) ＝ (x , b)
   δ (a , p) = (x , a) , (ap (x ,_) p)

   γ : ∃ (x' , a) ꞉ Σ A , (x' , ζ x' a) ＝ (x , b)
   γ = ∥∥-functor δ (i x b)

 corestriction-of-embedding-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                           → is-embedding f
                                           → is-equiv (corestriction f)
 corestriction-of-embedding-is-equivalence f e =
  surjective-embeddings-are-equivs f' e' s'
   where
    f' : domain f → image f
    f' = corestriction f
    s' : is-surjection f'
    s' = corestriction-is-surjection f
    e' : is-embedding f'
    e' (y , p) = retract-of-prop γ (e y)
     where
      γ : fiber f' (y , p) ◁ fiber f y
      γ = Σ-retract (λ x → f' x ＝ y , p) (λ x → f x ＝ y) ϕ
       where
        ϕ : (x : domain f) → (f' x ＝ (y , p)) ◁ (f x ＝ y)
        ϕ x = ρ , σ , η
         where
          ρ : f x ＝ y → f' x ＝ (y , p)
          ρ q = to-subtype-＝ (λ y' → ∥∥-is-prop) q
          σ : f' x ＝ (y , p) → f x ＝ y
          σ q' = ap pr₁ q'
          η : ρ ∘ σ ∼ id
          η refl = to-Σ-＝ (refl , q)    ＝⟨ ap (λ - → to-Σ-＝ (refl , -)) h ⟩
                   to-Σ-＝ (refl , refl) ＝⟨ refl ⟩
                   refl                 ∎
           where
            q : ∣ x , refl ∣ ＝ ∣ x , refl ∣
            q = ∥∥-is-prop ∣ x , refl ∣ ∣ x , refl ∣
            h : q ＝ refl
            h = props-are-sets ∥∥-is-prop q refl

 embedding-if-corestriction-is-equivalence : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                           → is-equiv (corestriction f)
                                           → is-embedding f
 embedding-if-corestriction-is-equivalence f i =
  embedding-closed-under-∼ f' f (∘-is-embedding e₁ e₂) H
   where
    f' : domain f → codomain f
    f' = pr₁ ∘ corestriction f
    H : f ∼ pr₁ ∘ corestriction f
    H x = refl
    e₁ : is-embedding (corestriction f)
    e₁ = equivs-are-embeddings (corestriction f) i
    e₂ : is-embedding pr₁
    e₂ = pr₁-is-embedding (λ y → ∥∥-is-prop)

 imageInduction : ∀ {𝓦 𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
 imageInduction {𝓦} {𝓤} {𝓥} {X} {Y} f =
                (P : Y → 𝓦 ̇ ) → ((y : Y) → is-prop (P y)) → ((x : X) → P (f x)) → (y : Y) → P y

 surjection-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-surjection f → imageInduction {𝓦} f
 surjection-induction f is P isp a y = ∥∥-rec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)

 image-surjection-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                           → imageInduction f → is-surjection f
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ＝ y) ∥)
                                       (λ y → ∥∥-is-prop)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {𝓦} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                   (f : X → Y) (P : image f → 𝓦 ̇ )
                 → (∀ y' → is-prop (P y'))
                 → (∀ x → P (corestriction f x))
                 → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-is-surjection f)

 retraction-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → has-section f → is-surjection f
 retraction-surjection {𝓤} {𝓥} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

 pr₁-is-surjection : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                   → ((x : X) → ∥ A x ∥)
                   → is-surjection (λ (σ : Σ A) → pr₁ σ)
 pr₁-is-surjection A s x = γ
  where
   δ : A x → Σ σ ꞉ Σ A , pr₁ σ ＝ x
   δ a = (x , a) , refl

   γ : ∃ σ ꞉ Σ A , pr₁ σ ＝ x
   γ = ∥∥-functor δ (s x)

 pr₁-is-surjection-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                            → is-surjection (λ (σ : Σ A) → pr₁ σ)
                            → ((x : X) → ∥ A x ∥)
 pr₁-is-surjection-converse A s x = γ
  where
   δ : (Σ σ ꞉ Σ A , pr₁ σ ＝ x) → A x
   δ ((.x , a) , refl) = a

   γ : ∥ A x ∥
   γ = ∥∥-functor δ (s x)

 surjection-≃-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-surjection f
                    → image f ≃ Y
 surjection-≃-image {𝓤} {𝓥} {X} {Y} f s =
  image f                       ≃⟨ ≃-refl _ ⟩
  (Σ y ꞉ Y , ∃ x ꞉ X , f x ＝ y) ≃⟨ Σ-cong γ ⟩
  (Σ y ꞉ Y , 𝟙)                 ≃⟨ ≃-refl _ ⟩
  Y × 𝟙                         ≃⟨ 𝟙-rneutral {𝓥} {𝓥} ⟩
  Y                             ■
   where
    γ : (y : Y) → (∃ x ꞉ X , f x ＝ y) ≃ 𝟙
    γ y = singleton-≃-𝟙 (pointed-props-are-singletons (s y) ∥∥-is-prop)

 ∘-is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
                 → is-surjection f → is-surjection g → is-surjection (g ∘ f)
 ∘-is-surjection {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} σ τ z =
  ∥∥-rec ∥∥-is-prop γ₁ (τ z)
   where
    γ₁ : (Σ y ꞉ Y , g y ＝ z) → ∃ x ꞉ X , (g ∘ f) x ＝ z
    γ₁ (y , q) = ∥∥-functor γ₂ (σ y)
     where
      γ₂ : (Σ x ꞉ X , f x ＝ y) → Σ x ꞉ X , (g ∘ f) x ＝ z
      γ₂ (x , p) = (x , (g (f x) ＝⟨ ap g p ⟩
                         g y     ＝⟨ q ⟩
                         z       ∎))

 equivs-are-surjections : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                        → is-equiv f → is-surjection f
 equivs-are-surjections ((ρ , η) , (σ , ε)) y = ∣ ρ y , η y ∣

\end{code}
