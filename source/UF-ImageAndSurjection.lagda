\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-ImageAndSurjection where

open import SpartanMLTT
open import UF-Base public
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-PropTrunc
open import UF-Retracts

\end{code}

A main application of propositional truncations is to be able to
define images and surjections:

\begin{code}

module ImageAndSurjection (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 image f = Σ y ꞉ codomain f , ∃ x ꞉ domain f , f x ≡ y

 restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
            → image f → Y
 restriction f (y , _) = y

 restriction-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-embedding(restriction f)
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
  to-Σ-≡ (∥∥-rec s (λ u → ∥∥-rec s (λ v → h u v) p') p ,
          ∥∥-is-prop _ p')
   where
    h : (Σ x ꞉ X , f x ≡ y) → (Σ x' ꞉ X , f x' ≡ y') → y ≡ y'
    h (x , e) (x' , e') = y    ≡⟨ e ⁻¹ ⟩
                          f x  ≡⟨ c x x' ⟩
                          f x' ≡⟨ e' ⟩
                          y'   ∎

 wconstant-map-to-set-truncation-of-domain-map' : (X : 𝓤 ̇ ) {Y : 𝓥 ̇}
                                               → is-set Y
                                               → (f : X → Y)
                                               → wconstant f
                                               → ∥ X ∥ → image f
 wconstant-map-to-set-truncation-of-domain-map' X s f c =
  ∥∥-rec
  (wconstant-maps-to-sets-have-propositional-images X s f c)
  (corestriction f)

 wconstant-map-to-set-truncation-of-domain-map : (X : 𝓤 ̇ ) {Y : 𝓥 ̇}
                                              → is-set Y
                                              → (f : X → Y)
                                              → wconstant f
                                              → ∥ X ∥ → Y
 wconstant-map-to-set-truncation-of-domain-map X s f c =
  restriction f ∘ wconstant-map-to-set-truncation-of-domain-map' X s f c

 wconstant-map-to-set-factors-through-truncation-of-domain : (X : 𝓤 ̇ ) {Y : 𝓥 ̇}
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
   γ : (x : X) → f x ≡ restriction f (g ∣ x ∣)
   γ x = f x                               ≡⟨ refl ⟩
         restriction f (corestriction f x) ≡⟨ ap (restriction f)
                                              (p (corestriction f x) (g ∣ x ∣)) ⟩
         restriction f (g ∣ x ∣)           ∎

\end{code}

TODO: a map is an embedding iff its corestriction is an equivalence.

\begin{code}

 is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 is-surjection f = ∀ y → ∃ x ꞉ domain f , f x ≡ y

 vv-equiv-iff-embedding-and-surjection  :  {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                        → is-vv-equiv f ⇔ is-embedding f × is-surjection f
 vv-equiv-iff-embedding-and-surjection f = g , h
  where
   g : is-vv-equiv f → is-embedding f × is-surjection f
   g i = (λ y → pr₁(pr₁ the-singletons-are-the-inhabited-propositions (i y))) ,
         (λ y → pr₂(pr₁ the-singletons-are-the-inhabited-propositions (i y)))

   h : is-embedding f × is-surjection f → is-vv-equiv f
   h (e , s) = λ y → pr₂ the-singletons-are-the-inhabited-propositions (e y , s y)

 surjective-embeddings-are-vv-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                     → is-embedding f → is-surjection f → is-vv-equiv f
 surjective-embeddings-are-vv-equivs f e s = pr₂ (vv-equiv-iff-embedding-and-surjection f) (e , s)

 surjective-embeddings-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                  → is-embedding f → is-surjection f → is-equiv f
 surjective-embeddings-are-equivs f e s = vv-equivs-are-equivs f (surjective-embeddings-are-vv-equivs f e s)

 corestriction-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                         → is-surjection (corestriction f)
 corestriction-surjection f (y , s) = ∥∥-functor g s
  where
   g : (Σ x ꞉ domain f , f x ≡ y) → Σ x ꞉ domain f , corestriction f x ≡ (y , s)
   g (x , p) = x , to-Σ-≡ (p , ∥∥-is-prop _ _)

 pt-is-surjection : {X : 𝓤 ̇ } → is-surjection(λ(x : X) → ∣ x ∣)
 pt-is-surjection t = ∥∥-rec ∥∥-is-prop (λ x → ∣ x , ∥∥-is-prop (∣ x ∣) t ∣) t

\end{code}

Surjections can be characterized as follows, modulo size:

\begin{code}

 imageInduction : ∀ {𝓦 𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
 imageInduction {𝓦} {𝓤} {𝓥} {X} {Y} f =
                (P : Y → 𝓦 ̇ ) → ((y : Y) → is-prop(P y)) → ((x : X) → P(f x)) → (y : Y) → P y

 surjection-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-surjection f → imageInduction {𝓦} f
 surjection-induction f is P isp a y = ∥∥-rec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)

 image-surjection-converse : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                           → imageInduction f → is-surjection f
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ≡ y) ∥)
                                       (λ y → ∥∥-is-prop)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {𝓦} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 (f : X → Y) (P : image f → 𝓦 ̇ )
               → (∀ y' → is-prop(P y'))
               → (∀ x → P(corestriction f x))
               → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-surjection f)

 retraction-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                       → has-section f → is-surjection f
 retraction-surjection {𝓤} {𝓥} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

\end{code}

Added 13 February 2020 by Tom de Jong.

\begin{code}

 surjection-≃-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → is-surjection f
                    → image f ≃ Y
 surjection-≃-image {𝓤} {𝓥} {X} {Y} f s =
  image f                       ≃⟨ ≃-refl _ ⟩
  (Σ y ꞉ Y , ∃ x ꞉ X , f x ≡ y) ≃⟨ Σ-cong γ ⟩
  (Σ y ꞉ Y , 𝟙)                 ≃⟨ ≃-refl _ ⟩
  Y × 𝟙                         ≃⟨ 𝟙-rneutral {𝓥} {𝓥} ⟩
  Y                             ■
   where
    γ : (y : Y) → (∃ x ꞉ X , f x ≡ y) ≃ 𝟙
    γ y = singleton-≃-𝟙 (pointed-props-are-singletons (s y) ∥∥-is-prop)

\end{code}
