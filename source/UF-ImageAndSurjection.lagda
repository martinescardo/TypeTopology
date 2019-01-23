\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-ImageAndSurjection where

open import SpartanMLTT
open import UF-Base public
open import UF-Equiv
open import UF-Embedding
open import UF-PropTrunc
open import UF-Retracts

\end{code}

A main application of propositional truncations is to be able to
define images and surjections:

\begin{code}

module ImageAndSurjection (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 image : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 image f = Σ \y → ∃ \x → f x ≡ y

 restriction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
            → image f → Y
 restriction f (y , _) = y

 restriction-embedding : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                      → is-embedding(restriction f)
 restriction-embedding f = pr₁-embedding (λ y → ∥∥-is-a-prop)


 corestriction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
             → X → image f
 corestriction f x = f x , ∣ x , refl ∣

\end{code}

TODO: a map is an embedding iff its corestriction is an equivalence.

\begin{code}

 is-surjection : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ̇
 is-surjection f = ∀ y → ∃ \x → f x ≡ y

 c-es  :  {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
          → is-vv-equiv f ⇔ is-embedding f × is-surjection f
 c-es f = g , h
  where
   g : is-vv-equiv f → is-embedding f × is-surjection f
   g i = (λ y → pr₁(pr₁ c-es₁ (i y))) , (λ y → pr₂(pr₁ c-es₁ (i y)))

   h : is-embedding f × is-surjection f → is-vv-equiv f
   h (e , s) = λ y → pr₂ c-es₁ (e y , s y)

 corestriction-surjection : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                         → is-surjection (corestriction f)
 corestriction-surjection f (y , s) = ∥∥-funct g s
  where
   g : (Σ \x → f x ≡ y) → Σ \x → corestriction f x ≡ y , s
   g (x , p) = x , to-Σ-≡ (p , ∥∥-is-a-prop _ _)

 pt-is-surjection : {X : 𝓤 ̇} → is-surjection(λ(x : X) → ∣ x ∣)
 pt-is-surjection t = ∥∥-rec ∥∥-is-a-prop (λ x → ∣ x , ∥∥-is-a-prop (∣ x ∣) t ∣) t

\end{code}

Surjections can be characterized as follows, modulo size:

\begin{code}

 imageInduction : ∀ {𝓦 𝓤 𝓥} {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦  ⁺ ̇
 imageInduction {𝓦} {𝓤} {𝓥} {X} {Y} f =
                (P : Y → 𝓦 ̇) → ((y : Y) → is-prop(P y)) → ((x : X) → P(f x)) → (y : Y) → P y

 surjection-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                      → is-surjection f → imageInduction {𝓦} f
 surjection-induction f is P isp a y = ∥∥-rec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)

 image-surjection-converse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                           → imageInduction f → is-surjection f
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ≡ y) ∥)
                                       (λ y → ∥∥-is-a-prop)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {𝓦} {X : 𝓤 ̇} {Y : 𝓥 ̇}
                 (f : X → Y) (P : image f → 𝓦 ̇)
               → (∀ y' → is-prop(P y'))
               → (∀ x → P(corestriction f x))
               → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-surjection f)

 retraction-surjection : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y)
                       → has-section f → is-surjection f
 retraction-surjection {𝓤} {𝓥} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

\end{code}
