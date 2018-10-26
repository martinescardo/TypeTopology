\begin{code}

{-# OPTIONS --without-K --exact-split #-}

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

module ImageAndSurjection (pt : PropTrunc) where

 open PropositionalTruncation (pt)

 image : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
 image f = Σ \y → ∃ \x → f x ≡ y

 restriction : {X : U ̇} {Y : V ̇} (f : X → Y)
            → image f → Y
 restriction f (y , _) = y

 restriction-embedding : {X : U ̇} {Y : V ̇} (f : X → Y)
                      → is-embedding(restriction f)
 restriction-embedding f = pr₁-embedding (λ y → ptisp)


 corestriction : {X : U ̇} {Y : V ̇} (f : X → Y)
             → X → image f
 corestriction f x = f x , ∣ x , refl ∣

\end{code}

TODO: a map is an embedding iff its corestriction is an equivalence.

\begin{code}

 is-surjection : {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
 is-surjection f = ∀ y → ∃ \x → f x ≡ y

 c-es  :  {X : U ̇} {Y : V ̇} (f : X → Y)
          → is-vv-equiv f ⇔ is-embedding f × is-surjection f
 c-es f = g , h
  where
   g : is-vv-equiv f → is-embedding f × is-surjection f
   g i = (λ y → pr₁(pr₁ c-es₁ (i y))) , (λ y → pr₂(pr₁ c-es₁ (i y)))

   h : is-embedding f × is-surjection f → is-vv-equiv f
   h (e , s) = λ y → pr₂ c-es₁ (e y , s y)

 corestriction-surjection : {X : U ̇} {Y : V ̇} (f : X → Y)
                         → is-surjection (corestriction f)
 corestriction-surjection f (y , s) = ptfunct g s
  where
   g : (Σ \x → f x ≡ y) → Σ \x → corestriction f x ≡ y , s
   g (x , p) = x , to-Σ-≡ (p , ptisp _ _)

 pt-is-surjection : {X : U ̇} → is-surjection(λ(x : X) → ∣ x ∣)
 pt-is-surjection t = ptrec ptisp (λ x → ∣ x , ptisp (∣ x ∣) t ∣) t

\end{code}

Surjections can be characterized as follows, modulo size:

\begin{code}

 imageInduction : ∀ {W U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ⊔ W ′ ̇
 imageInduction {W} {U} {V} {X} {Y} f =
                (P : Y → W ̇) → ((y : Y) → is-prop(P y)) → ((x : X) → P(f x)) → (y : Y) → P y

 surjection-induction : ∀ {W U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                      → is-surjection f → imageInduction {W} f
 surjection-induction f is P isp a y = ptrec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)

 image-surjection-converse : {X : U ̇} {Y : V ̇} (f : X → Y)
                           → imageInduction f → is-surjection f
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ≡ y) ∥)
                                       (λ y → ptisp)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {W U V} {X : U ̇} {Y : V ̇}
                 (f : X → Y) (P : image f → W ̇)
               → (∀ y' → is-prop(P y'))
               → (∀ x → P(corestriction f x))
               → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-surjection f)

 retraction-surjection : {X : U ̇} {Y : V ̇} (f : X → Y)
                       → has-section f → is-surjection f
 retraction-surjection {U} {V} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

\end{code}
