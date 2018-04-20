\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-ImageAndSurjection where

open import SpartanMLTT public
open import UF-Base public
open import UF-Subsingletons public
open import UF-Yoneda public
open import UF-Retracts public
open import UF-Subsingleton-Retracts public
open import UF-Equiv public
open import UF-LeftCancellable public
open import UF-FunExt public
open import UF-Univalence public
open import UF-Embedding public
open import UF-Subsingleton-FunExt public
open import UF-Retracts-FunExt public
open import UF-PropTrunc

\end{code}

A main application of propositional truncations is to be able to
define images and surjections:

\begin{code}

module ImageAndSurjection (pt : PropTrunc) where

 open PropositionalTruncation (pt)

 image : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
 image f = Σ \y → ∃ \x → f x ≡ y

 restriction : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
            → image f → Y
 restriction f (y , _) = y

 restriction-embedding : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                      → isEmbedding(restriction f)
 restriction-embedding f = pr₁-embedding (λ y → ptisp)


 corestriction : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
             → X → image f
 corestriction f x = f x , ∣ x , refl ∣

\end{code}

TODO: a map is an embedding iff its corestriction is an equivalence.

\begin{code}

 isSurjection : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
 isSurjection f = ∀ y → ∃ \x → f x ≡ y

 c-es  :  ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
          → isVoevodskyEquiv f ⇔ isEmbedding f × isSurjection f
 c-es f = g , h
  where
   g : isVoevodskyEquiv f → isEmbedding f × isSurjection f 
   g i = (λ y → pr₁(pr₁ c-es₁ (i y))) , (λ y → pr₂(pr₁ c-es₁ (i y)))
   
   h : isEmbedding f × isSurjection f → isVoevodskyEquiv f
   h (e , s) = λ y → pr₂ c-es₁ (e y , s y)

 corestriction-surjection : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                         → isSurjection (corestriction f)
 corestriction-surjection f (y , s) = ptfunct g s
  where
   g : (Σ \x → f x ≡ y) → Σ \x → corestriction f x ≡ y , s
   g (x , p) = x , to-Σ-Id (λ y → ∥ Σ (λ x → f x ≡ y) ∥) (p , (ptisp _ _))

 pt-is-surjection : ∀ {U} {X : U ̇} → isSurjection(λ(x : X) → ∣ x ∣)
 pt-is-surjection t = ptrec ptisp (λ x → ∣ x , ptisp (∣ x ∣) t ∣) t

\end{code}

Surjections can be characterized as follows, modulo size:

\begin{code}

 imageInduction : ∀ {W U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ⊔ W ′ ̇
 imageInduction {W} {U} {V} {X} {Y} f =
                (P : Y → W ̇) → ((y : Y) → isProp(P y)) → ((x : X) → P(f x)) → (y : Y) → P y

 surjection-induction : ∀ {W U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
                      → isSurjection f → imageInduction {W} f 
 surjection-induction f is P isp a y = ptrec (isp y)
                                             (λ σ → transport P (pr₂ σ) (a (pr₁ σ)))
                                             (is y)                

 image-surjection-converse : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
                           → imageInduction f → isSurjection f 
 image-surjection-converse f is' = is' (λ y → ∥ Σ (λ x → f x ≡ y) ∥)
                                       (λ y → ptisp)
                                       (λ x → ∣ x , refl ∣)

 image-induction : ∀ {W U V} {X : U ̇} {Y : V ̇}
                 (f : X → Y) (P : image f → W ̇)
               → (∀ y' → isProp(P y'))
               → (∀ x → P(corestriction f x))
               → ∀ y' → P y'
 image-induction f = surjection-induction (corestriction f)
                                          (corestriction-surjection f)

 retraction-surjection : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y) 
                       → hasSection f → isSurjection f 
 retraction-surjection {U} {V} {X} f φ y = ∣ pr₁ φ y , pr₂ φ y ∣

\end{code}
