--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

Aug 18, 2021
--------------------------------------------------------------------------------


\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Groups.Type
open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

\end{code}

The image of a group homomorphism has an underlying type which is the
\emph{image} of the underlying function as defined in
UF-ImageAndSurjection.

\begin{code}

module Groups.Image (pt : propositional-truncations-exist) where

open import UF.ImageAndSurjection pt
open PropositionalTruncation pt

private
     fact : (X : Group 𝓤) → (x y z w : ⟨ X ⟩) → (p : x ＝ y) (q : z ＝ w) → (x ·⟨ X ⟩ z ＝ y ·⟨ X ⟩ w)
     fact X x y z w p q = (ap (λ v → v ·⟨ X ⟩ z) p) ∙ (ap (λ v → y ·⟨ X ⟩ v) q)

module _ (X : Group 𝓤) (Y : Group 𝓥) (f : ⟨ X ⟩ → ⟨ Y ⟩) (isf : is-hom X Y f) where

     group-image : Group (𝓤 ⊔ 𝓥)
     group-image = Im , group-structure-im ,
                        is-set-im ,
                        assoc-im ,
                        unit-im ,
                        left-neutral-im ,
                        right-neutral-im ,
                        λ x → inv-im x , inv-left-im x , inv-right-im x
       where
         Im : 𝓤 ⊔ 𝓥 ̇
         Im = image f

         group-structure-im : group-structure Im
         pr₁ (group-structure-im (y₁ , p₁) (y₂ , p₂)) = y₁ ·⟨ Y ⟩ y₂
         pr₂ (group-structure-im (y₁ , p₁) (y₂ , p₂)) = do
           x₁ , u₁ ← p₁
           x₂ , u₂ ← p₂
           ∣ ((x₁ ·⟨ X ⟩ x₂) , ((isf {x₁} {x₂} ∙ fact Y (f x₁) y₁ (f x₂) y₂ u₁ u₂ ) ) )∣

         is-set-im : is-set Im
         is-set-im = Σ-is-set (groups-are-sets Y) (λ _ → props-are-sets ∥∥-is-prop)

         assoc-im : associative group-structure-im
         assoc-im (y₀ , p₀) (y₁ , p₁) (y₂ , p₂) = to-Σ-＝ ( (assoc Y y₀ y₁ y₂) , ∥∥-is-prop _ _ )

         unit-im : Im
         unit-im = (e⟨ Y ⟩) , ∣ ((e⟨ X ⟩) , homs-preserve-unit X Y f isf) ∣

         left-neutral-im : left-neutral unit-im group-structure-im
         left-neutral-im (y , p) = to-Σ-＝ ((unit-left Y y) , ∥∥-is-prop _ _)

         right-neutral-im : right-neutral unit-im group-structure-im
         right-neutral-im (y , p) = to-Σ-＝ ((unit-right Y y) , (∥∥-is-prop _ _))

         inv-im : Im → Im
         pr₁ (inv-im (y , p)) = inv Y y
         pr₂ (inv-im (y , p)) = do
                   x , u ← p
                   ∣ (inv X x) , ((homs-preserve-invs X Y f isf x) ∙ (ap (λ v → inv Y v) u)) ∣

         inv-left-im : (u : Im) → group-structure-im (inv-im u) u ＝ unit-im
         inv-left-im (y , p) = to-Σ-＝ ((inv-left Y y) , (∥∥-is-prop _ _))

         inv-right-im : (u : Im) → group-structure-im u (inv-im u) ＝ unit-im
         inv-right-im (y , p) = to-Σ-＝ ((inv-right Y y) , (∥∥-is-prop _ _))

\end{code}


The group image comes with two canonical maps. One is the "injection"
into the target. We prove that it is left-cancellable, hence an
embedding. The other is the obvious map from the source, and we prove
it is a surjection.


\begin{code}

     -- Canonical map from the image to the target
     group-image-inj : ⟨ group-image ⟩ → ⟨ Y ⟩
     group-image-inj = λ { (y , p) → y}

     group-image-inj-is-hom : is-hom group-image Y group-image-inj
     group-image-inj-is-hom = refl

     -- Canonical map is left cancellable
     group-image-inj-is-lc : left-cancellable group-image-inj
     group-image-inj-is-lc u = to-Σ-＝ (u , ∥∥-is-prop _ _)

     -- Canonical map is an embedding
     group-image-inj-is-embedding : is-embedding group-image-inj
     group-image-inj-is-embedding = lc-maps-into-sets-are-embeddings
                                    group-image-inj
                                    group-image-inj-is-lc
                                    (groups-are-sets Y)

     group-image-inj-is-embedding₁ : is-embedding group-image-inj
     group-image-inj-is-embedding₁ = pr₁-is-embedding (λ y → ∃-is-prop)

     -- Canonical map from the source to the image
     group-image-srj : ⟨ X ⟩ → ⟨ group-image ⟩
     group-image-srj = λ {x → (f x) , ∣ (x , refl) ∣}

     group-image-srj-is-hom : is-hom X group-image group-image-srj
     group-image-srj-is-hom {x₁} {x₂} = to-Σ-＝ (isf , ∥∥-is-prop _ _)

     group-image-srj-is-surjection : is-surjection group-image-srj
     group-image-srj-is-surjection (y , p) = do
       x , u ← p
       ∣ x , to-Σ-＝ (u , (∥∥-is-prop _ _)) ∣

\end{code}
