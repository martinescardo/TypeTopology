Martin Escardo and Paulo Oliva, April 2024

Lists without repetitions over a discrete types form a monad, as a
corollary of the fact that lists without repetitions over a discrete
type form the free discrete graphic monoid.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DiscreteGraphicMonoids.Monad
        (fe : Fun-Ext)
       where

open import DiscreteGraphicMonoids.Free fe
open import DiscreteGraphicMonoids.LWRDGM fe
open import DiscreteGraphicMonoids.ListsWithoutRepetitions fe
open import DiscreteGraphicMonoids.Type
open import MLTT.Spartan
open import Notation.CanonicalMap
open import UF.DiscreteAndSeparated

module _ {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {Y : 𝓥 ̇ }
         {{Y-is-discrete' : is-discrete' Y}}
      where

 ext⁻ : (X → List⁻ Y) → List⁻ X → List⁻ Y
 ext⁻ = extension (List⁻-DGM Y)

 unit⁻ : (f : X → List⁻ Y) → ext⁻ f ∘ η⁻ ∼ f
 unit⁻ = triangle (List⁻-DGM Y)

module _ {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
       where

 ext⁻-η⁻ : ext⁻ η⁻ ∼ 𝑖𝑑 (List⁻ X)
 ext⁻-η⁻ = uniqueness (List⁻-DGM X)
            η⁻
            id
            (id-is-hom (List⁻-DGM X))
            (λ _ → refl)

module _ {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {Y : 𝓥 ̇ }
         {{Y-is-discrete' : is-discrete' Y}}
         {Z : 𝓦 ̇ }
         {{Z-is-discrete' : is-discrete' Z}}
       where

 assoc⁻ : (g : Y → List⁻ Z) (f : X → List⁻ Y)
        → ext⁻ (ext⁻ g ∘ f) ∼ ext⁻ g ∘ ext⁻ f
 assoc⁻ g f = III
  where
   H : List⁻ X → List⁻ Z
   H = ext⁻ g ∘ ext⁻ f

   I : is-hom (List⁻-DGM X) (List⁻-DGM Z) H
   I = ∘-is-hom (List⁻-DGM X) (List⁻-DGM Y) (List⁻-DGM Z)
        (ext⁻ f)
        (ext⁻ g)
        (extension-is-hom (List⁻-DGM Y) f)
        (extension-is-hom (List⁻-DGM Z) g)

   II = H ∘ η⁻                ∼⟨ ∼-refl ⟩
        ext⁻ g ∘ ext⁻ f ∘ η⁻  ∼⟨ ∼-ap-∘ (ext⁻ g) (triangle (List⁻-DGM Y) f) ⟩
        ext⁻ g ∘ f            ∼∎

   III : ext⁻ (ext⁻ g ∘ f) ∼ H
   III = uniqueness (List⁻-DGM Z) (ext⁻ g ∘ f) H I II

\end{code}
