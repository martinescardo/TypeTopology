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
open import UF.DiscreteAndSeparated

module _
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇ }
        {{X-is-discrete' : is-discrete' X}}
        {Y : 𝓥 ̇ }
        {{Y-is-discrete' : is-discrete' Y}}
       where

 ext⁻ : (X → List⁻ Y) → List⁻ X → List⁻ Y
 ext⁻ = extension (List⁻-DGM Y)

 unit⁻ : (f : X → List⁻ Y) (x : X) → ext⁻ f (η⁻ x) ＝ f x
 unit⁻ = triangle (List⁻-DGM Y)

module _
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
        {{X-is-discrete' : is-discrete' X}}
       where

 ext⁻-η⁻ : ext⁻ η⁻ ∼ 𝑖𝑑 (List⁻ X)
 ext⁻-η⁻ 𝔁𝓼 = (uniqueness (List⁻-DGM X) η⁻ id
                (refl , (λ _ _ → refl)) (λ _ → refl) 𝔁𝓼)⁻¹

module _
        {𝓤 𝓥 𝓦 : Universe}
        {X : 𝓤 ̇ }
        {Y : 𝓥 ̇ }
        {{Y-is-discrete' : is-discrete' Y}}
        {{X-is-discrete' : is-discrete' X}}
        {Z : 𝓦 ̇ }
        {{Z-is-discrete' : is-discrete' Z}}
       where

 assoc⁻ : (g : Y → List⁻ Z) (f : X → List⁻ Y) (𝔁𝓼 : List⁻ X)
        → ext⁻ (λ x → ext⁻ g (f x)) 𝔁𝓼 ＝ ext⁻ g (ext⁻ f 𝔁𝓼)
 assoc⁻ g f 𝔁𝓼 = a ⁻¹
  where
   h : is-hom (List⁻-DGM X) (List⁻-DGM Z) (λ x → ext⁻ g (ext⁻ f x))
   h = refl , I
    where
     I = λ 𝔁𝓼 𝔂𝓼 → ext⁻ g (ext⁻ f (𝔁𝓼 · 𝔂𝓼))               ＝⟨ I₀ 𝔁𝓼 𝔂𝓼 ⟩
                   ext⁻ g (ext⁻ f 𝔁𝓼 · ext⁻ f 𝔂𝓼)          ＝⟨ I₁ 𝔁𝓼 𝔂𝓼 ⟩
                   ext⁻ g (ext⁻ f 𝔁𝓼) · ext⁻ g (ext⁻ f 𝔂𝓼) ∎
      where
       I₀ = λ 𝔁𝓼 𝔂𝓼 → ap (ext⁻ g)
                         (homs-preserve-mul (List⁻-DGM X) (List⁻-DGM Y)
                           (ext⁻ f)
                           (extension-is-hom (List⁻-DGM Y) f)
                           𝔁𝓼 𝔂𝓼)

       I₁ = λ 𝔁𝓼 𝔂𝓼 → homs-preserve-mul (List⁻-DGM Y) (List⁻-DGM Z)
                       (ext⁻ g)
                       (extension-is-hom (List⁻-DGM Z) g)
                       (ext⁻ f 𝔁𝓼) (ext⁻ f 𝔂𝓼)

   t : (λ x → ext⁻ g (ext⁻ f x)) ∘ η⁻ ∼ (λ x → ext⁻ g (f x))
   t = λ x → ((λ 𝔁𝓼 → ext⁻ g (ext⁻ f 𝔁𝓼)) ∘ η⁻) x ＝⟨ refl ⟩
             ext⁻ g (ext⁻ f (η⁻ x))               ＝⟨ II x ⟩
             ext⁻ g (f x)                         ∎
              where
               II = λ x → ap (ext⁻ g) (triangle (List⁻-DGM Y) f x)

   a : ext⁻ g (ext⁻ f 𝔁𝓼) ＝ ext⁻ (λ x → ext⁻ g (f x)) 𝔁𝓼
   a = uniqueness (List⁻-DGM Z)
        (λ x → ext⁻ g (f x))
        (ext⁻ g ∘ ext⁻ f)
        h
        t
        𝔁𝓼

\end{code}
