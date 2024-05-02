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

module _ {𝓤 𝓥 : Universe}
         {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {Y : 𝓥 ̇ }
         {{Y-is-discrete' : is-discrete' Y}}
      where

 ext⁻ : (X → List⁻ Y) → List⁻ X → List⁻ Y
 ext⁻ = extension (LDGM Y)

 unit⁻ : (f : X → List⁻ Y) (x : X) → ext⁻ f (η⁻ x) ＝ f x
 unit⁻ = triangle (LDGM Y)

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
       where

 ext⁻-η⁻ : ext⁻ η⁻ ∼ 𝑖𝑑 (List⁻ X)
 ext⁻-η⁻ 𝔁𝓼 = uniqueness (LDGM X)
               η⁻
               id
               (id-is-hom (LDGM X))
               (λ _ → refl) 𝔁𝓼

module _ {𝓤 𝓥 𝓦 : Universe}
         {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {Y : 𝓥 ̇ }
         {{Y-is-discrete' : is-discrete' Y}}
         {Z : 𝓦 ̇ }
         {{Z-is-discrete' : is-discrete' Z}}
       where

 assoc⁻ : (g : Y → List⁻ Z) (f : X → List⁻ Y) (𝔁𝓼 : List⁻ X)
        → ext⁻ (λ x → ext⁻ g (f x)) 𝔁𝓼 ＝ ext⁻ g (ext⁻ f 𝔁𝓼)
 assoc⁻ g f 𝔁𝓼 = III
  where
   I : is-hom (LDGM X) (LDGM Z) (λ x → ext⁻ g (ext⁻ f x))
   I = I₁ , I₂
    where
     I₁ : ext⁻ g (ext⁻ f []⁻) ＝ []⁻
     I₁ = refl

     I₂ : (𝔁𝓼 𝔂𝓼 : ⟨ LDGM X ⟩)
        → ext⁻ g (ext⁻ f (𝔁𝓼 · 𝔂𝓼)) ＝ ext⁻ g (ext⁻ f 𝔁𝓼) · ext⁻ g (ext⁻ f 𝔂𝓼)
     I₂ = homs-preserve-mul (LDGM X) (LDGM Z) ((λ x → ext⁻ g (ext⁻ f x)))
           (∘-is-hom (LDGM X) (LDGM Y) (LDGM Z)
             (ext⁻ f)
             (ext⁻ g)
             (extension-is-hom (LDGM Y) f)
             (extension-is-hom (LDGM Z) g))

   II : (λ x → ext⁻ g (ext⁻ f x)) ∘ η⁻ ∼ (λ x → ext⁻ g (f x))
   II = λ x → ((λ 𝔁𝓼 → ext⁻ g (ext⁻ f 𝔁𝓼)) ∘ η⁻) x ＝⟨ refl ⟩
              ext⁻ g (ext⁻ f (η⁻ x))               ＝⟨ II₀ x ⟩
              ext⁻ g (f x)                         ∎
               where
                II₀ = λ x → ap (ext⁻ g) (triangle (LDGM Y) f x)

   III : ext⁻ (λ x → ext⁻ g (f x)) 𝔁𝓼 ＝ ext⁻ g (ext⁻ f 𝔁𝓼)
   III = uniqueness (LDGM Z)
          (λ x → ext⁻ g (f x))
          (ext⁻ g ∘ ext⁻ f)
          I
          II
          𝔁𝓼

\end{code}
