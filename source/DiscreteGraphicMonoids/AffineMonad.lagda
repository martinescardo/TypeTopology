Martin Escardo and Paulo Oliva, April 2024

Non-empty lists without repetitions over a discrete types form a
submonad of the monad of lists without repetitions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module DiscreteGraphicMonoids.AffineMonad
        (fe : Fun-Ext)
       where

open import MLTT.Spartan
open import MLTT.List
            renaming (_∷_ to _•_ ;          -- typed as \bub
                      _++_ to _◦_ ;         -- typed as \buw
                      ++-assoc to ◦-assoc ;
                      is-non-empty-++ to is-non-empty-◦)
open import DiscreteGraphicMonoids.Free fe
open import DiscreteGraphicMonoids.LWRDGM fe
open import DiscreteGraphicMonoids.ListsWithoutRepetitions fe
open import DiscreteGraphicMonoids.Monad fe
open import DiscreteGraphicMonoids.Type
open import Notation.CanonicalMap
open import UF.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Equiv

being-non-empty-is-prop : {X : 𝓤 ̇ } (xs : List X) → is-prop (is-non-empty xs)
being-non-empty-is-prop []       = 𝟘-is-prop
being-non-empty-is-prop (x • xs) = 𝟙-is-prop

List⁻⁺ : (X : 𝓤 ̇ ) {{_ : is-discrete' X}} → 𝓤 ̇
List⁻⁺ X = Σ 𝔁𝓼 ꞉ List⁻ X , is-non-empty (ι 𝔁𝓼)

module _ {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
       where

 η⁻⁺ : X → List⁻⁺ X
 η⁻⁺ x = η⁻ x , ⋆

 underlying-list⁻ : List⁻⁺ X → List⁻ X
 underlying-list⁻ = pr₁

 underlying-list⁻⁺ : List⁻⁺ X → List X
 underlying-list⁻⁺ = underlying-list ∘ underlying-list⁻

 instance
  canonical-map-List⁻⁺-to-List⁻ : Canonical-Map (List⁻⁺ X) (List⁻ X)
  ι {{canonical-map-List⁻⁺-to-List⁻}} = underlying-list⁻

  canonical-map-List⁻⁺-to-List : Canonical-Map (List⁻⁺ X) (List X)
  ι {{canonical-map-List⁻⁺-to-List}} = underlying-list⁻⁺

 underlying-list⁻⁺-is-non-empty
  : (𝔁𝓼 : List⁻⁺ X)
  → is-non-empty (ι 𝔁𝓼)
 underlying-list⁻⁺-is-non-empty = pr₂


 to-List⁻⁺-＝ : {𝑥𝑠 𝑦𝑠 : List⁻⁺ X} → ι 𝑥𝑠 ＝ ι 𝑦𝑠 → 𝑥𝑠 ＝ 𝑦𝑠
 to-List⁻⁺-＝ = to-subtype-＝ (being-non-empty-is-prop ∘ ι)

module _ {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {Y : 𝓥 ̇ }
         {{Y-is-discrete' : is-discrete' Y}}
      where

 ext⁻⁺ : (X → List⁻⁺ Y) → List⁻⁺ X → List⁻⁺ Y
 ext⁻⁺ f 𝑥𝑠 = 𝑓 (ι 𝑥𝑠) , I (ι 𝑥𝑠) (underlying-list⁻⁺-is-non-empty 𝑥𝑠)
  where
   𝑓 : List⁻ X → List⁻ Y
   𝑓 = ext⁻ (ι ∘ f)

   I : (𝔁𝓼 : List⁻ X) → is-non-empty (ι 𝔁𝓼) → is-non-empty (ι (𝑓 𝔁𝓼))
   I ((x • xs) , a) ⋆ = I₁
    where
     b : ρ xs ＝ xs
     b = ρ-tail x xs a

     𝔁𝓼 : List⁻ X
     𝔁𝓼 = xs , b

     I₀ =
      ι (𝑓 ((x • xs) , a))                     ＝⟨ ⦅1⦆ ⟩
      ι (𝑓 (η⁻ x · 𝔁𝓼))                        ＝⟨ ⦅2⦆ ⟩
      ι (𝑓 (η⁻ x) · 𝑓 𝔁𝓼)                      ＝⟨ ⦅3⦆ ⟩
      ι (ι (f x) · 𝑓 𝔁𝓼)                       ＝⟨ refl ⟩
      ρ (ι (f x) ◦ ι (𝑓 𝔁𝓼))                   ＝⟨ ⦅4⦆ ⟩
      ρ (ι (f x)) ◦ Δ (ι (f x)) (ρ (ι (𝑓 𝔁𝓼))) ∎
       where
        ⦅1⦆ = ap (ι ∘ 𝑓) (·-lemma x xs a)
        ⦅2⦆ = ap ι (homs-preserve-mul (List⁻-DGM X) (List⁻-DGM Y) 𝑓
                      (extension-is-hom (List⁻-DGM Y) (ι ∘ f)) (η⁻ x) 𝔁𝓼)
        ⦅3⦆ = ap (λ - → ι (- · 𝑓 𝔁𝓼)) (triangle (List⁻-DGM Y) (ι ∘ f) x)
        ⦅4⦆ = ρ-◦ (ι (f x)) (ι (𝑓 𝔁𝓼))

     I₁ : is-non-empty (ι (𝑓 ((x • xs) , a)))
     I₁ = transport⁻¹ is-non-empty I₀
           (is-non-empty-◦
             (ρ (ι (f x)))
             (Δ (ι (f x)) (ρ (ι (𝑓 𝔁𝓼))))
             (ρ-is-non-empty (ι (f x)) (underlying-list⁻⁺-is-non-empty (f x))))

 unit⁻⁺ : (f : X → List⁻⁺ Y) → ext⁻⁺ f ∘ η⁻⁺ ∼ f
 unit⁻⁺ f x = to-List⁻⁺-＝ (unit⁻ (ι ∘ f) x)

module _ {X : 𝓤 ̇ }
         {{X-is-discrete' : is-discrete' X}}
         {Y : 𝓥 ̇ }
         {{Y-is-discrete' : is-discrete' Y}}
         {Z : 𝓦 ̇ }
         {{Z-is-discrete' : is-discrete' Z}}
       where

 assoc⁻⁺ : (g : Y → List⁻⁺ Z) (f : X → List⁻⁺ Y)
         → ext⁻⁺ (ext⁻⁺ g ∘ f) ∼ ext⁻⁺ g ∘ ext⁻⁺ f
 assoc⁻⁺ g f 𝑥𝑠 = to-List⁻⁺-＝ (assoc⁻ (ι ∘ g) (ι ∘ f) (ι 𝑥𝑠))

instance
 𝟙⁻-is-discrete' : is-discrete' (𝟙 {𝓤})
 𝟙⁻-is-discrete' = discrete-gives-discrete' 𝟙-is-discrete

affine⁻⁺ : is-equiv (η⁻⁺ {𝓤} {𝟙})
affine⁻⁺ = qinvs-are-equivs f (g , gf , fg)
 where
   f : 𝟙 → List⁻⁺ 𝟙
   f ⋆ = ((⋆ • []) , refl) , cons-is-non-empty

   g : List⁻⁺ 𝟙 → 𝟙
   g _ = ⋆

   fg : f ∘ g ∼ id
   fg (((⋆ • []) , refl) , cons-is-non-empty) = refl
   fg (((⋆ • ⋆ • xs) , no-reps) , cons-is-non-empty) =
    𝟘-elim (repetition-lemma ⋆ xs no-reps)

   gf : g ∘ f ∼ id
   gf ⋆ = refl

\end{code}
