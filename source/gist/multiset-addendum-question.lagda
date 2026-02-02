Alice Laroche, 14th June 2024

This file answers the question asked in Iterative.Multisets-Addendum
That is : Is there a function Πᴹ of the above type that satisfies the
following equation?

Σ Πᴹ ꞉ ((X → 𝕄) → 𝕄)
     , ((A : X → 𝕄) → Πᴹ A ＝ ssup
                               (Π x ꞉ X , 𝕄-root (A x))
                               (λ g → Πᴹ (λ x → 𝕄-forest (A x) (g x))))

We prove that it isn't the case in general, as the existence of function for
the empty type would allow infinite recursion.
We then prove that the function exists up to equivalence for pointed types,
and, admitting function extensionality, for inhabited types.


\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Univalence
open import W.Type

module gist.multiset-addendum-question
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤

swap-Idtofun : {X Y : 𝓤 ̇ } {Z : 𝓥 ̇ } → {f : X → Z} {g : Y → Z}
             → (p : Y ＝ X)
             → f ∘ Idtofun p ＝ g
             → f ＝ g ∘ Idtofun⁻¹ p
swap-Idtofun  refl refl = refl

Question𝟘 :
 ¬ (Σ Πᴹ ꞉ ((𝟘 {𝓤} → 𝕄) → 𝕄)
         , ((A : 𝟘 → 𝕄) → Πᴹ A ＝ ssup
                                  (Π x ꞉ 𝟘 , 𝕄-root (A x))
                                  (λ g → Πᴹ (λ x → 𝕄-forest (A x) (g x)))))
Question𝟘 (Πᴹ , eq) = recurs A (Πᴹ A) (eq A)
 where
  A : 𝟘 → 𝕄
  A x = 𝟘-elim x

  recurs : (A : 𝟘 → 𝕄) → (x : 𝕄)
       → ¬(x ＝ ssup
                (Π x ꞉ 𝟘 , 𝕄-root (A x))
                (λ g → Πᴹ (λ x → 𝕄-forest (A x) (g x))))
  recurs A (ssup X φ) eq' = recurs A' (φ I) II
   where
    I : X
    I =  transport⁻¹ 𝕄-root eq' (λ x → 𝟘-elim x)

    A' : 𝟘 → 𝕄
    A' x = 𝕄-forest (A x) (Idtofun (pr₁ (from-𝕄-＝ eq')) I x)

    II : φ I ＝ ssup
                (Π x ꞉ 𝟘 , 𝕄-root (A' x))
                (λ g → Πᴹ (λ x → 𝕄-forest (A' x) (g x)))
    II = happly (pr₂ (from-𝕄-＝ eq')) I
       ∙ (eq A')

Question-is-false : ¬ Question
Question-is-false Q = Question𝟘 (Q {𝟘})

module _ {X : 𝓤 ̇ } where

 data _<_ : (X → 𝕄) → (X → 𝕄) → (𝓤 ⁺) ̇ where
  smaller : {f g : X → 𝕄} → ((x : X) → f x ⁅ g x) → f < g

 open import Ordinals.Notions _<_

 <-is-well-founded : X → is-well-founded
 <-is-well-founded x f = acc (rec' x f (f x) refl)
  where
   rec' : (x : X) (f : X → 𝕄) (m : 𝕄) → m ＝ f x
      → (g : X → 𝕄) → g < f
      → is-accessible g
   rec' x f (ssup Y φ) eq g (smaller p) =
    acc (rec' x g (φ II) (III ∙ pr₂ (p x)))
    where
     I : Σ p ꞉ Y ＝ 𝕄-root (f x) , φ ＝ (𝕄-forest (f x)) ∘ Idtofun p
     I = from-𝕄-＝ (eq ∙ 𝕄-η (f x) ⁻¹)

     II : Y
     II = Idtofun⁻¹ (pr₁ I) (pr₁ (p x))

     III : φ II ＝ 𝕄-forest (f x) (pr₁ (p x))
     III = happly'
            (φ ∘ Idtofun⁻¹ (pr₁ I))
            (𝕄-forest (f x))
            (swap-Idtofun (pr₁ I) (pr₂ I ⁻¹) ⁻¹)
            (pr₁ (p x))

 module without-funext where

  QuestionX :
   X → Σ Πᴹ ꞉ ((X → 𝕄) → 𝕄)
            , ((A : X → 𝕄) → Πᴹ A ≃ᴹ ssup
                                      (Π x ꞉ X , 𝕄-root (A x))
                                      (λ g → Πᴹ (λ x → 𝕄-forest (A x) (g x))))
  QuestionX x = Πᴹ'' , eqv
   where
    I : (A : X → 𝕄) → ((g : X → 𝕄) → g < A → 𝕄) → 𝕄
    I A rec = ssup
               (Π x ꞉ X , 𝕄-root (A x))
               (λ g → rec (λ x → 𝕄-forest (A x) (g x))
                          (smaller λ y → (g y) , refl))

    Πᴹ' : (A : X → 𝕄) → is-accessible A → 𝕄
    Πᴹ' A = transfinite-induction'
             (λ - → 𝕄)
             I
             A

    Πᴹ'' : (A : X → 𝕄) → 𝕄
    Πᴹ'' A = Πᴹ' A (<-is-well-founded x A)

    II : (A : X → 𝕄) (acc₁ : is-accessible A) → Πᴹ' A acc₁ ＝ _
    II A acc₁ =  transfinite-induction'-behaviour (λ - → 𝕄) I A acc₁

    III : (A : X → 𝕄)
        → ( (g : X → 𝕄)
            → g < A
            → (acc₁ acc₂ : is-accessible g)
            → Πᴹ' g acc₁ ≃ᴹ Πᴹ' g acc₂)
        → (acc₁ acc₂ : is-accessible A) → Πᴹ' A acc₁ ≃ᴹ Πᴹ' A acc₂
    III A rec acc₁ acc₂ = transport₂ _≃ᴹ_ (II A acc₁ ⁻¹) (II A acc₂ ⁻¹)
                           ((≃-refl _)
                           , λ g → rec (λ x → 𝕄-forest (A x) (g x))
                                       (smaller λ y → (g y) , refl)
                                       (prev acc₁ _ _)
                                       (prev acc₂ _ _))

    IV : (A : X → 𝕄) → (acc₁ acc₂ : is-accessible A)
        → Πᴹ' A acc₁ ≃ᴹ Πᴹ' A acc₂
    IV A = transfinite-induction'
            (λ A → (acc₁ acc₂ : is-accessible A) → Πᴹ' A acc₁ ≃ᴹ Πᴹ' A acc₂)
            III
            A
            (<-is-well-founded x A)

    eqv : (A : X → 𝕄)
        → Πᴹ'' A ≃ᴹ ssup
                     (Π x ꞉ X , 𝕄-root (A x))
                     (λ g → Πᴹ'' (λ x → 𝕄-forest (A x) (g x)))
    eqv A =
     transport⁻¹
      (_≃ᴹ ssup
            (Π x ꞉ X , 𝕄-root (A x))
            (λ g → Πᴹ'' (λ x → 𝕄-forest (A x) (g x))))
      (transfinite-induction'-behaviour (λ - → 𝕄) I A (<-is-well-founded x A))
      ((≃-refl _) , λ g → IV
                           (λ x → 𝕄-forest (A x) (g x))
                           (prev (<-is-well-founded x A) _ _)
                           (<-is-well-founded x _))

 module with-funext (pt : propositional-truncations-exist) (fe : FunExt) where

  open PropositionalTruncation pt

  <-is-well-founded' : ∥ X ∥ → is-well-founded
  <-is-well-founded' x f = ∥∥-rec
                            (accessibility-is-prop fe f)
                            (λ x → <-is-well-founded x f)
                            x

  QuestionX :
   ∥ X ∥ → Σ Πᴹ ꞉ ((X → 𝕄) → 𝕄)
                , ((A : X → 𝕄) → Πᴹ A ＝ ssup
                                         (Π x ꞉ X , 𝕄-root (A x))
                                         (λ g → Πᴹ (λ x → 𝕄-forest (A x) (g x))))
  QuestionX x = Πᴹ' , eq
   where
    I : (A : X → 𝕄) → ((g : X → 𝕄) → g < A → 𝕄) → 𝕄
    I A rec = ssup
               (Π x ꞉ X , 𝕄-root (A x))
               (λ g → rec (λ x → 𝕄-forest (A x) (g x))
                          (smaller λ y → (g y) , refl))

    Πᴹ' : (X → 𝕄) → 𝕄
    Πᴹ' A = transfinite-recursion
             (<-is-well-founded' x)
             I
             A

    eq : (A : X → 𝕄)
       → Πᴹ' A ＝ ssup
                   (Π x ꞉ X , 𝕄-root (A x))
                 (λ g → Πᴹ' (λ x → 𝕄-forest (A x) (g x)))
    eq A = transfinite-recursion-behaviour fe (<-is-well-founded' x) I A

\end{code}
