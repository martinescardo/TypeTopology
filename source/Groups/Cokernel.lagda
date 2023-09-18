--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

October 11, 2021

Revision started April 2, 2022
--------------------------------------------------------------------------------

If $f \colon X → Y$ is a group homomorphism, we define an equivalence
relation on the underlying type of $Y$ by the left (and right)
multiplications by the image of $f$.

If the image is normal in $Y$ (which is defined in
\texttt{Groups.homomorphisms}) then the quotient is a group that can
(ought to) be interpreted as the cokernel of $f$.

TODO: adapt to use (small) quotients defined in UF-Quotient

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Quotient.Type
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Embeddings
open import UF.FunExt
open import UF.PropTrunc

module Groups.Cokernel
        (pt  : propositional-truncations-exist)
        (fe  : Fun-Ext)
        (pe : Prop-Ext)
        (sq : set-quotients-exist)
       where

open general-set-quotients-exist sq

open import Groups.Homomorphisms
open import Groups.Image
open import Groups.Kernel
open import Groups.Quotient pt fe sq
open import Groups.Triv
open import Groups.Type renaming (_≅_ to _≣_)
open import Quotient.Effectivity
open import UF.ImageAndSurjection pt

\end{code}

Standard equivalence relation by "normality."

\begin{code}

module _ (X : Group 𝓤) (Y : Group 𝓥)
         (f : ⟨ X ⟩ → ⟨ Y ⟩) (isf : is-hom X Y f) where

  open PropositionalTruncation pt

  -- Left cosets
  _≈_ : ⟨ Y ⟩ → ⟨ Y ⟩ → _
  y₁ ≈ y₂ = ∃ λ x → (y₂ ＝ y₁ ·⟨ Y ⟩ (f x))

  ≈p : is-prop-valued _≈_ -- pt fe pe _≈_
  ≈p = λ y₁ y₂ → ∥∥-is-prop

  ≈r : reflexive _≈_
  ≈r y = ∣ (unit X) , (q ⁻¹) ∣
    where
      p : f (unit X) ＝ unit Y
      p = homs-preserve-unit X Y f isf

      q : multiplication Y y (f (unit X)) ＝ y
      q = ap (λ v → y ·⟨ Y ⟩ v) p ∙ (unit-right Y y)

  ≈s : symmetric _≈_
  ≈s y₁ y₂ p = do
    x , u ← p
    ∣ ((inv X x) , q x u) ∣
    where
      q : (x : ⟨ X ⟩) (u : y₂ ＝ multiplication Y y₁ (f x))
        → y₁ ＝ multiplication Y y₂ (f (inv X x))
      q x u = y₁                                  ＝⟨ (unit-right Y y₁) ⁻¹ ⟩
              y₁ ·⟨ Y ⟩ unit Y                     ＝⟨ ap (λ v → y₁ ·⟨ Y ⟩ v) (inv-right Y (f x)) ⁻¹ ⟩
              y₁ ·⟨ Y ⟩ ( (f x) ·⟨ Y ⟩ inv Y (f x)) ＝⟨ (assoc Y _ _ _) ⁻¹ ⟩
              (y₁ ·⟨ Y ⟩ (f x)) ·⟨ Y ⟩ inv Y (f x)  ＝⟨ ap (λ v → v ·⟨ Y ⟩ (inv Y (f x)) ) u ⁻¹ ⟩
              y₂ ·⟨ Y ⟩ inv Y (f x)                ＝⟨ ap (λ v → y₂ ·⟨ Y ⟩ v) (homs-preserve-invs X Y f isf x) ⁻¹ ⟩
              y₂ ·⟨ Y ⟩ f (inv X x) ∎

  ≈t : transitive _≈_
  ≈t y₁ y₂ y₃ p₁ p₂ = do
     x₁ , u₁ ← p₁
     x₂ , u₂ ← p₂
     ∣ ((x₁ ·⟨ X ⟩ x₂) , q x₁ u₁ x₂ u₂) ∣
     where
       q : (x₁ : ⟨ X ⟩) (u₁ : y₂ ＝ y₁ ·⟨ Y ⟩ (f x₁))
           (x₂ : ⟨ X ⟩) (u₂ : y₃ ＝ y₂ ·⟨ Y ⟩ (f x₂)) →
           y₃ ＝ y₁ ·⟨ Y ⟩ f (x₁ ·⟨ X ⟩ x₂)
       q x₁ u₁ x₂ u₂ = y₃                             ＝⟨ u₂ ⟩
                       y₂ ·⟨ Y ⟩ (f x₂)                ＝⟨ ap (λ v → v ·⟨ Y ⟩ (f x₂)) u₁ ⟩
                       (y₁ ·⟨ Y ⟩ f (x₁)) ·⟨ Y ⟩ (f x₂) ＝⟨ assoc Y _ _ _ ⟩
                       y₁ ·⟨ Y ⟩ (f (x₁) ·⟨ Y ⟩ (f x₂)) ＝⟨ ap (λ v → y₁ ·⟨ Y ⟩ v) (isf {x₁} {x₂}) ⁻¹ ⟩
                       y₁ ·⟨ Y ⟩ f (x₁ ·⟨ X ⟩ x₂) ∎

\end{code}

We define a second equivalence relation using right cosets.

\begin{code}

  -- Right cosets
  _≈'_ : ⟨ Y ⟩ → ⟨ Y ⟩ → _
  y₁ ≈' y₂ = ∃ λ x → (y₂ ＝ (f x) ·⟨ Y ⟩ y₁)

  ≈'p : is-prop-valued _≈'_ -- pt fe pe _≈'_
  ≈'p = λ y₁ y₂ → ∥∥-is-prop

  ≈'r : reflexive _≈'_
  ≈'r y = ∣ (unit X) , (q ⁻¹) ∣
    where
      p : f (unit X) ＝ unit Y
      p = homs-preserve-unit X Y f isf

      q : (f (unit X)) ·⟨ Y ⟩ y ＝ y
      q = ap (λ v → v ·⟨ Y ⟩ y) p ∙ (unit-left Y y)

  ≈'s : symmetric _≈'_
  ≈'s y₁ y₂ p = do
    x , u ← p
    ∣ ((inv X x) , q x u) ∣
    where
      q : (x : ⟨ X ⟩) (u : y₂ ＝ (f x) ·⟨ Y ⟩ y₁) →
          y₁ ＝ (f (inv X x)) ·⟨ Y ⟩ y₂
      q x u  = y₁                                 ＝⟨ (unit-left Y y₁) ⁻¹ ⟩
               unit Y ·⟨ Y ⟩ y₁                    ＝⟨ ap (λ v → v ·⟨ Y ⟩ y₁) (inv-left Y (f x)) ⁻¹ ⟩
               (inv Y (f x) ·⟨ Y ⟩ (f x)) ·⟨ Y ⟩ y₁ ＝⟨ assoc Y _ _ _ ⟩
               inv Y (f x) ·⟨ Y ⟩ ((f x) ·⟨ Y ⟩ y₁) ＝⟨ ap (λ v → (inv Y (f x)) ·⟨ Y ⟩ v) u ⁻¹  ⟩
               inv Y (f x) ·⟨ Y ⟩ y₂               ＝⟨ ap (λ v → v ·⟨ Y ⟩ y₂) (homs-preserve-invs X Y f isf x) ⁻¹ ⟩
               (f (inv X x)) ·⟨ Y ⟩ y₂ ∎

  ≈'t : transitive _≈'_
  ≈'t y₁ y₂ y₃ p₁ p₂ = do
     x₁ , u₁ ← p₁
     x₂ , u₂ ← p₂
     ∣ ((x₂ ·⟨ X ⟩ x₁) , q x₁ u₁ x₂ u₂) ∣
     where
       q : (x₁ : ⟨ X ⟩) (u₁ : y₂ ＝ (f x₁) ·⟨ Y ⟩ y₁)
         → (x₂ : ⟨ X ⟩) (u₂ : y₃ ＝ (f x₂) ·⟨ Y ⟩ y₂)
         → y₃ ＝ f (x₂ ·⟨ X ⟩ x₁) ·⟨ Y ⟩ y₁
       q x₁ u₁ x₂ u₂ = y₃                             ＝⟨ u₂ ⟩
                       (f x₂) ·⟨ Y ⟩ y₂                ＝⟨ ap (λ v → (f x₂) ·⟨ Y ⟩ v) u₁ ⟩
                       (f x₂) ·⟨ Y ⟩ ((f x₁) ·⟨ Y ⟩ y₁) ＝⟨ (assoc Y _ _ _) ⁻¹ ⟩
                       ((f x₂) ·⟨ Y ⟩ (f x₁)) ·⟨ Y ⟩ y₁ ＝⟨ ap (λ v → v ·⟨ Y ⟩ y₁) (isf {x₂} {x₁}) ⁻¹ ⟩
                       f (x₂ ·⟨ X ⟩ x₁) ·⟨ Y ⟩ y₁ ∎

\end{code}

The relations _≈_ and _≈'_ are not equal, in general. One of the
possible ways to define "normal" is to assume that they are (see
P. Aluffi, "Algebra—Chapter 0").  The two conditions are in fact
equivalent.


\begin{code}

  ≈-implies-≈' : _
  ≈-implies-≈' = ∀ {y y'} → (y ≈ y' → y ≈' y')

  ≈'-implies-≈ : _
  ≈'-implies-≈ = ∀ {y y'} → (y ≈' y' → y ≈ y')

  ≈-is-same-as-≈' : _
  ≈-is-same-as-≈' = ≈-implies-≈' × ≈'-implies-≈

  ≈-is-same-as-≈'-gives-normal-image : ≈-is-same-as-≈' → (has-normal-image X Y f isf pt)
  ≈-is-same-as-≈'-gives-normal-image φ z (y , u) = do
                               x  , p  ← u
                               x₁ , p₁ ← pr₁ φ {z} {z ·⟨ Y ⟩ (f x)} ∣ (x , refl) ∣
                               let
                                 q = z ·⟨ Y ⟩ y ＝⟨ ap (λ v → z ·⟨ Y ⟩ v) p ⁻¹ ⟩
                                     z ·⟨ Y ⟩ (f x)  ＝⟨ p₁ ⟩
                                     (f x₁) ·⟨ Y ⟩ z ∎
                                 r = f x₁ ＝⟨ (unit-right Y (f x₁)) ⁻¹ ⟩
                                     f x₁ ·⟨ Y ⟩ (unit Y) ＝⟨ ap (λ v → (f x₁) ·⟨ Y ⟩ v) (inv-right Y z) ⁻¹ ⟩
                                     f x₁ ·⟨ Y ⟩ (z ·⟨ Y ⟩ (inv Y z)) ＝⟨ (assoc Y _ _ _) ⁻¹  ⟩
                                     (f x₁ ·⟨ Y ⟩ z) ·⟨ Y ⟩ (inv Y z) ＝⟨ (ap (λ v → v ·⟨ Y ⟩ (inv Y z)) q ⁻¹) ⟩
                                     (z ·⟨ Y ⟩ y) ·⟨ Y ⟩ (inv Y z) ∎
                                 in
                                 ∣ (x₁ , r) ∣

  has-normal-image-gives-≈-is-same-as-≈' : (has-normal-image X Y f isf pt) → ≈-is-same-as-≈'
  pr₁ (has-normal-image-gives-≈-is-same-as-≈' ni) {y} {y'} r = do
                  x , p ← r
                  x' , p' ← ni y (corestriction f x)
                  let
                    q = y ·⟨ Y ⟩ (f x)                           ＝⟨ (unit-right Y _) ⁻¹ ⟩
                        (y ·⟨ Y ⟩ (f x)) ·⟨ Y ⟩ (unit Y)          ＝⟨ ap (λ v → (y ·⟨ Y ⟩ (f x)) ·⟨ Y ⟩ v) (inv-left Y _ ⁻¹) ⟩
                        (y ·⟨ Y ⟩ (f x)) ·⟨ Y ⟩ (inv Y y ·⟨ Y ⟩ y) ＝⟨ assoc Y _ _ _ ⁻¹ ⟩
                        ((y ·⟨ Y ⟩ (f x)) ·⟨ Y ⟩ inv Y y) ·⟨ Y ⟩ y ＝⟨ ap (λ v → multiplication Y v y) (p' ⁻¹) ⟩
                        (f x') ·⟨ Y ⟩ y ∎
                    in
                    ∣ (x' , (p ∙ q)) ∣
  pr₂ (has-normal-image-gives-≈-is-same-as-≈' ni) {y} {y'} r' = do
                  x' , p' ← r'
                  x , p ← ni (inv Y y) (corestriction f x')
                  let
                    ii : y ＝ inv Y (inv Y y)
                    ii = one-left-inv Y (inv Y y) y (inv-right Y y)
                    q' = (f x') ·⟨ Y ⟩ y                            ＝⟨  unit-left Y _ ⁻¹ ⟩
                         (unit Y) ·⟨ Y ⟩ ((f x') ·⟨ Y ⟩ y)           ＝⟨ ap (λ v → v ·⟨ Y ⟩ ((f x') ·⟨ Y ⟩ y)) (inv-right Y _ ⁻¹) ⟩
                         (y ·⟨ Y ⟩ inv Y y) ·⟨ Y ⟩ ((f x') ·⟨ Y ⟩ y)  ＝⟨ assoc Y _ _ _ ⟩
                         y ·⟨ Y ⟩ (inv Y y ·⟨ Y ⟩ ((f x') ·⟨ Y ⟩ y))  ＝⟨ ap (λ v → y ·⟨ Y ⟩ (inv Y y ·⟨ Y ⟩ ((f x') ·⟨ Y ⟩ v))) ii ⟩
                         y ·⟨ Y ⟩ (inv Y y ·⟨ Y ⟩ ((f x') ·⟨ Y ⟩ (inv Y (inv Y y))))  ＝⟨ ap (λ v → y ·⟨ Y ⟩ v) ( assoc Y _ _ _ ⁻¹) ⟩
                         y ·⟨ Y ⟩ ((inv Y y ·⟨ Y ⟩ (f x')) ·⟨ Y ⟩ (inv Y (inv Y y)))  ＝⟨ ap ((λ v → y ·⟨ Y ⟩ v)) (p ⁻¹) ⟩
                         y ·⟨ Y ⟩ (f x) ∎
                     in
                    ∣ (x , (p' ∙ q' )) ∣
\end{code}

The relations _≈_ and _≈'_ are the same if and only if they are both
left and right-invariant, in the sense specified in Groups.quotient.

\begin{code}


  ≋ ≋' : EqRel ⟨ Y ⟩
  ≋    = _≈_ , ≈p , ≈r , (≈s , ≈t)
  ≋'   = _≈'_ , ≈'p , ≈'r , (≈'s , ≈'t)

  ≈-linv : ≈left-invariant Y ≋
  ≈-linv = λ y y' a r → do
                         x , p ← r
                         let
                           q = a ·⟨ Y ⟩ y'              ＝⟨ ap (λ v → a ·⟨ Y ⟩ v) p ⟩
                               a ·⟨ Y ⟩ (y ·⟨ Y ⟩ (f x)) ＝⟨  assoc Y _ _ _ ⁻¹ ⟩
                               (a ·⟨ Y ⟩ y) ·⟨ Y ⟩ (f x) ∎
                           in ∣ (x , q) ∣

  ≈'-rinv : ≈right-invariant Y ≋'
  ≈'-rinv = λ y y' a r →  do
                          x , p ← r
                          let
                            q = y' ·⟨ Y ⟩ a                ＝⟨ ap (λ v → v ·⟨ Y ⟩ a) p ⟩
                                ((f x) ·⟨ Y ⟩ y) ·⟨ Y ⟩ a   ＝⟨ assoc Y _ _ _ ⟩
                                (f x) ·⟨ Y ⟩  (y ·⟨ Y ⟩ a) ∎
                            in ∣ (x , q) ∣

  ≈-is-same-as-≈'-gives-invariance≈ : ≈-is-same-as-≈' → (≈left-invariant Y ≋) × (≈right-invariant Y ≋)
  pr₁ (≈-is-same-as-≈'-gives-invariance≈ Φ) = ≈-linv
  pr₂ (≈-is-same-as-≈'-gives-invariance≈ Φ) = λ y y' a r → do
                                           x , p ← (pr₁ Φ) {y} {y'} r
                                           let
                                             q = y' ·⟨ Y ⟩ a               ＝⟨ ap (λ v → v ·⟨ Y ⟩ a) p ⟩
                                                ((f x) ·⟨ Y ⟩ y) ·⟨ Y ⟩ a   ＝⟨ assoc Y _ _ _ ⟩
                                                (f x) ·⟨ Y ⟩  (y ·⟨ Y ⟩ a) ∎
                                             in (pr₂ Φ) {y ·⟨ Y ⟩ a} {y' ·⟨ Y ⟩ a} ( ∣ (x , q) ∣ )

  ≈-is-same-as-≈'-gives-invariance≈' : ≈-is-same-as-≈' → (≈left-invariant Y ≋') × (≈right-invariant Y ≋')
  pr₁ (≈-is-same-as-≈'-gives-invariance≈' Φ) = λ y y' a r  → do
                                          x , p ← (pr₂ Φ) {y} {y'} r
                                          let
                                           q = a ·⟨ Y ⟩ y'              ＝⟨ ap (λ v → a ·⟨ Y ⟩ v) p ⟩
                                               a ·⟨ Y ⟩ (y ·⟨ Y ⟩ (f x)) ＝⟨  assoc Y _ _ _ ⁻¹ ⟩
                                               (a ·⟨ Y ⟩ y) ·⟨ Y ⟩ (f x) ∎
                                           in (pr₁ Φ) {a ·⟨ Y ⟩ y} {a ·⟨ Y ⟩ y'} ( ∣ (x , q) ∣ )
  pr₂ (≈-is-same-as-≈'-gives-invariance≈' Φ) = ≈'-rinv

\end{code}

We also prove that being left and right invariant, for \emph{both}
relations ≈ and ≈', implies the two relations ≈ and ≈' are the same.

As there is a certain cross-symmetry, we prove this in a slightly
roundabout way. Note that, as shown above, ≈ (resp. ≈') is
automatically left (resp. right) invariant.

\begin{code}

  ≈-rinv-gives-≈-implies-≈' : ≈right-invariant Y ≋ → ≈-implies-≈'
  ≈-rinv-gives-≈-implies-≈' ≈ri {y} {y'} = λ r → do
                                         x , p ← ≈ri y y' (inv Y y) r
                                         let
                                           q = y' ·⟨ Y ⟩ (inv Y y)              ＝⟨ p ⟩
                                               (y ·⟨ Y ⟩ (inv Y y)) ·⟨ Y ⟩ (f x) ＝⟨ ap (λ v → v ·⟨ Y ⟩ (f x)) (inv-right Y y) ⟩
                                               (unit Y) ·⟨ Y ⟩ (f x)            ＝⟨ unit-left Y (f x) ⟩
                                               f x ∎
                                           q₁ = y'                         ＝⟨ unit-right Y y' ⁻¹ ⟩
                                                y' ·⟨ Y ⟩ (unit Y)          ＝⟨ ap (λ v → y' ·⟨ Y ⟩ v) (inv-left Y y ⁻¹) ⟩
                                                y' ·⟨ Y ⟩ (inv Y y ·⟨ Y ⟩ y) ＝⟨ assoc Y _ _ _ ⁻¹ ⟩
                                                (y' ·⟨ Y ⟩ inv Y y) ·⟨ Y ⟩ y ＝⟨ ap (λ v → v ·⟨ Y ⟩ y) q ⟩
                                                (f x) ·⟨ Y ⟩ y ∎
                                           in ∣ (x , q₁) ∣

  ≈'-linv-gives-≈'-implies-≈ : ≈left-invariant Y ≋' → ≈'-implies-≈
  ≈'-linv-gives-≈'-implies-≈ ≈'li {y} {y'} = λ r' → do
                                           x , p ← ≈'li y y' (inv Y y) r'
                                           let
                                             q = (inv Y y) ·⟨ Y ⟩ y'              ＝⟨ p ⟩
                                                 (f x) ·⟨ Y ⟩ ((inv Y y) ·⟨ Y ⟩ y) ＝⟨ ap (λ v → (f x) ·⟨ Y ⟩ v) (inv-left Y y) ⟩
                                                 (f x) ·⟨ Y ⟩ (unit Y)            ＝⟨ unit-right Y (f x) ⟩
                                                 f x ∎
                                             q₁ = y'                         ＝⟨ unit-left Y y' ⁻¹ ⟩
                                                  (unit Y) ·⟨ Y ⟩ y'          ＝⟨ ap (λ v → v ·⟨ Y ⟩ y') (inv-right Y y ⁻¹) ⟩
                                                  (y ·⟨ Y ⟩ inv Y y) ·⟨ Y ⟩ y' ＝⟨ assoc Y _ _ _ ⟩
                                                  y ·⟨ Y ⟩ (inv Y y ·⟨ Y ⟩ y') ＝⟨ ap (λ v → y ·⟨ Y ⟩ v) q ⟩
                                                  y ·⟨ Y ⟩ (f x) ∎
                                             in ∣ (x , q₁) ∣

\end{code}

Finally, the cokernel of f : X → Y is simply a specialization of the
group quotient for an invariant equivalence relation.

\begin{code}

  module cokernel (normf : has-normal-image X Y f isf pt) where

    ≈lrinv : ≈left-invariant Y ≋ × ≈right-invariant Y ≋
    ≈lrinv = ≈-is-same-as-≈'-gives-invariance≈ ( has-normal-image-gives-≈-is-same-as-≈' normf)

    open GroupQuotient Y ≋ (pr₁ ≈lrinv) (pr₂ ≈lrinv)

    cokernel-gr : Group _
    cokernel-gr = quotient-gr

\end{code}

Stating the obvious, f : X → Y has trivial cokernel if the latter is
isomorphic via the terminal morphism to the trivial group.

Then having a trivial cokernel is equivalent to f : X → Y being
surjective.

\begin{code}
    has-triv-coker : 𝓤 ⊔ (𝓥 ⁺) ̇
    has-triv-coker = is-iso (cokernel-gr) (triv {𝓤 ⊔ 𝓥 ⁺}) (triv-terminal cokernel-gr)

    triv-coker-implies-surj-hom : has-triv-coker → is-surjective-hom X Y f isf pt
    triv-coker-implies-surj-hom i y = do
                                 x , p ← lemma1 y
                                 let
                                   q = y                 ＝⟨ p ⟩
                                       e⟨ Y ⟩ ·⟨ Y ⟩ (f x) ＝⟨ unit-left Y _ ⟩
                                       f x               ∎
                                   in ∣ (x , (q ⁻¹)) ∣
      where
        Y≈ : _
        Y≈ = ⟨ cokernel-gr ⟩

        π≈ : _
        π≈ = η/ ≋

        e≈ : Y≈
        e≈ = unit (cokernel-gr)

        u : Y≈ → ⟨ triv {𝓤 ⊔ 𝓥 ⁺} ⟩
        u = triv-terminal cokernel-gr

        is-equiv-u : _
        is-equiv-u = pr₁ i

        is-hom-u : _
        is-hom-u = pr₂ i

        v : ⟨ triv {𝓤 ⊔ 𝓥 ⁺} ⟩ → Y≈
        v = inverse u is-equiv-u

        lemma3 : (y≈ : Y≈) → y≈ ＝ e≈
        lemma3 y≈ = y≈         ＝⟨ (inverses-are-retractions u is-equiv-u y≈) ⁻¹ ⟩
                    v (u (y≈)) ＝⟨ ap v refl ⟩
                    v (⋆)      ＝⟨ homs-preserve-unit (triv {𝓤 ⊔ 𝓥 ⁺}) cokernel-gr v (inverses-are-homs cokernel-gr (triv {𝓤 ⊔ 𝓥 ⁺}) u is-equiv-u refl) ⟩
                    e≈ ∎

        lemma2 : (y : ⟨ Y ⟩) → π≈ (unit Y) ＝ π≈ y
        lemma2 y = π≈ (unit Y) ＝⟨ refl ⟩
                   e≈          ＝⟨ (lemma3 (π≈ y)) ⁻¹ ⟩
                   π≈ y        ∎

        lemma1 : (y : ⟨ Y ⟩) → e⟨ Y ⟩ ≈ y
        lemma1 y = effectivity fe pe sq ≋ (lemma2 y)

\end{code}
