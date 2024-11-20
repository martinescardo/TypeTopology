Ian Ray, 4th Febuary 2024.

Modifications made by Ian Ray on 14 October 2024.

We develop some results that relate size, truncation and connectedness from
a paper by Dan Christensen (see https://browse.arxiv.org/abs/2109.06670).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.SizeandConnectedness
        (fe : Fun-Ext)
       where
                          
open import MLTT.Spartan hiding (_+_)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.ConnectedTypes fe
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropTrunc
open import UF.SmallnessProperties
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Truncations fe
open import UF.TruncationLevels
open import UF.TruncatedTypes fe
open import UF.Univalence

module _
        (te : general-truncations-exist)
        (ua : Univalence)
        (𝓥 : Universe)
       where

 private
  pt : propositional-truncations-exist
  pt = general-truncations-give-propositional-truncations te

 open import UF.ImageAndSurjection pt

\end{code}

We begin by giving some definitions that Dan uses in his paper. We will use
𝓥 as our point of reference for 'smallness'.

\begin{code}

 _is_locally-small : (X : 𝓤 ̇) → (n : ℕ) → 𝓤 ⊔ (𝓥 ⁺) ̇
 X is zero locally-small = X is 𝓥 small
 X is (succ n) locally-small = (x x' : X) → (x ＝ x') is n locally-small

 locally-small-is-prop : {X : 𝓤 ̇} {n : ℕ}
                       → is-prop (X is n locally-small)
 locally-small-is-prop {_} {X} {zero} = being-small-is-prop ua X 𝓥
 locally-small-is-prop {_} {X} {succ n} =
  Π₂-is-prop fe (λ x y → locally-small-is-prop)

 locally-small-is-upper-closed : {X : 𝓤 ̇} {n : ℕ}
                               → X is n locally-small
                               → X is (succ n) locally-small
 locally-small-is-upper-closed {_} {X} {zero} = small-implies-locally-small X 𝓥
 locally-small-is-upper-closed {_} {X} {succ n} X-loc-small x x' =
  locally-small-is-upper-closed (X-loc-small x x')

\end{code}

Local smallness is closed under sigma and equivalence for each n : ℕ.

TODO: Add other closure properties and maybe move this to size file(?).

\begin{code}

 locally-small-≃-closed : {X : 𝓤 ̇} {Y : 𝓦 ̇} {n : ℕ}
                        → X ≃ Y
                        → X is n locally-small
                        → Y is n locally-small
 locally-small-≃-closed {_} {_} {_} {_} {zero} e X-small =
  smallness-closed-under-≃ X-small e
 locally-small-≃-closed {_} {_} {_} {_} {succ n} e X-loc-small y y' =
  locally-small-≃-closed path-equiv (X-loc-small (⌜ e ⌝⁻¹ y) (⌜ e ⌝⁻¹ y'))
  where
   path-equiv : (⌜ e ⌝⁻¹ y ＝ ⌜ e ⌝⁻¹ y') ≃ (y ＝ y')
   path-equiv = ≃-sym (ap ⌜ e ⌝⁻¹ , ap-is-equiv ⌜ e ⌝⁻¹ (⌜⌝⁻¹-is-equiv e))

 locally-small-Σ-closed : {X : 𝓤 ̇} {Y : X → 𝓦 ̇} {n : ℕ}
                        → X is n locally-small
                        → ((x : X) → (Y x) is n locally-small)
                        → (Σ x ꞉ X , Y x) is n locally-small
 locally-small-Σ-closed {_} {_} {_} {_} {zero} X-small Y-small =
  Σ-is-small X-small Y-small
 locally-small-Σ-closed {_} {_} {_} {Y} {succ n}
  X-loc-small Y-loc-small (x , y) (x' , y') =
  locally-small-≃-closed (≃-sym Σ-＝-≃)
   (locally-small-Σ-closed (X-loc-small x x')
    (λ - → Y-loc-small x' (transport Y - y) y'))

 locally-small-from-small : {X : 𝓤 ̇} {n : ℕ}
                          → X is 𝓥 small
                          → X is n locally-small
 locally-small-from-small {_} {_} {zero} X-small = X-small
 locally-small-from-small {_} {X} {succ n} X-small x x' =
  locally-small-from-small (small-implies-locally-small X 𝓥 X-small x x')

 open general-truncations-exist te

 trunc-loc-small-from-loc-small : {X : 𝓤 ̇} {n : ℕ₋₂}
                                → X is ι (n + 2) locally-small
                                → ∥ X ∥[ n ] is ι (n + 2) locally-small
 trunc-loc-small-from-loc-small {_} {X} {−2} = size-closed-under-truncation
 trunc-loc-small-from-loc-small {_} {X} {succ n} X-loc-small =
  ∥∥ₙ-ind₂ (λ u v → (u ＝ v) is ι (n + 2) locally-small)
           (λ u v → truncation-levels-are-upper-closed' ⋆
                     (is-prop-implies-is-prop' locally-small-is-prop))
           (λ x y → locally-small-≃-closed
                     (eliminated-trunc-identity-char (ua _))
                    (trunc-loc-small-from-loc-small (X-loc-small x y)))

\end{code}

Lemma 2.2. and Lemma 2.5. follow from a result in Egbert Rijke's
"The Join Construction". Unfortunately, these results have yet to be
implemented in the TypeTopology library. We will state the join
construction result below and explicilty assume it when necessary.

TODO: Implement the join construction.

\begin{code}

 open connectedness-results te
 open PropositionalTruncation pt

 Join-Construction-Result : {𝓤 𝓦 : Universe} → (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓦 ⁺) ̇
 Join-Construction-Result {𝓤} {𝓦} = {A : 𝓤 ̇} {X : 𝓦 ̇} {f : A → X}
                                  → A is 𝓥 small
                                  → X is 1 locally-small
                                  → f is −1 connected-map
                                  → X is 𝓥 small

\end{code}

We will now begin proving some of the results of the paper. We will attempt to
avoid any unnecesay use of propositional resizing. Theorem numbers will be
provided for easy reference.

Prop 2.2.

\begin{code}

 Prop-2-2 : {𝓤 𝓦 : Universe} {A : 𝓤 ̇} {X : 𝓦 ̇} {f : A → X} {n : ℕ₋₂}
          → Join-Construction-Result {𝓤} {𝓦}
          → f is n connected-map
          → A is 𝓥 small
          → X is ι (n + 2) locally-small
          → X is 𝓥 small
 Prop-2-2 {_} {_} {_} {_} {_} {−2} j f-con A-small X-small = X-small
 Prop-2-2 {𝓤} {𝓦} {A} {X} {f} {succ n} j f-con A-small X-is-loc-small =
  j A-small
    (locally-small-from-surjection (map-is-surj-if-−1-connected f-−1-con))
    f-−1-con
  where
   f-−1-con : f is −1 connected-map
   f-−1-con = map-connectedness-is-lower-closed ⋆ f-con
   helper : (x x' : X)
          → Σ a ꞉ A , f a ＝ x
          → Σ a ꞉ A , f a ＝ x'
          → (x ＝ x') is 𝓥 small
   helper .(f a) .(f a') (a , refl) (a' , refl) =
    Prop-2-2 j (ap-is-less-connected (ua (𝓤 ⊔ 𝓦)) f f-con)
             (small-implies-locally-small A 𝓥 A-small a a')
             (X-is-loc-small (f a) (f a')) 
   locally-small-from-surjection : is-surjection f
                                 → (x x' : X)
                                 → (x ＝ x') is 𝓥 small
   locally-small-from-surjection f-is-surj x x' =
    ∥∥-rec₂ (being-small-is-prop ua (x ＝ x') 𝓥)
            (helper x x')
            (f-is-surj x)
            (f-is-surj x')
\end{code}

Lemma 2.3.

\begin{code}

 Lemma-2-3 : {X : 𝓤 ̇} {n : ℕ₋₂}
           → Propositional-Resizing
           → X is (n + 1) truncated
           → X is ι (n + 2) locally-small
 Lemma-2-3 {_} {X} {−2} pr X-prop =
  pr X (is-prop'-implies-is-prop X-prop)
 Lemma-2-3 {_} {_} {succ n} pr X-trunc x x' =
  Lemma-2-3 pr (X-trunc x x')

\end{code}

Lemma 2.4.

\begin{code}

 Lemma-2-4 : {X : 𝓤 ̇} {Y : 𝓦 ̇} {f : X → Y} {n : ℕ₋₂}
           → Propositional-Resizing
           → f is (n + 1) truncated-map
           → Y is ι (n + 2) locally-small
           → X is ι (n + 2) locally-small
 Lemma-2-4 {_} {_} {_} {_} {f} {_} pr f-trunc Y-loc-small =
  locally-small-≃-closed (total-fiber-is-domain f)
   (locally-small-Σ-closed Y-loc-small (λ y → Lemma-2-3 pr (f-trunc y)))

\end{code}

Lemma 2.5.

\begin{code}

 Lemma-2-5 : {X : 𝓤 ̇} {Y : 𝓦 ̇} {f : X → Y} {n : ℕ₋₂}
           → Join-Construction-Result {𝓤} {𝓤}
           → Propositional-Resizing
           → f is (n + 1) truncated-map
           → Y is ι (n + 2) locally-small
           → X is (n + 1) connected
           → X is 𝓥 small
 Lemma-2-5 {𝓤} {_} {X} {_} {_} {n} j pr f-trunc Y-loc-small X-conn =
  ∥∥-rec (being-small-is-prop ua X 𝓥)
   X-inhabited-implies-small (center X-−1-conn)
  where
   X-loc-small : X is ι (n + 2) locally-small
   X-loc-small = Lemma-2-4 pr f-trunc Y-loc-small
   X-−1-conn : X is −1 connected
   X-−1-conn = connectedness-is-lower-closed' ⋆ X-conn
   X-point : X → 𝟙 {𝓤} → X
   X-point x ⋆ = x
   X-point-n-conn : (x : X) → (X-point x) is n connected-map
   X-point-n-conn x = basepoint-map-is-less-connected (ua 𝓤) (X-point x) X-conn
   𝟙-is-small : 𝟙 {𝓤} is 𝓥 small
   𝟙-is-small = pr 𝟙 𝟙-is-prop
   X-inhabited-implies-small : X → X is 𝓥 small
   X-inhabited-implies-small x =
    Prop-2-2 j (X-point-n-conn x) 𝟙-is-small X-loc-small

\end{code}

We shall follow Dan's updated result and prove the following in the absence of
propositional resizing.

Theorem 2.6.

\begin{code}

 small-path-space-lemma : {X : 𝓤 ̇} {n : ℕ₋₂}
                        → Join-Construction-Result {𝓤} {𝓤}
                        → X is ι (n + 2) locally-small
                         × ∥ X ∥[ n + 1 ] is 𝓥 small
                        → (Σ y ꞉ ∥ X ∥[ n + 1 ] , Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ y)
                         is 𝓥 small
 small-path-space-lemma {_} {X} {n} j (X-loc-small , trunc-X-small) =
  Σ-is-small trunc-X-small fiber-path-space-small
  where
   trunc-ind-helper : (x' : X)
                    → (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]) is 𝓥 small
   trunc-ind-helper x' = Prop-2-2 j f-con 𝟙-is-small cod-locally-small
    where
     f : 𝟙 {𝓤} → Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]
     f ⋆ = (x' , refl)
     cod-con : (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]) is (n + 1)
                connected
     cod-con = canonical-trunc-map-is-connected ∣ x' ∣[ n + 1 ]
     f-con : f is n connected-map
     f-con = basepoint-map-is-less-connected (ua _) f cod-con
     𝟙-is-small : 𝟙 {𝓤} is 𝓥 small
     𝟙-is-small = (𝟙 {𝓥} , one-𝟙-only)
     cod-locally-small : (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]) is
                          ι (n + 2) locally-small
     cod-locally-small = locally-small-Σ-closed X-loc-small path-locally-small
      where
       path-locally-small : (x : X)
                          → (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ]) is
                           ι (n + 2) locally-small
       path-locally-small x =
        locally-small-≃-closed (eliminated-trunc-identity-char (ua _))
                               path-char-locally-small
         where
          path-char-locally-small : ∥ x ＝ x' ∥[ n ] is ι (n + 2) locally-small
          path-char-locally-small =
           trunc-loc-small-from-loc-small (locally-small-is-upper-closed
            X-loc-small x x')
   fiber-path-space-small : (y : ∥ X ∥[ n + 1 ])
                          → (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ y) is 𝓥 small
   fiber-path-space-small =
    ∥∥ₙ-ind (λ - → is-trunc-from-is-prop pt
                    (being-small-is-prop ua (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ -) 𝓥))
            trunc-ind-helper

 small-from-locally-and-trunc-small : {X : 𝓤 ̇} {n : ℕ₋₂}
                                    → Join-Construction-Result {𝓤} {𝓤}
                                    → X is ι (n + 2) locally-small
                                     × ∥ X ∥[ n + 1 ] is 𝓥 small
                                    → X is 𝓥 small
 small-from-locally-and-trunc-small {_} {X} {n} j small-hyp =
  smallness-closed-under-≃' (small-path-space-lemma j small-hyp)
                            equiv-trunc-path-space

 Theorem-2-6 : {X : 𝓤 ̇} {n : ℕ₋₂}
             → Join-Construction-Result {𝓤} {𝓤}
             → X is 𝓥 small
             ↔ X is ι (n + 2) locally-small × ∥ X ∥[ n + 1 ] is 𝓥 small 
 Theorem-2-6 {_} {X} {n} j =
  (foreward , small-from-locally-and-trunc-small j)
  where
   foreward : X is 𝓥 small
            → X is ι (n + 2) locally-small × ∥ X ∥[ n + 1 ] is 𝓥 small
   foreward X-small =
    (locally-small-from-small X-small , size-closed-under-truncation X-small)

\end{code}

Corollary 2.7.

\begin{code}

 Corollary-2-7 : {X : 𝓤 ̇} {Y : 𝓦 ̇} {f : X → Y} {n : ℕ₋₂}
               → Join-Construction-Result {𝓤} {𝓤}
               → Propositional-Resizing
               → f is (n + 1) truncated-map
               → Y is ι (n + 2) locally-small
               → ∥ X ∥[ n + 1 ] is 𝓥 small
               → X is 𝓥 small
 Corollary-2-7 j pr f-trunc Y-loc-small trunc-X-small =
  small-from-locally-and-trunc-small j
   (Lemma-2-4 pr f-trunc Y-loc-small , trunc-X-small)

\end{code}

TODO: Proposition 2.8. requires the concept of Homotopy Groups.
