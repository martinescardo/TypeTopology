Ian Ray, 23rd July 2024

We define connected types and maps. We then explore relationships, closure
properties and characterizations of interest pertaining to the concept of
connectedness.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.ConnectedTypes
        (fe : Fun-Ext)
       where
                          
open import MLTT.Spartan hiding (_+_)
open import Notation.Order
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropTrunc 
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Truncations fe
open import UF.TruncationLevels
open import UF.TruncatedTypes fe
open import UF.Univalence

\end{code}

We now define the notion of k-connectedness for types and functions with respect
to truncation levels.

TODO: show that connectedness as defined elsewhere in the library is
a special case of k-connectedness. Connectedness typically means set
connectedness, by our convention it will mean 0-connectedness.

\begin{code}

module _ (te : general-truncations-exist) where

 private 
  pt : propositional-truncations-exist
  pt = general-truncations-give-propositional-truncations te

 open general-truncations-exist te
 open propositional-truncations-exist pt
 open import UF.ImageAndSurjection pt

 _is_connected : 𝓤 ̇ → ℕ₋₂ → 𝓤 ̇
 X is k connected = is-contr (∥ X ∥[ k ])

 _is_connected-map : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ₋₂ → 𝓤 ⊔ 𝓥 ̇
 f is k connected-map = each-fiber-of f (λ - → - is k connected)

\end{code}

We characterize 1-connected types as inhabited types and 1-connected maps as
surjections.

\begin{code}

 inhabited-if-−1-connected : {X : 𝓤 ̇}
                            → X is −1 connected → ∥ X ∥
 inhabited-if-−1-connected X-1-conn = −1-trunc-to-prop-trunc pt (center X-1-conn)

 −1-connected-if-inhabited : {X : 𝓤 ̇}
                            → ∥ X ∥ → X is −1 connected
 −1-connected-if-inhabited x-anon =
  pointed-props-are-singletons (prop-trunc-to-−1-trunc pt x-anon) −1-trunc-is-prop

 −1-connected-iff-inhabited : {X : 𝓤 ̇}
                             → X is −1 connected ↔ ∥ X ∥
 −1-connected-iff-inhabited =
  (inhabited-if-−1-connected , −1-connected-if-inhabited)

 map-is-surj-if-−1-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                              → f is −1 connected-map → is-surjection f
 map-is-surj-if-−1-connected m y = inhabited-if-−1-connected (m y)

 map-is-−1-connected-if-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                              → is-surjection f → f is −1 connected-map
 map-is-−1-connected-if-surj f-is-surj y = −1-connected-if-inhabited (f-is-surj y)

 map-is-one-connected-iff-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                               → f is −1 connected-map ↔ is-surjection f
 map-is-one-connected-iff-surj =
  (map-is-surj-if-−1-connected , map-is-−1-connected-if-surj)

\end{code}

We develop some closure conditions pertaining to connectedness. Connectedness
is closed under equivalence as expected, but more importantly connectedness
extends below: more precisely if a type is k connected then it is l connected
for all l ≤ k. We provide a few incarnations of this fact below which may prove
useful. 

\begin{code}

 connectedness-closed-under-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ₋₂}
                                  → X ≃ Y
                                  → Y is k connected
                                  → X is k connected
 connectedness-closed-under-equiv e Y-con =
  equiv-to-singleton (truncation-closed-under-equiv e) Y-con

 contractible-types-are-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                  → is-contr X
                                  → X is k connected
 contractible-types-are-connected {𝓤} {X} {k} (c , C) = ((∣ c ∣[ k ]) , C')
  where
   C' : (s : ∥ X ∥[ k ]) → (∣ c ∣[ k ]) ＝ s
   C' = ∥∥ₙ-ind (truncation-levels-closed-under-Id ∥∥ₙ-is-truncated (∣ c ∣[ k ]))
                (λ x → ap ∣_∣[ k ] (C x))

 connectedness-is-lower-closed : {X : 𝓤 ̇} {k : ℕ₋₂}
                               → X is (succ k) connected
                               → X is k connected
 connectedness-is-lower-closed {𝓤} {X} {k} X-succ-con =
  equiv-to-singleton successive-truncations-equiv 
                     (contractible-types-are-connected X-succ-con)

 connectedness-is-lower-closed-+ : {X : 𝓤 ̇} {l : ℕ₋₂} {k : ℕ}
                                 → X is (l + k) connected
                                 → X is l connected
 connectedness-is-lower-closed-+ {𝓤} {X} {l} {0} X-con = X-con
 connectedness-is-lower-closed-+ {𝓤} {X} {l} {succ k} X-con =
  connectedness-is-lower-closed-+ (connectedness-is-lower-closed X-con)

 connectedness-is-lower-closed' : {X : 𝓤 ̇} {k l : ℕ₋₂}
                                → (l ≤ k)
                                → X is k connected
                                → X is l connected
 connectedness-is-lower-closed' {𝓤} {X} {k} {l} o X-con =
  connectedness-is-lower-closed-+ (transport (λ z → X is z connected) p X-con)
  where
   m : ℕ
   m = subtraction-ℕ₋₂-term l k o
   p = k        ＝⟨ subtraction-ℕ₋₂-identification l k o ⁻¹ ⟩
       l + m   ∎

\end{code}

We characterize connected types in terms of inhabitedness and connectedness of
the identity type at one level below. We will assume univalence only when necessary.

\begin{code}

 inhabited-if-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                        → X is (succ k) connected → ∥ X ∥
 inhabited-if-connected {_} {_} {k} X-conn =
  inhabited-if-−1-connected (connectedness-is-lower-closed' ⋆ X-conn)

 _is-locally_connected : (X : 𝓤 ̇) (k : ℕ₋₂) → 𝓤  ̇
 X is-locally k connected = (x y : X) → (x ＝ y) is k connected

 connected-types-are-locally-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                       → is-univalent 𝓤
                                       → X is (succ k) connected
                                       → X is-locally k connected
 connected-types-are-locally-connected {_} {_} {k} ua X-conn x y =
  equiv-to-singleton (eliminated-trunc-identity-char ua)
   (is-prop-implies-is-prop' (singletons-are-props X-conn)
    ∣ x ∣[ succ k ] ∣ y ∣[ succ k ])

 connected-types-are-inhabited-and-locally-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                                     → is-univalent 𝓤
                                                     → X is (succ k) connected
                                                     → ∥ X ∥
                                                      × X is-locally k connected
 connected-types-are-inhabited-and-locally-connected ua X-conn =
  (inhabited-if-connected X-conn , connected-types-are-locally-connected ua X-conn)

 inhabited-and-locally-connected-types-are-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                                     → is-univalent 𝓤
                                                     → ∥ X ∥
                                                      × X is-locally k connected
                                                     → X is (succ k) connected
 inhabited-and-locally-connected-types-are-connected
  {_} {_} {−2} ua (anon-x , id-conn) =
  pointed-props-are-singletons (prop-trunc-to-−1-trunc pt anon-x) −1-trunc-is-prop
 inhabited-and-locally-connected-types-are-connected
  {_} {_} {succ k} ua (anon-x , id-conn) =
  ∥∥-rec (being-singleton-is-prop fe)
         (λ x → (∣ x ∣[ succ (succ k) ]
          , ∥∥ₙ-ind (λ v → truncation-levels-are-upper-closed
                            (λ p q → ∥∥ₙ-is-truncated ∣ x ∣[ succ (succ k) ] v p q)) 
                    (λ y → forth-trunc-id-char ua (center (id-conn x y)))))
         anon-x

 connected-characterization : {X : 𝓤 ̇} {k : ℕ₋₂}
                            → is-univalent 𝓤
                            → X is (succ k) connected
                            ↔ ∥ X ∥ × X is-locally k connected
 connected-characterization ua =
  (connected-types-are-inhabited-and-locally-connected ua
   , inhabited-and-locally-connected-types-are-connected ua)

 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ₋₂} 
                      → (ua : is-univalent (𝓤 ⊔ 𝓥))
                      → (f : X → Y)
                      → f is (succ k) connected-map
                      → {x x' : X}
                      → (ap f {x} {x'}) is k connected-map
 ap-is-less-connected ua f f-conn {x} {x'} p =
  equiv-to-singleton (truncation-closed-under-equiv (fiber-of-ap-≃ f p))
   (connected-types-are-locally-connected ua (f-conn (f x'))
    (x , p) (x' , refl))

\end{code}
