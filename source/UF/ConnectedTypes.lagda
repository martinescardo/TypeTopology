Ian Ray, 23rd July 2024

We define connected types and maps (recall our convention that H-levels start
at 0). We then explore relationships, closure properties and characterizations
of interest pertaining to the concept of connectedness.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.ConnectedTypes
        (fe : Fun-Ext)
       where
                          
open import MLTT.Spartan
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.H-Levels fe

open import UF.PropTrunc 
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Truncations fe
open import UF.Univalence

\end{code}

We now define the notion of k-connectedness for types and functions with respect
to H-levels. TODO: show that connectedness as defined elsewhere is a
special case of k-connectedness. Connectedness typically means set connectedness.
In terms of our H-level convetion it will mean 2-connectedness.

\begin{code}

module connectedness (te : H-level-truncations-exist) where

 private 
  pt : propositional-truncations-exist
  pt = H-level-truncations-give-propositional-truncations te

 open H-level-truncations-exist te
 open propositional-truncations-exist pt
 open import UF.ImageAndSurjection pt

 _is_connected : 𝓤 ̇ → ℕ → 𝓤 ̇
 X is k connected = is-contr (∥ X ∥[ k ])

 _is_connected-map : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ → 𝓤 ⊔ 𝓥 ̇
 f is k connected-map = each-fiber-of f (λ - → - is k connected)

\end{code}

We characterize 1-connected types as inhabited types and 1-connected maps as
surjections.

\begin{code}

 inhabited-if-one-connected : {X : 𝓤 ̇}
                            → X is 1 connected → ∥ X ∥
 inhabited-if-one-connected X-1-conn = one-trunc-to-prop-trunc pt (center X-1-conn)

 one-connected-if-inhabited : {X : 𝓤 ̇}
                            → ∥ X ∥ → X is 1 connected
 one-connected-if-inhabited x-anon =
  pointed-props-are-singletons (prop-trunc-to-one-trunc pt x-anon) one-trunc-is-prop

 one-connected-iff-inhabited : {X : 𝓤 ̇}
                             → X is 1 connected ↔ ∥ X ∥
 one-connected-iff-inhabited =
  (inhabited-if-one-connected , one-connected-if-inhabited)

 map-is-surj-if-one-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                              → f is 1 connected-map → is-surjection f
 map-is-surj-if-one-connected f-1-con y = inhabited-if-one-connected (f-1-con y)

 map-is-one-connected-if-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                              → is-surjection f → f is 1 connected-map
 map-is-one-connected-if-surj f-is-surj y = one-connected-if-inhabited (f-is-surj y)

 map-is-one-connected-iff-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                               → f is 1 connected-map ↔ is-surjection f
 map-is-one-connected-iff-surj =
  (map-is-surj-if-one-connected , map-is-one-connected-if-surj)

\end{code}

We develop some closure conditions pertaining to connectedness. Connectedness
is closed under equivalence as expected, but more importantly connectedness
extends below: more precisely if a type is k connected then it is l connected
for all l ≤ k. We provide a few incarnations of this fact below which may prove
useful. 

\begin{code}

 connectedness-closed-under-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ}
                                  → X ≃ Y
                                  → Y is k connected
                                  → X is k connected
 connectedness-closed-under-equiv e Y-con =
  equiv-to-singleton (truncation-closed-under-equiv e) Y-con

 contractible-types-are-connected : {X : 𝓤 ̇} {k : ℕ}
                                  → is-contr X
                                  → X is k connected
 contractible-types-are-connected {𝓤} {X} {k} (c , C) = ((∣ c ∣[ k ]) , C')
  where
   C' : (s : ∥ X ∥[ k ]) → (∣ c ∣[ k ]) ＝ s
   C' = ∥∥ₙ-ind (hlevels-are-closed-under-id ∥∥ₙ-hlevel (∣ c ∣[ k ]))
                (λ x → ap ∣_∣[ k ] (C x))

 connectedness-is-lower-closed : {X : 𝓤 ̇} {k : ℕ}
                               → X is (succ k) connected
                               → X is k connected
 connectedness-is-lower-closed {𝓤} {X} {k} X-succ-con =
  equiv-to-singleton successive-truncations-equiv 
                      (contractible-types-are-connected X-succ-con)

 connectedness-is-lower-closed-+ : {X : 𝓤 ̇} {k l : ℕ}
                                 → X is (l +' k) connected
                                 → X is l connected
 connectedness-is-lower-closed-+ {𝓤} {X} {0} {l} X-con = X-con
 connectedness-is-lower-closed-+ {𝓤} {X} {succ k} {l} X-con =
  connectedness-is-lower-closed-+ (connectedness-is-lower-closed X-con)

 connectedness-is-lower-closed' : {X : 𝓤 ̇} {k l : ℕ}
                                → (l ≤ℕ k)
                                → X is k connected
                                → X is l connected
 connectedness-is-lower-closed' {𝓤} {X} {k} {l} o X-con =
  connectedness-is-lower-closed-+ (transport (λ z → X is z connected) p X-con)
  where
   m : ℕ
   m = pr₁ (subtraction l k o)
   p = k        ＝⟨ pr₂ (subtraction l k o) ⁻¹ ⟩
       m +' l   ＝⟨ addition-commutativity m l ⟩
       l +' m   ∎

\end{code}

We can characterize connected types in terms of inhabitedness and connectedness
of the identity type at the level below. We will assume univalence when necessary.

\begin{code}

 inhabited-if-connected : {X : 𝓤 ̇} {k : ℕ}
                        → X is (succ k) connected → ∥ X ∥
 inhabited-if-connected {_} {_} {k} X-conn =
  inhabited-if-one-connected (connectedness-is-lower-closed' ⋆ X-conn)

 _is-locally_connected : (X : 𝓤 ̇) (k : ℕ) → 𝓤  ̇
 X is-locally k connected = (x y : X) → (x ＝ y) is k connected

 connected-types-are-locally-connected : {X : 𝓤 ̇} {k : ℕ}
                                       → is-univalent 𝓤
                                       → X is (succ k) connected
                                       → X is-locally k connected
 connected-types-are-locally-connected {_} {_} {k} ua X-conn x y =
  equiv-to-singleton (eliminated-trunc-identity-char ua)
   (is-prop-implies-is-prop' (singletons-are-props X-conn)
    ∣ x ∣[ succ k ] ∣ y ∣[ succ k ])

 connected-types-are-inhabited-and-locally-connected : {X : 𝓤 ̇} {k : ℕ}
                                                     → is-univalent 𝓤
                                                     → X is (succ k) connected
                                                     → ∥ X ∥
                                                      × X is-locally k connected
 connected-types-are-inhabited-and-locally-connected ua X-conn =
  (inhabited-if-connected X-conn , connected-types-are-locally-connected ua X-conn)

 inhabited-and-locally-connected-types-are-connected : {X : 𝓤 ̇} {k : ℕ}
                                                     → is-univalent 𝓤
                                                     → ∥ X ∥
                                                      × X is-locally k connected
                                                     → X is (succ k) connected
 inhabited-and-locally-connected-types-are-connected
  {_} {_} {0} ua (anon-x , id-conn) =
  pointed-props-are-singletons (prop-trunc-to-one-trunc pt anon-x) one-trunc-is-prop
 inhabited-and-locally-connected-types-are-connected
  {_} {_} {succ k} ua (anon-x , id-conn) =
  ∥∥-rec (being-singleton-is-prop fe)
         (λ x → (∣ x ∣[ succ (succ k) ]
          , ∥∥ₙ-ind (λ v → hlevels-are-upper-closed
                            (λ p q → ∥∥ₙ-hlevel ∣ x ∣[ succ (succ k) ] v p q)) 
                    (λ y → forth-trunc-id-char ua (center (id-conn x y)))))
         anon-x

 connected-characterization : {X : 𝓤 ̇} {k : ℕ}
                            → is-univalent 𝓤
                            → X is (succ k) connected
                            ↔ ∥ X ∥ × X is-locally k connected
 connected-characterization ua =
  (connected-types-are-inhabited-and-locally-connected ua
   , inhabited-and-locally-connected-types-are-connected ua)

 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ} 
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
