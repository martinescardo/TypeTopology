Ian Ray, 07/23/2024

We will define connected types and maps (recall our convetion for H-levels starts
at 0). We then explore relationships, closure properties and characterizations
of interest pertaining to the concept of connectedness.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.IdentitySystems
open import UF.PropTrunc 
open import UF.Retracts
open import UF.Sets
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence
open import UF.UA-FunExt
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order

module UF.ConnectedTypes (fe : Fun-Ext)
                         (pt : propositional-truncations-exist)
                          where

open import UF.ImageAndSurjection pt
open import UF.H-Levels fe  
open import UF.Truncations fe pt

\end{code}

We now define the notion of k-connectedness for types and functions with respect
to H-levels. TODO: show that connectedness as defined elsewhere is a
special case of k-connectedness. Connectedness typically means set connectedness.
In terms of our Hlevel convetion it will mean 2-connectedness.

\begin{code}

module k-connectedness
        (te : H-level-truncations-exist)
       where

 open H-level-truncations-exist te

 _is_connected : 𝓤 ̇ → ℕ → 𝓤 ̇
 X is k connected = is-contr (∥ X ∥[ k ])

 map_is_connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ → 𝓤 ⊔ 𝓥 ̇
 map f is k connected = (y : codomain f) → (fiber f y) is k connected

\end{code}

We now characterize 1-connected types as inhabited types and 1-connected maps
as surjections.

\begin{code}

 open propositional-truncations-exist pt

 one-connected-is-inhabited : {X : 𝓤 ̇}
                            → X is 1 connected → ∥ X ∥
 one-connected-is-inhabited X-1-conn = one-trunc-to-prop-trunc (center X-1-conn)

 inhabited-is-one-connected : {X : 𝓤 ̇}
                            → ∥ X ∥ → X is 1 connected
 inhabited-is-one-connected x-anon =
  pointed-props-are-singletons (prop-trunc-to-one-trunc x-anon) one-trunc-is-prop

 one-connected-iff-inhabited : {X : 𝓤 ̇}
                             → X is 1 connected
                             ↔ ∥ X ∥
 one-connected-iff-inhabited =
  (one-connected-is-inhabited , inhabited-is-one-connected)

 one-connected-map-is-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                           → map f is 1 connected
                           → is-surjection f
 one-connected-map-is-surj f-1-con y = one-connected-is-inhabited (f-1-con y)

 surj-is-one-connected-map : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                           → is-surjection f
                           → map f is 1 connected
 surj-is-one-connected-map f-is-surj y = inhabited-is-one-connected (f-is-surj y)

 one-connected-map-iff-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                            → map f is 1 connected
                            ↔ is-surjection f
 one-connected-map-iff-surj = (one-connected-map-is-surj , surj-is-one-connected-map)

\end{code}

We now devlop some closure conditions pertaining to connectedness. Connectedness
is closed under equivalence as expected, but more importantly connectedness
extends below: more precisely if a type is k connected then it is l connected
for all l ≤ k. We provide many incarnations of this fact below which may prove
useful. 

\begin{code}

 connectedness-closed-under-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ}
                                  → X ≃ Y
                                  → Y is k connected
                                  → X is k connected
 connectedness-closed-under-equiv e Y-con =
   equiv-to-singleton (truncation-closed-under-equiv e) Y-con

 contractible-types-are-connected : {X : 𝓤 ̇} {n : ℕ}
                                  → is-contr X
                                  → X is n connected
 contractible-types-are-connected {𝓤} {X} {n} (c , C) = ((∣ c ∣[ n ]) , C')
  where
   C' : (s : ∥ X ∥[ n ]) → (∣ c ∣[ n ]) ＝ s
   C' = ∥∥ₙ-ind (hlevels-are-closed-under-id ∥∥ₙ-hlevel (∣ c ∣[ n ]))
                (λ x → ap ∣_∣[ n ] (C x))

 connectedness-is-lower-closed : {X : 𝓤 ̇} {k : ℕ}
                               → X is (succ k) connected
                               → X is k connected
 connectedness-is-lower-closed {𝓤} {X} {k} X-succ-con =
   equiv-to-singleton successive-truncations-equiv 
                      (contractible-types-are-connected X-succ-con)

 connectedness-extends-to-zero : {X : 𝓤 ̇} {k : ℕ}
                               → X is k connected
                               → X is 0 connected
 connectedness-extends-to-zero {𝓤} {X} {0} X-con = X-con
 connectedness-extends-to-zero {𝓤} {X} {succ k} X-con =
   connectedness-extends-to-zero (connectedness-is-lower-closed X-con)

 connectedness-step-down : {X : 𝓤 ̇} {k l : ℕ}
                         → X is (l +' k) connected
                         → X is l connected
 connectedness-step-down {𝓤} {X} {0} {l} X-con = X-con
 connectedness-step-down {𝓤} {X} {succ k} {l} X-con =
   connectedness-step-down (connectedness-is-lower-closed X-con)

 connectedness-extends-below : {X : 𝓤 ̇} {k l : ℕ}
                             → (l ≤ℕ k)
                             → X is k connected
                             → X is l connected
 connectedness-extends-below {𝓤} {X} {k} {l} o X-con =
   connectedness-step-down (transport (λ z → X is z connected) p X-con)
  where
   m : ℕ
   m = pr₁ (subtraction l k o)
   p = k        ＝⟨ pr₂ (subtraction l k o) ⁻¹ ⟩
       m +' l   ＝⟨ addition-commutativity m l ⟩
       l +' m   ∎

\end{code}

We can characterize connected types in terms of inhabitedness and connectedness
of the identity type at the level below. We will assume univalence when neccesary.

\begin{code}

 conn-to-inhabited : {X : 𝓤 ̇} {n : ℕ}
                   → X is (succ n) connected
                   → ∥ X ∥
 conn-to-inhabited {_} {_} {0} X-conn =
  center (equiv-to-singleton' one-trunc-≃-prop-trunc X-conn)
 conn-to-inhabited {_} {_} {succ n} X-conn =
  conn-to-inhabited (connectedness-is-lower-closed X-conn)

 conn-to-id-conn : {X : 𝓤 ̇} {n : ℕ}
                 → (ua : is-univalent 𝓤)
                 → X is (succ n) connected
                 → (x y : X) → (x ＝ y) is n connected
 conn-to-id-conn {_} {_} {n} ua X-conn x y =
  equiv-to-singleton (eliminated-trunc-identity-char ua)
                     (is-prop-implies-is-prop' (singletons-are-props X-conn)
                                               ∣ x ∣[ succ n ]
                                               ∣ y ∣[ succ n ])

 conn-to-inhabited-id-conn : {X : 𝓤 ̇} {n : ℕ}
                           → (ua : is-univalent 𝓤)
                           → X is (succ n) connected
                           → ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
 conn-to-inhabited-id-conn ua X-conn =
  (conn-to-inhabited X-conn , conn-to-id-conn ua X-conn)

 inhabited-id-conn-to-conn : {X : 𝓤 ̇} {n : ℕ}
                           → (ua : is-univalent 𝓤)
                           → ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
                           → X is (succ n) connected
 inhabited-id-conn-to-conn {_} {_} {0} ua (anon-x , id-conn) =
  pointed-props-are-singletons (prop-trunc-to-one-trunc anon-x) one-trunc-is-prop
 inhabited-id-conn-to-conn {_} {_} {succ n} ua (anon-x , id-conn) =
  ∥∥-rec (being-singleton-is-prop fe)
         (λ x → (∣ x ∣[ succ (succ n) ]
          , ∥∥ₙ-ind (λ v → hlevels-are-upper-closed
                            (λ p q → ∥∥ₙ-hlevel ∣ x ∣[ succ (succ n) ] v p q)) 
                    (λ y → forth-trunc-id-char ua (center (id-conn x y)))))
         anon-x

 connected-characterization : {X : 𝓤 ̇} {n : ℕ}
                            → (ua : is-univalent 𝓤)
                            → X is (succ n) connected
                            ↔ ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
 connected-characterization ua =
  (conn-to-inhabited-id-conn ua , inhabited-id-conn-to-conn ua)

 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ} {x x' : X}
                      → (ua : is-univalent (𝓤 ⊔ 𝓥))
                      → (f : X → Y)
                      → map f is (succ n) connected
                      → map (ap f {x} {x'}) is n connected
 ap-is-less-connected {_} {_} {_} {_} {n} {x} {x'} ua f f-conn p =
  equiv-to-singleton (truncation-closed-under-equiv (fiber-of-ap-≃ f p))
                     (conn-to-id-conn ua (f-conn (f x')) (x , p) (x' , refl))

\end{code}


