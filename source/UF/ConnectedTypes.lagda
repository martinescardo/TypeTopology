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

module UF.ConnectedTypes (fe : FunExt)
                         (fe' : Fun-Ext)
                         (pt : propositional-truncations-exist)
                          where

open import UF.ImageAndSurjection pt
open import UF.H-Levels fe fe' 
open import UF.Truncations fe fe' pt

\end{code}

We now define the notion of k-connectedness for types and functions with respect
to H-levels. We will then see that connectedness as defined elsewhere is a
special case of k-connectedness:
Connectedness typically means set connectedness. In terms of H-levels defined
here it will mean 2-connectedness.

\begin{code}

module k-connectedness
        (te : H-level-truncations-exist)
        (ua : Univalence)
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
 open GeneralTruncations te ua
 open 1-truncation-propositional-truncation-relationship te ua

 1-connected-is-inhabited : {X : 𝓤 ̇}
                          → X is 1 connected → ∥ X ∥
 1-connected-is-inhabited X-1-conn = 1-trunc-to-prop-trunc (center X-1-conn)

 inhabited-is-1-connected : {X : 𝓤 ̇}
                          → ∥ X ∥ → X is 1 connected
 inhabited-is-1-connected x-anon =
  pointed-props-are-singletons (prop-trunc-to-1-trunc x-anon) one-trunc-is-prop

 1-connected-iff-inhabited : {X : 𝓤 ̇}
                           → X is 1 connected
                           ↔ ∥ X ∥
 1-connected-iff-inhabited {𝓤} {X} =
  (1-connected-is-inhabited , inhabited-is-1-connected)

 1-connected-map-is-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                         → map f is 1 connected
                         → is-surjection f
 1-connected-map-is-surj {𝓤} {𝓥} {X} {Y} {f} f-1-con y =
  1-connected-is-inhabited (f-1-con y)

 surj-is-1-connected-map : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                         → is-surjection f
                         → map f is 1 connected
 surj-is-1-connected-map f-is-surj y = inhabited-is-1-connected (f-is-surj y)

 1-connected-map-iff-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                         → map f is 1 connected
                         ↔ is-surjection f
 1-connected-map-iff-surj = (1-connected-map-is-surj , surj-is-1-connected-map)

\end{code}

We now devlop some closure conditions pertaining to connectedness. Connectedness
is closed under equivalence as expected, but more importantly connectedness
extends below: more precisely if a type is n connected then it is k connected
for all k ≤ n. We provide many incarnations of this fact below which may prove
useful. 

\begin{code}

 connectedness-closed-under-equiv : {𝓤 𝓥 : Universe}
                                  → (k : ℕ)
                                  → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                  → X ≃ Y
                                  → Y is k connected
                                  → X is k connected
 connectedness-closed-under-equiv k X Y e Y-con =
   equiv-to-singleton (truncation-closed-under-equiv e) Y-con

 contractible-types-are-connected : {𝓤 : Universe}
                                  → (X : 𝓤 ̇ )
                                  → is-contr X
                                  → (n : ℕ)
                                  → X is n connected
 contractible-types-are-connected X (c , C) n = ((∣ c ∣[ n ]) , C')
  where
   C' : (s : ∥ X ∥[ n ]) → (∣ c ∣[ n ]) ＝ s
   C' = ∥∥ₙ-ind (id-types-are-same-hlevel n (∥∥ₙ-h-level n) (∣ c ∣[ n ]))
                 (λ x → ap (λ x → ∣ x ∣[ n ]) (C x))

 connectedness-is-lower-closed : {X : 𝓤 ̇} {k : ℕ}
                               → X is (succ k) connected
                               → X is k connected
 connectedness-is-lower-closed {𝓤} {X} {k} X-succ-con =
   equiv-to-singleton (succesive-truncations-equiv X k)
                      (contractible-types-are-connected (∥ X ∥[ succ k ])
                                                        X-succ-con k)

 connectedness-extends-to-zero : {X : 𝓤 ̇} (k : ℕ)
                               → X is k connected
                               → X is zero connected
 connectedness-extends-to-zero zero X-con = X-con
 connectedness-extends-to-zero (succ k) X-con =
   connectedness-extends-to-zero k (connectedness-is-lower-closed X-con)

 connectedness-step-down : {X : 𝓤 ̇} (k l : ℕ)
                         → X is (l +' k) connected
                         → X is l connected
 connectedness-step-down zero l X-con = X-con
 connectedness-step-down (succ k) l X-con =
   connectedness-step-down k l (connectedness-is-lower-closed X-con)

 connectedness-extends-below : {X : 𝓤 ̇} (k l : ℕ)
                             → (l ≤ℕ k)
                             → X is k connected
                             → X is l connected
 connectedness-extends-below {𝓤} {X} k l o X-con =
   connectedness-step-down m l (transport (λ z → X is z connected) p X-con)
  where
   m : ℕ
   m = pr₁ (subtraction l k o)
   p = k        ＝⟨ pr₂ (subtraction l k o) ⁻¹ ⟩
       m +' l   ＝⟨ addition-commutativity m l ⟩
       l +' m   ∎

\end{code}

We can characterize connected types in terms of inhabitedness and connectedness
at the level below of the identity type.

\begin{code}

 conn-to-inhabited : {X : 𝓤 ̇} (n : ℕ)
                   → X is (succ n) connected
                   → ∥ X ∥
 conn-to-inhabited zero X-conn =
  center (equiv-to-singleton' 1-trunc-≃-prop-trunc X-conn)
 conn-to-inhabited (succ n) X-conn =
  conn-to-inhabited n (connectedness-is-lower-closed X-conn)

 conn-to-id-conn : {X : 𝓤 ̇} (n : ℕ)
                 → X is (succ n) connected
                 → ((x y : X) → (x ＝ y) is n connected)
 conn-to-id-conn n X-conn x y =
  equiv-to-singleton eliminated-trunc-identity-char
                     (is-prop-implies-is-prop' (singletons-are-props X-conn)
                                               ∣ x ∣[ succ n ]
                                               ∣ y ∣[ succ n ])

 conn-to-inhabited-id-conn : {X : 𝓤 ̇} (n : ℕ)
                           → X is (succ n) connected
                           → ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
 conn-to-inhabited-id-conn n X-conn =
  (conn-to-inhabited n X-conn , conn-to-id-conn n X-conn)

 inhabited-id-conn-to-conn : {X : 𝓤 ̇} (n : ℕ)
                           → ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
                           → X is (succ n) connected
 inhabited-id-conn-to-conn zero (anon-x , id-conn) =
  pointed-props-are-singletons (prop-trunc-to-1-trunc anon-x) one-trunc-is-prop
 inhabited-id-conn-to-conn (succ n) (anon-x , id-conn) =
  ∥∥-rec (being-singleton-is-prop fe')
         (λ x → (∣ x ∣[ succ (succ n) ]
          , ∥∥ₙ-ind (λ - → hlevels-are-upper-closed (succ n)
                            (∣ x ∣[ succ (succ n) ] ＝ -)
                            (∥∥ₙ-h-level (succ (succ n))
                                         ∣ x ∣[ succ (succ n) ] -))
                    (λ y → forth-trunc-id-char (center (id-conn x y)))))
         anon-x

 connected-characterization : {X : 𝓤 ̇} (n : ℕ)
                            → X is (succ n) connected
                            ↔ ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
 connected-characterization {𝓤} {X} n =
  (conn-to-inhabited-id-conn n , inhabited-id-conn-to-conn n)

 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ} {x x' : X}
                      → (f : X → Y)
                      → map f is (succ n) connected
                      → map (ap f {x} {x'}) is n connected
 ap-is-less-connected {𝓤} {𝓥} {X} {Y} {n} {x} {x'} f f-conn p =
  equiv-to-singleton (truncation-closed-under-equiv (fiber-of-ap-≃ f p))
                     (conn-to-id-conn n (f-conn (f x')) (x , p) (x' , refl))

\end{code}
