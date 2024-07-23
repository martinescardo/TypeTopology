Ian Ray, 07/23/2024

Connectedness...

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
open import UF.H-Levels fe fe' pt
open import UF.Truncations fe fe' pt

\end{code}

We now define the notion of k-connectedness for types and functions with respect
to H-levels. We will then see that connectedness as defined elsewhere is a
special case:
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

We now add some results about connectedness.

\begin{code}

 open propositional-truncations-exist pt
 open GeneralTruncations te ua
 open 1-truncation-propositional-truncation te ua

 1-connected-map-is-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                         → map f is 1 connected
                         → is-surjection f
 1-connected-map-is-surj {𝓤} {𝓥} {X} {Y} {f} f-1-con y =
   g y (center (f-1-con y))
  where
   g : (y : Y) → ∥ fiber f y ∥[ 1 ] → y ∈image f
   g y' = ∥∥ₙ-rec (is-prop-implies-is-prop'
                  (being-in-the-image-is-prop y' f))
                  ∣_∣

 connectedness-closed-under-equiv : {𝓤 𝓥 : Universe}
                                  → (k : ℕ)
                                  → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                  → X ≃ Y
                                  → Y is k connected
                                  → X is k connected
 connectedness-closed-under-equiv k X Y e Y-con =
   equiv-to-singleton (truncation-closed-under-equiv k X Y e) Y-con

 contractible-types-are-connected : {𝓤 : Universe}
                                  → (X : 𝓤 ̇ )
                                  → is-contr X
                                  → (n : ℕ)
                                  → X is n connected
 contractible-types-are-connected X (c , C) n = ((∣ c ∣[ n ]) , C')
  where
   C' : (s : ∥ X ∥[ n ]) → (∣ c ∣[ n ]) ＝ s
   C' = ∥∥ₙ-ind (id-types-are-same-hlevel n ∥∥ₙ-h-level (∣ c ∣[ n ]))
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

 connected-characterization : {X : 𝓤 ̇} {n : ℕ}
                            → X is (succ n) connected
                            ↔ ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
 connected-characterization {𝓤} {X} {zero} = (left-to-right , right-to-left)
  where
   left-to-right : X is 1 connected
                 → ∥ X ∥ × ((x y : X) → (x ＝ y) is zero connected)
   left-to-right X-is-conn =
    (center (equiv-to-singleton' 1-trunc-≃-prop-trunc X-is-conn)
     , λ x x' → equiv-to-singleton trunc-id-type-char
                 (is-prop-implies-is-prop' (singletons-are-props X-is-conn)
                  ∣ x ∣[ 1 ] ∣ x' ∣[ 1 ]))
   right-to-left : ∥ X ∥ × ((x y : X) → (x ＝ y) is zero connected)
                 → X is 1 connected
   right-to-left (anon-x , conn) =
    pointed-props-are-singletons (prop-trunc-to-1-trunc anon-x) 1-trunc-is-prop
 connected-characterization {𝓤} {X} {succ n} = (left-to-right , {!!})
  where
   left-to-right : X is succ (succ n) connected
                 → ∥ X ∥ × ((x y : X) → (x ＝ y) is succ n connected)
   left-to-right X-is-conn = {!!}

 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y)
                      → (n : ℕ)
                      → map f is (succ n) connected
                      → map (ap f) is n connected
 ap-is-less-connected = {!!}

\end{code}
