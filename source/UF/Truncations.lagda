Ian Ray, 23 July 2024

Minor modifications by Tom de Jong on 4 September 2024

Modifactions made by Ian Ray on 26th September 2024.

Using records we define the general truncation of a type; this will include
a constructor, an induction principle and a computation rule
(up to identification). We then proceed to develop some machinery derived from
the induction principle and explore relationships, closure properties and
finally characterize the identity type of truncations. We explicitly assume
univalence locally for the characterization of idenity types but not
globally as many important properties hold in the absence of univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Truncations
        (fe : Fun-Ext)
       where

open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.TruncationLevels
open import UF.TruncatedTypes fe
open import UF.Univalence
open import UF.Yoneda
open import Notation.Decimal

\end{code}

We define the general notion of truncation using record types.

\begin{code}

record general-truncations-exist : 𝓤ω where
 field
  ∥_∥[_] : 𝓤 ̇ → ℕ₋₂ → 𝓤 ̇
  ∥∥ₙ-is-truncated : {X : 𝓤 ̇ } {n : ℕ₋₂} → ∥ X ∥[ n ] is n truncated
  ∣_∣[_] :  {X : 𝓤 ̇ } → X → (n : ℕ₋₂) → ∥ X ∥[ n ]
  ∥∥ₙ-ind : {X : 𝓤 ̇ } {n : ℕ₋₂} {P : ∥ X ∥[ n ] → 𝓥 ̇}
          → ((s : ∥ X ∥[ n ]) → (P s) is n truncated)
          → ((x : X) → P (∣ x ∣[ n ]))
          → (s : ∥ X ∥[ n ]) → P s
  ∥∥ₙ-ind-comp : {X : 𝓤 ̇ } {n : ℕ₋₂} {P : ∥ X ∥[ n ] → 𝓥 ̇ }
               → (m : (s : ∥ X ∥[ n ]) → (P s) is n truncated)
               → (g : (x : X) → P (∣ x ∣[ n ]))
               → (x : X) → ∥∥ₙ-ind m g (∣ x ∣[ n ]) ＝ g x
 infix 0 ∥_∥[_]
 infix 0 ∣_∣[_]

\end{code}

We now add some some machinery that will prove useful: truncation recursion
and uniqueness, induction/recursion for two arguments and all associated
computation rules.

\begin{code}

 ∥∥ₙ-rec : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
         → Y is n truncated
         → (X → Y)
         → ∥ X ∥[ n ] → Y
 ∥∥ₙ-rec m f s = ∥∥ₙ-ind (λ - → m) f s

 ∥∥ₙ-uniqueness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                → Y is n truncated
                → (f g : ∥ X ∥[ n ] → Y)
                → ((x : X) → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                → f ∼ g
 ∥∥ₙ-uniqueness m f g =
  ∥∥ₙ-ind (λ s → truncation-levels-closed-under-Id m (f s) (g s))

 ∥∥ₙ-rec-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
              → (m : Y is n truncated)
              → (g : X → Y)
              → (x : X) → ∥∥ₙ-rec m g ∣ x ∣[ n ] ＝ g x
 ∥∥ₙ-rec-comp m = ∥∥ₙ-ind-comp (λ - → m)

 ∥_∥ₙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
      → (f : X → Y)
      → ∥ X ∥[ n ] → ∥ Y ∥[ n ]
 ∥_∥ₙ {_} {_} {_} {_} {n} f = ∥∥ₙ-rec ∥∥ₙ-is-truncated (∣_∣[ n ] ∘ f)

 ∥∥ₙ-functorial-id : {X : 𝓤 ̇ } {n : ℕ₋₂}
                   → ∥ id ∥ₙ ∼ id
 ∥∥ₙ-functorial-id {_} {X} {n} =
  ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated ∥ id ∥ₙ id H
  where
   H : (x : X) → ∥ id ∥ₙ ∣ x ∣[ n ] ＝ ∣ x ∣[ n ]
   H = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣_∣[ n ]

 ∥∥ₙ-functorial-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ₋₂}
                     → (f : X → Y)
                     → (g : Y → Z)
                     → ∥ g ∘ f ∥ₙ ∼ ∥ g ∥ₙ ∘ ∥ f ∥ₙ
 ∥∥ₙ-functorial-comp {_} {_} {_} {X} {_} {_} {n} f g =
  ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated ∥ g ∘ f ∥ₙ (∥ g ∥ₙ ∘ ∥ f ∥ₙ) H
  where
   H : (x : X) → ∥ g ∘ f ∥ₙ ∣ x ∣[ n ] ＝ ∥ g ∥ₙ (∥ f ∥ₙ ∣ x ∣[ n ])
   H x = ∥ g ∘ f ∥ₙ ∣ x ∣[ n ]         ＝⟨ I ⟩
         ∣ g (f x) ∣[ n ]              ＝⟨ II ⟩
         ∥ g ∥ₙ ∣ f x ∣[ n ]           ＝⟨ III ⟩
         ∥ g ∥ₙ (∥ f ∥ₙ ∣ x ∣[ n ])    ∎ 
    where
     I = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (∣_∣[ n ] ∘ g ∘ f) x
     II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (∣_∣[ n ] ∘ g) (f x) ⁻¹
     III = ap ∥ g ∥ₙ (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (∣_∣[ n ] ∘ f) x) ⁻¹

 ∥∥ₙ-rec₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ₋₂}
          → Z is n truncated
          → (X → Y → Z)
          → ∥ X ∥[ n ] → ∥ Y ∥[ n ] → Z
 ∥∥ₙ-rec₂ m g = ∥∥ₙ-rec (truncated-types-closed-under-→ m)
                        (λ x → ∥∥ₙ-rec m (g x))

 ∥∥ₙ-rec-comp₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ₋₂}
               → (m : Z is n truncated)
               → (g : X → Y → Z)
               → (x : X) → (y : Y)
               → ∥∥ₙ-rec₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
 ∥∥ₙ-rec-comp₂ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} m g x y =
  ∥∥ₙ-rec₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ I ⟩
  ∥∥ₙ-rec m (g x) ∣ y ∣[ n ]         ＝⟨ ∥∥ₙ-rec-comp m (g x) y ⟩
  g x y                              ∎
   where
    I = happly (∥∥ₙ-rec-comp (truncated-types-closed-under-→ m)
                (λ x → ∥∥ₙ-rec m (g x)) x)
               ∣ y ∣[ n ]

 abstract
  ∥∥ₙ-ind₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
           → (P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇)
           → ((u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → (P u v) is n truncated)
           → ((x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
           → (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → P u v
  ∥∥ₙ-ind₂ {𝓤} {𝓥} {𝓦} {X} {Y} {n} P m f =
   ∥∥ₙ-ind (λ u → truncated-types-closed-under-Π (P u) (m u))
           (λ x → ∥∥ₙ-ind (λ v → m ∣ x ∣[ n ] v) (f x))
           
  ∥∥ₙ-ind-comp₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                → (P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇)
                → (m : (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ])
                 → (P u v) is n truncated)
                → (g : (x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
                → (x : X) → (y : Y)
                → ∥∥ₙ-ind₂ P m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
  ∥∥ₙ-ind-comp₂ {𝓤} {𝓥} {𝓦} {X} {Y} {n} P m g x y =
   ∥∥ₙ-ind₂ P m g ∣ x ∣[ n ] ∣ y ∣[ n ]     ＝⟨ I ⟩
   ∥∥ₙ-ind (m ∣ x ∣[ n ]) (g x) ∣ y ∣[ n ]  ＝⟨ II ⟩
   g x y                                    ∎
    where
     I : ∥∥ₙ-ind₂ P m g ∣ x ∣[ n ] ∣ y ∣[ n ]
       ＝ ∥∥ₙ-ind (m ∣ x ∣[ n ]) (g x) ∣ y ∣[ n ]
     I = happly
          (∥∥ₙ-ind-comp (λ u → truncated-types-closed-under-Π (P u) (m u))
           (λ x' → ∥∥ₙ-ind (m ∣ x' ∣[ n ]) (g x')) x)
          ∣ y ∣[ n ]
     II : ∥∥ₙ-ind (m ∣ x ∣[ n ]) (g x) ∣ y ∣[ n ] ＝ g x y
     II = ∥∥ₙ-ind-comp (m ∣ x ∣[ n ]) (g x) y

\end{code} 

We characterize the first couple levels of truncation.

(TODO: 1-type is a groupoid).

\begin{code}

 −2-trunc-is-contr : {X : 𝓤 ̇ } → is-contr (∥ X ∥[ −2 ])
 −2-trunc-is-contr = ∥∥ₙ-is-truncated

 −1-trunc-is-prop : {X : 𝓤 ̇ } → is-prop (∥ X ∥[ −1 ])
 −1-trunc-is-prop = is-prop'-implies-is-prop ∥∥ₙ-is-truncated

 0-trunc-is-set : {X : 𝓤 ̇ } → is-set (∥ X ∥[ 0 ])
 0-trunc-is-set {𝓤} {X} {x} {y} =
  is-prop'-implies-is-prop (∥∥ₙ-is-truncated x y)

\end{code}

We demonstrate the equivalence of -1-truncation and propositional truncation:
 ∥ X ∥[ −1 ] ≃ ∥ X ∥

\begin{code}

 module _ (pt : propositional-truncations-exist)
           where

  open propositional-truncations-exist pt
  
  −1-trunc-to-prop-trunc : {X : 𝓤 ̇} → ∥ X ∥[ −1 ] → ∥ X ∥
  −1-trunc-to-prop-trunc = ∥∥ₙ-rec (is-prop-implies-is-prop' ∥∥-is-prop) ∣_∣

  prop-trunc-to-−1-trunc : {X : 𝓤 ̇} → ∥ X ∥ → ∥ X ∥[ −1 ]
  prop-trunc-to-−1-trunc = ∥∥-rec −1-trunc-is-prop (∣_∣[ −1 ])

  −1-trunc-≃-prop-trunc : {X : 𝓤 ̇}
                         → (∥ X ∥[ −1 ]) ≃ ∥ X ∥
  −1-trunc-≃-prop-trunc =
   logically-equivalent-props-are-equivalent −1-trunc-is-prop ∥∥-is-prop
                                             −1-trunc-to-prop-trunc
                                             prop-trunc-to-−1-trunc

\end{code}

We provide the canonical predecessor map and show truncations are closed under
equivalence and successive applications of truncation

TODO: closure under retracts, embeddings, etc. Note that functoriality of
∥_∥ₙ allows us to simplify existing closure proofs.

\begin{code}
 canonical-pred-map : {X : 𝓤 ̇} {n : ℕ₋₂}
                    → ∥ X ∥[ succ n ] → ∥ X ∥[ n ]
 canonical-pred-map {𝓤} {X} {n} x =
  ∥∥ₙ-rec (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated)
          ∣_∣[ n ] x

 canonical-pred-map-comp : {X : 𝓤 ̇} {n : ℕ₋₂} (x : X)
                         → canonical-pred-map (∣ x ∣[ succ n ]) ＝ (∣ x ∣[ n ])
 canonical-pred-map-comp {𝓤} {X} {n} x =
  ∥∥ₙ-rec-comp (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated)
               ∣_∣[ n ] x

 to-∼-of-maps-with-truncated-domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ₋₂}
                                    → (f g : ∥ X ∥[ n ] → Y)
                                    → Y is n truncated
                                    → ((x : X)
                                          → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                                    → f ∼ g
 to-∼-of-maps-with-truncated-domain f g m =
  ∥∥ₙ-ind (λ - → truncation-levels-closed-under-Id m (f -) (g -))

 to-∼-of-maps-between-truncated-types : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ₋₂}
                                      → (f g : ∥ X ∥[ n ] → ∥ Y ∥[ n ])
                                      → ((x : X)
                                            → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                                      → f ∼ g
 to-∼-of-maps-between-truncated-types {𝓤} {𝓥} {X} {Y} {n} f g =
  to-∼-of-maps-with-truncated-domain f g ∥∥ₙ-is-truncated

 truncation-closed-under-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ₋₂}
                               → X ≃ Y
                               → ∥ X ∥[ n ] ≃ ∥ Y ∥[ n ]
 truncation-closed-under-equiv {𝓤} {𝓥} {X} {Y} {n} e = (f , (b , G) , (b , H))
  where
   f : ∥ X ∥[ n ] → ∥ Y ∥[ n ]
   f = ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ x → ∣ ⌜ e ⌝ x ∣[ n ])
   b : ∥ Y ∥[ n ] → ∥ X ∥[ n ]
   b = ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ y → ∣ ⌜ e ⌝⁻¹ y ∣[ n ])
   H : b ∘ f ∼ id
   H = to-∼-of-maps-between-truncated-types (b ∘ f) id H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))           ＝⟨ I ⟩
            b (∣ ⌜ e ⌝ x ∣[ n ])         ＝⟨ II ⟩
            (∣ ⌜ e ⌝⁻¹ (⌜ e ⌝ x) ∣[ n ]) ＝⟨ III ⟩
            (∣ x ∣[ n ])                 ∎
      where
       I = ap b (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ x → ∣ (⌜ e ⌝ x) ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) (⌜ e ⌝ x)
       III = ap (λ x → ∣ x ∣[ n ]) (inverses-are-retractions' e x)
   G : f ∘ b ∼ id
   G = to-∼-of-maps-between-truncated-types (f ∘ b) id G'
    where
     G' : (y : Y) → f (b (∣ y ∣[ n ])) ＝ (∣ y ∣[ n ])
     G' y = f (b (∣ y ∣[ n ]))           ＝⟨ I ⟩
            f (∣ (⌜ e ⌝⁻¹ y) ∣[ n ])     ＝⟨ II ⟩
            (∣ ⌜ e ⌝ (⌜ e ⌝⁻¹ y) ∣[ n ]) ＝⟨ III ⟩
            (∣ y ∣[ n ])                 ∎
      where
       I = ap f (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) y)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ x → ∣ ⌜ e ⌝ x ∣[ n ]) (⌜ e ⌝⁻¹ y)
       III = ap ∣_∣[ n ] (inverses-are-sections' e y)

 successive-truncations-equiv : {X : 𝓤 ̇} {n : ℕ₋₂}
                              → (∥ X ∥[ n ]) ≃ (∥ (∥ X ∥[ succ n ]) ∥[ n ])
 successive-truncations-equiv {𝓤} {X} {n} = (f , (b , G) , (b , H))
  where
   f : ∥ X ∥[ n ] → ∥ ∥ X ∥[ succ n ] ∥[ n ]
   f = ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ _ → ∣ ∣ _ ∣[ succ n ] ∣[ n ])
   b : ∥ ∥ X ∥[ succ n ] ∥[ n ] → ∥ X ∥[ n ]
   b = ∥∥ₙ-rec ∥∥ₙ-is-truncated canonical-pred-map
   G : f ∘ b ∼ id
   G = to-∼-of-maps-with-truncated-domain (f ∘ b) id ∥∥ₙ-is-truncated
        (to-∼-of-maps-with-truncated-domain
          (f ∘ b ∘ ∣_∣[ n ])
          ∣_∣[ n ]
          (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated)
          G')
    where
     G' : (x : X)
        → f (b (∣ ∣ x ∣[ succ n ] ∣[ n ])) ＝ (∣ ∣ x ∣[ succ n ] ∣[ n ])
     G' x = f (b (∣ ∣ x ∣[ succ n ] ∣[ n ]))         ＝⟨ I ⟩
            f (canonical-pred-map (∣ x ∣[ succ n ])) ＝⟨ II ⟩
            f (∣ x ∣[ n ])                           ＝⟨ III ⟩
            (∣ ∣ x ∣[ succ n ] ∣[ n ])               ∎
      where
       I = ap f (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated canonical-pred-map
                              (∣ x ∣[ succ n ]))
       II = ap f (canonical-pred-map-comp x)
       III = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ _ → ∣ ∣ _ ∣[ succ n ] ∣[ n ]) x
   H : b ∘ f ∼ id
   H = to-∼-of-maps-with-truncated-domain (b ∘ f) id ∥∥ₙ-is-truncated H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))                   ＝⟨ I ⟩
            b (∣ ∣ x ∣[ succ n ] ∣[ n ])         ＝⟨ II ⟩
            canonical-pred-map (∣ x ∣[ succ n ]) ＝⟨ canonical-pred-map-comp x ⟩
            (∣ x ∣[ n ])                         ∎
      where
       I = ap b (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ _ → ∣ ∣ _ ∣[ succ n ] ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated canonical-pred-map (∣ x ∣[ succ n ])

\end{code}

We now define an equivalence that characterizes the truncated identity type
under the assumption of univalence. The following proof was inspired by
the agda unimath library -- although the development there is more thorough --
for details see: https://unimath.github.io/agda-unimath/foundation.truncations.

\begin{code}

 canonical-identity-trunc-map : {X : 𝓤 ̇} {x x' : X} {n : ℕ₋₂}
                              → ∥ x ＝ x' ∥[ n ]
                              → ∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ]
 canonical-identity-trunc-map {𝓤} {X} {x} {x'} {n} =
  ∥∥ₙ-rec (∥∥ₙ-is-truncated ∣ x ∣[ succ n ] ∣ x' ∣[ succ n ])
          (ap ∣_∣[ (succ n) ])

 module _ {X : 𝓤 ̇} {n : ℕ₋₂}
          (ua : is-univalent 𝓤) (x : X)
           where

  trunc-id-family : ∥ X ∥[ succ n ] → 𝕋 n 𝓤
  trunc-id-family = ∥∥ₙ-rec (𝕋-is-of-next-truncation-level ua)
                            (λ x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-is-truncated))

  trunc-id-family-type : ∥ X ∥[ succ n ] → 𝓤 ̇
  trunc-id-family-type = pr₁ ∘ trunc-id-family

  trunc-id-family-level : (v : ∥ X ∥[ succ n ])
                        → (trunc-id-family-type v) is n truncated
  trunc-id-family-level = pr₂ ∘ trunc-id-family

  trunc-id-family-computes : (x' : X)
                           → trunc-id-family-type ∣ x' ∣[ succ n ]
                             ＝ ∥ x ＝ x' ∥[ n ]
  trunc-id-family-computes x' =
    ap pr₁ (∥∥ₙ-rec-comp (𝕋-is-of-next-truncation-level ua)
                         (λ x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-is-truncated))
                         x')

  trunc-id-forward-map : (x' : X)
                       → trunc-id-family-type ∣ x' ∣[ succ n ]
                       → ∥ x ＝ x' ∥[ n ]
  trunc-id-forward-map x' = transport id (trunc-id-family-computes x')

  trunc-id-backward-map : (x' : X)
                        → ∥ x ＝ x' ∥[ n ]
                        → trunc-id-family-type ∣ x' ∣[ succ n ]
  trunc-id-backward-map x' = transport⁻¹ id (trunc-id-family-computes x')

  trunc-id-back-is-retraction
   : (x' : X)
   → trunc-id-backward-map x' ∘ trunc-id-forward-map x' ∼ id
  trunc-id-back-is-retraction x' q =
   forth-and-back-transport (trunc-id-family-computes x')

  refl-trunc-id-family : trunc-id-family-type ∣ x ∣[ succ n ]
  refl-trunc-id-family = trunc-id-backward-map x ∣ refl ∣[ n ]

  identity-on-trunc-to-family : (v : ∥ X ∥[ succ n ])
                              → ∣ x ∣[ succ n ] ＝ v
                              → trunc-id-family-type v
  identity-on-trunc-to-family .(∣ x ∣[ succ n ]) refl = refl-trunc-id-family

  trunc-id-family-is-identity-system : is-contr (Σ trunc-id-family-type)
  trunc-id-family-is-identity-system =
   ((∣ x ∣[ succ n ] , refl-trunc-id-family) , trunc-id-fam-is-central)
   where
    I : (x' : X) (p : x ＝ x')
      → (∣ x ∣[ succ n ] , refl-trunc-id-family)
       ＝[ Σ trunc-id-family-type ]
        (∣ x' ∣[ succ n ] , trunc-id-backward-map x' ∣ p ∣[ n ])
    I x' refl = refl

    II : (x' : X) (q' : ∥ x ＝ x' ∥[ n ])
       → (∣ x ∣[ succ n ] , refl-trunc-id-family)
        ＝[ Σ trunc-id-family-type ]
         (∣ x' ∣[ succ n ] , trunc-id-backward-map x' q')
    II x' = ∥∥ₙ-ind (λ s → truncated-types-closed-under-Σ
                            trunc-id-family-type
                            ∥∥ₙ-is-truncated
                            (λ v → truncation-levels-are-upper-closed
                                    (trunc-id-family-level v))
                            (∣ x ∣[ succ n ] , refl-trunc-id-family)
                            (∣ x' ∣[ succ n ] , trunc-id-backward-map x' s))
                      (I x')

    III : (x' : X) (q : trunc-id-family-type ∣ x' ∣[ succ n ])
        → (∣ x ∣[ succ n ] , refl-trunc-id-family)
          ＝[ Σ trunc-id-family-type ]
          (∣ x' ∣[ succ n ] , q)
    III x' q = transport (λ - → (∣ x ∣[ succ n ] , refl-trunc-id-family)
                                ＝[ Σ trunc-id-family-type ]
                                (∣ x' ∣[ succ n ] , -))
                         (trunc-id-back-is-retraction x' q)
                         (II x' (trunc-id-forward-map x' q))

    IV : (v : ∥ X ∥[ succ n ]) (q : trunc-id-family-type v)
       → (∣ x ∣[ succ n ] , refl-trunc-id-family) ＝ (v , q)
    IV =
     ∥∥ₙ-ind
      (λ s → truncated-types-closed-under-Π
              (λ q → (∣ x ∣[ succ n ] , refl-trunc-id-family) ＝ (s , q))
              (λ q → truncated-types-closed-under-Σ
                      trunc-id-family-type
                       (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated)
                       (λ v → truncation-levels-are-upper-closed
                               (truncation-levels-are-upper-closed
                                 (trunc-id-family-level v)))
                       (∣ x ∣[ succ n ] , refl-trunc-id-family)
                       (s , q)))
              III

    trunc-id-fam-is-central : is-central (Σ trunc-id-family-type)
                                         (∣ x ∣[ succ n ] , refl-trunc-id-family)
    trunc-id-fam-is-central (v , q) = IV v q

 trunc-identity-characterization : {X : 𝓤 ̇} {n : ℕ₋₂}
                                 → (ua : is-univalent 𝓤)
                                 → (x : X) (v : ∥ X ∥[ succ n ])
                                 → (∣ x ∣[ succ n ] ＝ v)
                                 ≃ trunc-id-family-type ua x v
 trunc-identity-characterization {𝓤} {X} {n} ua x v =
  (identity-on-trunc-to-family ua x v ,
   Yoneda-Theorem-forth ∣ x ∣[ succ n ]
    (identity-on-trunc-to-family ua x)
    (trunc-id-family-is-identity-system ua x) v)

 eliminated-trunc-identity-char : {X : 𝓤 ̇} {x x' : X} {n : ℕ₋₂}
                                → (ua : is-univalent 𝓤)
                                → ∥ x ＝ x' ∥[ n ]
                                ≃ (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ])
 eliminated-trunc-identity-char {𝓤} {X} {x} {x'} {n} ua =
  ≃-comp (idtoeq ∥ x ＝ x' ∥[ n ]
                 (trunc-id-family-type ua x ∣ x' ∣[ succ n ])
                 (trunc-id-family-computes ua x x' ⁻¹))
         (≃-sym (trunc-identity-characterization ua x ∣ x' ∣[ succ n ]))

 forth-trunc-id-char : {X : 𝓤 ̇} {x x' : X} {n : ℕ₋₂}
                     → (ua : is-univalent 𝓤)
                     → ∥ x ＝ x' ∥[ n ]
                     → (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ])
 forth-trunc-id-char ua = ⌜ eliminated-trunc-identity-char ua ⌝

\end{code}

We show that the existence of propositional truncation follows from the existence
of general truncations. Notice this implication manifests as a function between
record types.

\begin{code}

general-truncations-give-propositional-truncations : general-truncations-exist
                                                   → propositional-truncations-exist
general-truncations-give-propositional-truncations te = record
 { ∥_∥        = ∥_∥[ −1 ]
 ; ∥∥-is-prop = is-prop'-implies-is-prop ∥∥ₙ-is-truncated
 ; ∣_∣        = ∣_∣[ −1 ]
 ; ∥∥-rec     = λ - → ∥∥ₙ-rec (is-prop-implies-is-prop' -)
 }
 where
  open general-truncations-exist te

\end{code}
