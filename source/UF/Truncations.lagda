Ian Ray, 23 July 2024

Minor modifications by Tom de Jong on 4 September 2024

Modifications made by Ian Ray on 26th September 2024.

Modifications made by Ian Ray on 17th December 2024.

Using records we define the general truncation of a type; this will include
a constructor, an induction principle and a computation rule
(up to identification). We then proceed to develop some machinery derived from
the induction principle and explore relationships, closure properties and
finally characterize the identity type of truncations. We explicitly assume
univalence locally for the characterization of identity types but not
globally as many important properties hold in the absence of univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Truncations
        (fe : Fun-Ext)
       where

open import MLTT.Spartan hiding (_+_)

open import UF.Base
open import UF.Equiv
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Size
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
  ∥∥ₙ-ind : {X : 𝓤 ̇ } {n : ℕ₋₂} {P : ∥ X ∥[ n ] → 𝓥 ̇ }
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

 ∥∥ₙ-universal-property : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                        → Y is n truncated
                        → (∥ X ∥[ n ] → Y) ≃ (X → Y)
 ∥∥ₙ-universal-property {_} {_} {X} {Y} {n} Y-trunc =
  (foreward , qinvs-are-equivs foreward (backward , H , G))
  where
   foreward : (∥ X ∥[ n ] → Y) → (X → Y)
   foreward g = g ∘ ∣_∣[ n ]
   backward : (X → Y) → (∥ X ∥[ n ] → Y)
   backward = ∥∥ₙ-rec Y-trunc
   H : backward ∘ foreward ∼ id
   H g = dfunext fe (∥∥ₙ-ind (λ - → truncation-levels-are-upper-closed Y-trunc
                              ((backward ∘ foreward) g -) (g -))
                             H')
    where
     H' : (x : X)
        → backward (foreward (g)) ∣ x ∣[ n ]  ＝ g ∣ x ∣[ n ]
     H' = ∥∥ₙ-ind-comp (λ - → Y-trunc) (g ∘ ∣_∣[ n ])
   G : foreward ∘ backward ∼ id
   G f = dfunext fe (∥∥ₙ-ind-comp (λ - → Y-trunc) f)

 to-∼-of-maps-between-truncated-types : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                                      → (f g : ∥ X ∥[ n ] → ∥ Y ∥[ n ])
                                      → ((x : X)
                                            → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                                      → f ∼ g
 to-∼-of-maps-between-truncated-types {𝓤} {𝓥} {X} {Y} {n} f g =
  ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated f g

 ∥∥ₙ-rec-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
              → (m : Y is n truncated)
              → (g : X → Y)
              → (x : X) → ∥∥ₙ-rec m g ∣ x ∣[ n ] ＝ g x
 ∥∥ₙ-rec-comp m = ∥∥ₙ-ind-comp (λ - → m)

 ∣_∣ₙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
      → (X → Y)
      → X → ∥ Y ∥[ n ]
 ∣_∣ₙ {_} {_} {_} {_} {n} f = ∣_∣[ n ] ∘ f

 ∥_∥ₙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
      → (X → Y)
      → ∥ X ∥[ n ] → ∥ Y ∥[ n ]
 ∥ f ∥ₙ = ∥∥ₙ-rec ∥∥ₙ-is-truncated (∣ f ∣ₙ)

 ∥∥ₙ-id-functorial : {X : 𝓤 ̇ } {n : ℕ₋₂}
                   → ∥ id ∥ₙ ∼ id
 ∥∥ₙ-id-functorial {_} {X} {n} =
  ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated ∥ id ∥ₙ id H
  where
   H : (x : X) → ∥ id ∥ₙ ∣ x ∣[ n ] ＝ ∣ x ∣[ n ]
   H = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣_∣[ n ]

 ∥∥ₙ-composition-functorial : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ₋₂}
                            → (f : X → Y)
                            → (g : Y → Z)
                            → ∥ g ∘ f ∥ₙ ∼ ∥ g ∥ₙ ∘ ∥ f ∥ₙ
 ∥∥ₙ-composition-functorial {_} {_} {_} {X} {_} {_} {n} f g =
  ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated ∥ g ∘ f ∥ₙ (∥ g ∥ₙ ∘ ∥ f ∥ₙ) H
  where
   H : (x : X) → ∥ g ∘ f ∥ₙ ∣ x ∣[ n ] ＝ ∥ g ∥ₙ (∥ f ∥ₙ ∣ x ∣[ n ])
   H x = ∥ g ∘ f ∥ₙ ∣ x ∣[ n ]         ＝⟨ I ⟩
         ∣ g (f x) ∣[ n ]              ＝⟨ II ⟩
         ∥ g ∥ₙ ∣ f x ∣[ n ]           ＝⟨ III ⟩
         ∥ g ∥ₙ (∥ f ∥ₙ ∣ x ∣[ n ])    ∎
    where
     I = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣ g ∘ f ∣ₙ x
     II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣ g ∣ₙ (f x) ⁻¹
     III = ap ∥ g ∥ₙ (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣ f ∣ₙ x) ⁻¹

 ∥∥ₙ-preserves-homotopy' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                        → (f g : X → Y)
                        → f ∼ g
                        → ∥ f ∥ₙ ∘ ∣_∣[ n ] ∼ ∥ g ∥ₙ ∘ ∣_∣[ n ]
 ∥∥ₙ-preserves-homotopy' {_} {_} {X} {_} {n} f g H x =
  ∥ f ∥ₙ ∣ x ∣[ n ]         ＝⟨ I ⟩
  ∣ f x ∣[ n ]              ＝⟨ II ⟩
  ∣ g x ∣[ n ]              ＝⟨ III ⟩
  ∥ g ∥ₙ ∣ x ∣[ n ]         ∎
  where
   I = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣ f ∣ₙ x
   II = ap ∣_∣[ n ] (H x)
   III = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated ∣ g ∣ₙ x ⁻¹

 ∥∥ₙ-preserves-homotopy : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                        → (f g : X → Y)
                        → f ∼ g
                        → ∥ f ∥ₙ ∼ ∥ g ∥ₙ
 ∥∥ₙ-preserves-homotopy {_} {_} {X} {_} {n} f g H = G
  where
   G : (x : ∥ X ∥[ n ]) → ∥ f ∥ₙ x ＝ ∥ g ∥ₙ x
   G = ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated ∥ f ∥ₙ ∥ g ∥ₙ
                      (∥∥ₙ-preserves-homotopy' f g H)

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
           → (P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇ )
           → ((u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → (P u v) is n truncated)
           → ((x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
           → (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → P u v
  ∥∥ₙ-ind₂ {𝓤} {𝓥} {𝓦} {X} {Y} {n} P m f =
   ∥∥ₙ-ind (λ u → truncated-types-closed-under-Π (P u) (m u))
           (λ x → ∥∥ₙ-ind (λ v → m ∣ x ∣[ n ] v) (f x))

  ∥∥ₙ-ind-comp₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                → (P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇ )
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

We characterize the first couple truncation levels.

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

  −1-trunc-to-prop-trunc : {X : 𝓤 ̇ } → ∥ X ∥[ −1 ] → ∥ X ∥
  −1-trunc-to-prop-trunc = ∥∥ₙ-rec (is-prop-implies-is-prop' ∥∥-is-prop) ∣_∣

  prop-trunc-to-−1-trunc : {X : 𝓤 ̇ } → ∥ X ∥ → ∥ X ∥[ −1 ]
  prop-trunc-to-−1-trunc = ∥∥-rec −1-trunc-is-prop (∣_∣[ −1 ])

  −1-trunc-≃-prop-trunc : {X : 𝓤 ̇ }
                         → (∥ X ∥[ −1 ]) ≃ ∥ X ∥
  −1-trunc-≃-prop-trunc =
   logically-equivalent-props-are-equivalent −1-trunc-is-prop ∥∥-is-prop
                                             −1-trunc-to-prop-trunc
                                             prop-trunc-to-−1-trunc

  props-are-truncated : {X : 𝓤 ̇ } {n : ℕ₋₂}
                      → is-prop X
                      → X is (n + 1) truncated
  props-are-truncated {_} {_} {−2} = is-prop-implies-is-prop'
  props-are-truncated {_} {_} {succ n} X-is-prop =
   truncation-levels-are-upper-closed
    (λ x x' → props-are-truncated X-is-prop x x')

\end{code}

We define the canonical predecessor map and give a computation rule.

\begin{code}
 canonical-pred-map : {X : 𝓤 ̇ } {n : ℕ₋₂}
                    → ∥ X ∥[ n + 1 ] → ∥ X ∥[ n ]
 canonical-pred-map {𝓤} {X} {n} =
  ∥∥ₙ-rec (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated) ∣_∣[ n ]

 canonical-pred-map-comp : {X : 𝓤 ̇ } {n : ℕ₋₂} (x : X)
                         → canonical-pred-map (∣ x ∣[ n + 1 ]) ＝ (∣ x ∣[ n ])
 canonical-pred-map-comp {𝓤} {X} {n} =
  ∥∥ₙ-rec-comp (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated) ∣_∣[ n ]

\end{code}

We show truncations are closed under equivalence and successive applications
of truncation.

TODO: closure under retracts, embeddings, etc. Note closure under equivalence
can be refactored to use closure under retracts.

\begin{code}

 truncation-closed-under-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
                                 → retract Y of X
                                 → retract ∥ Y ∥[ n ] of ∥ X ∥[ n ]
 truncation-closed-under-retract {_} {_} {X} {Y} {n} (r , s , H) =
  (∥ r ∥ₙ , ∥ s ∥ₙ , G)
  where
   G : ∥ r ∥ₙ ∘ ∥ s ∥ₙ ∼ id
   G y = (∥ r ∥ₙ ∘ ∥ s ∥ₙ) y ＝⟨ I ⟩
         ∥ r ∘ s ∥ₙ y        ＝⟨ II ⟩
         ∥ id ∥ₙ y           ＝⟨ III ⟩
         y                   ∎
    where
     I = ∥∥ₙ-composition-functorial s r y ⁻¹
     II = ∥∥ₙ-preserves-homotopy (r ∘ s) id H y
     III = ∥∥ₙ-id-functorial y

 truncation-closed-under-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ₋₂}
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

 truncations-of-small-types-are-small : {X : 𝓤 ̇ } {n : ℕ₋₂}
                                      → X is 𝓥 small
                                      → ∥ X ∥[ n ] is 𝓥 small
 truncations-of-small-types-are-small {_} {_} {_} {n} (Y , e) =
  (∥ Y ∥[ n ] , truncation-closed-under-equiv e)

 successive-truncations-equiv : {X : 𝓤 ̇ } {n : ℕ₋₂}
                              → (∥ X ∥[ n ]) ≃ (∥ (∥ X ∥[ n + 1 ]) ∥[ n ])
 successive-truncations-equiv {𝓤} {X} {n} = (f , (b , G) , (b , H))
  where
   f : ∥ X ∥[ n ] → ∥ ∥ X ∥[ n + 1 ] ∥[ n ]
   f = ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ _ → ∣ ∣ _ ∣[ n + 1 ] ∣[ n ])
   b : ∥ ∥ X ∥[ succ n ] ∥[ n ] → ∥ X ∥[ n ]
   b = ∥∥ₙ-rec ∥∥ₙ-is-truncated canonical-pred-map
   G : f ∘ b ∼ id
   G = ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated (f ∘ b) id
        (∥∥ₙ-uniqueness
          (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated)
          (f ∘ b ∘ ∣_∣[ n ])
          ∣_∣[ n ]
          G')
    where
     G' : (x : X)
        → f (b (∣ ∣ x ∣[ n + 1 ] ∣[ n ])) ＝ (∣ ∣ x ∣[ n + 1 ] ∣[ n ])
     G' x = f (b (∣ ∣ x ∣[ n + 1 ] ∣[ n ]))         ＝⟨ I ⟩
            f (canonical-pred-map (∣ x ∣[ n + 1 ])) ＝⟨ II ⟩
            f (∣ x ∣[ n ])                          ＝⟨ III ⟩
            (∣ ∣ x ∣[ n + 1 ] ∣[ n ])               ∎
      where
       I = ap f (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated canonical-pred-map
                              (∣ x ∣[ n + 1 ]))
       II = ap f (canonical-pred-map-comp x)
       III = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ _ → ∣ ∣ _ ∣[ n + 1 ] ∣[ n ]) x
   H : b ∘ f ∼ id
   H = ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated (b ∘ f) id H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))                   ＝⟨ I ⟩
            b (∣ ∣ x ∣[ n + 1 ] ∣[ n ])          ＝⟨ II ⟩
            canonical-pred-map (∣ x ∣[ n + 1 ])  ＝⟨ canonical-pred-map-comp x ⟩
            (∣ x ∣[ n ])                          ∎
      where
       I = ap b (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ _ → ∣ ∣ _ ∣[ n + 1 ] ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated canonical-pred-map (∣ x ∣[ n + 1 ])

 truncated-Σ-≃ : {X : 𝓤 ̇ } {P : X → 𝓦 ̇ } {n : ℕ₋₂}
               → ∥ Σ x ꞉ X , ∥ P x ∥[ n ] ∥[ n ] ≃ ∥ Σ x ꞉ X , P x ∥[ n ]
 truncated-Σ-≃ {_} {_} {X} {P} {n} = (f , (b , G) , (b , H))
  where
   f : ∥ Σ x ꞉ X , ∥ P x ∥[ n ] ∥[ n ] → ∥ Σ x ꞉ X , P x ∥[ n ]
   f = ∥∥ₙ-rec ∥∥ₙ-is-truncated
               (uncurry (λ x → ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ p → ∣ (x , p) ∣[ n ])))
   b : ∥ Σ x ꞉ X , P x ∥[ n ] → ∥ Σ x ꞉ X , ∥ P x ∥[ n ] ∥[ n ]
   b = ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ (x , p) → ∣ (x , ∣ p ∣[ n ]) ∣[ n ])
   G : f ∘ b ∼ id
   G = ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated (f ∘ b) id G'
    where
     G' : (z : Σ x ꞉ X , P x) → f (b ∣ z ∣[ n ]) ＝ ∣ z ∣[ n ]
     G' (x , p) = f (b ∣ (x , p) ∣[ n ])       ＝⟨ I ⟩
                  f ∣ (x , ∣ p ∣[ n ]) ∣[ n ] ＝⟨ II ⟩
                  f' (x , ∣ p ∣[ n ])          ＝⟨ III ⟩
                  ∣ (x , p) ∣[ n ]             ∎
      where
       I = ap f (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated
                              (λ (x , p) → ∣ (x , ∣ p ∣[ n ]) ∣[ n ])
                              (x , p))
       f' = uncurry (λ x → ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ p → ∣ x , p ∣[ n ]))
       II = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated f' (x , ∣ p ∣[ n ])
       III = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ p → ∣ (x , p) ∣[ n ]) p

   H : b ∘ f ∼ id
   H = ∥∥ₙ-uniqueness ∥∥ₙ-is-truncated (b ∘ f) id H'
    where
     H'' : (x : X)
         → (p : P x)
         → b (f ∣ (x , ∣ p ∣[ n ]) ∣[ n ]) ＝ ∣ (x , ∣ p ∣[ n ]) ∣[ n ]
     H'' x p = b (f ∣ (x , ∣ p ∣[ n ]) ∣[ n ]) ＝⟨ I ⟩
               b (f' (x , ∣ p ∣[ n ]))         ＝⟨ II ⟩
               b ∣ (x , p) ∣[ n ]              ＝⟨ III ⟩
               ∣ (x , ∣ p ∣[ n ]) ∣[ n ]       ∎
      where
       f' = uncurry (λ x → ∥∥ₙ-rec ∥∥ₙ-is-truncated (λ p → ∣ x , p ∣[ n ]))
       I = ap b (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated f' (x , ∣ p ∣[ n ]))
       II = ap b (∥∥ₙ-rec-comp ∥∥ₙ-is-truncated (λ p → ∣ x , p ∣[ n ]) p)
       III = ∥∥ₙ-rec-comp ∥∥ₙ-is-truncated
                          (λ (x , p) → ∣ (x , ∣ p ∣[ n ]) ∣[ n ])
                          (x , p)
     H''' : (x : X)
          → (p : ∥ P x ∥[ n ])
          → b (f ∣ (x , p) ∣[ n ]) ＝ ∣ (x , p) ∣[ n ]
     H''' x = ∥∥ₙ-ind (λ p → truncation-levels-closed-under-Id ∥∥ₙ-is-truncated
                              (b (f ∣ (x , p) ∣[ n ])) ∣ (x , p) ∣[ n ])
                      (H'' x)
     H' : (z : Σ x ꞉ X , ∥ P x ∥[ n ]) → b (f ∣ z ∣[ n ]) ＝ ∣ z ∣[ n ]
     H' (x , p) = H''' x p

\end{code}

We now define an equivalence that characterizes the truncated identity type
under the assumption of univalence. The following proof was inspired by
the agda unimath library -- although the development there is more thorough --
for details see: https://unimath.github.io/agda-unimath/foundation.truncations.

\begin{code}

 canonical-identity-trunc-map : {X : 𝓤 ̇ } {x x' : X} {n : ℕ₋₂}
                              → ∥ x ＝ x' ∥[ n ]
                              → ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]
 canonical-identity-trunc-map {𝓤} {X} {x} {x'} {n} =
  ∥∥ₙ-rec (∥∥ₙ-is-truncated ∣ x ∣[ n + 1 ] ∣ x' ∣[ n + 1 ])
          (ap ∣_∣[ n + 1 ])

 module _ {X : 𝓤 ̇ } {n : ℕ₋₂}
          (ua : is-univalent 𝓤) (x : X)
           where

  trunc-id-family : ∥ X ∥[ n + 1 ] → 𝕋 n 𝓤
  trunc-id-family = ∥∥ₙ-rec (𝕋-is-of-next-truncation-level ua)
                            (λ x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-is-truncated))

  trunc-id-family-type : ∥ X ∥[ n + 1 ] → 𝓤 ̇
  trunc-id-family-type = pr₁ ∘ trunc-id-family

  trunc-id-family-level : (v : ∥ X ∥[ n + 1 ])
                        → (trunc-id-family-type v) is n truncated
  trunc-id-family-level = pr₂ ∘ trunc-id-family

  trunc-id-family-computes : (x' : X)
                           → trunc-id-family-type ∣ x' ∣[ n + 1 ]
                           ＝ ∥ x ＝ x' ∥[ n ]
  trunc-id-family-computes x' =
    ap pr₁ (∥∥ₙ-rec-comp (𝕋-is-of-next-truncation-level ua)
                         (λ x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-is-truncated))
                         x')

  trunc-id-forward-map : (x' : X)
                       → trunc-id-family-type ∣ x' ∣[ n + 1 ]
                       → ∥ x ＝ x' ∥[ n ]
  trunc-id-forward-map x' = transport id (trunc-id-family-computes x')

  trunc-id-backward-map : (x' : X)
                        → ∥ x ＝ x' ∥[ n ]
                        → trunc-id-family-type ∣ x' ∣[ n + 1 ]
  trunc-id-backward-map x' = transport⁻¹ id (trunc-id-family-computes x')

  trunc-id-back-is-retraction
   : (x' : X)
   → trunc-id-backward-map x' ∘ trunc-id-forward-map x' ∼ id
  trunc-id-back-is-retraction x' q =
   forth-and-back-transport (trunc-id-family-computes x')

  refl-trunc-id-family : trunc-id-family-type ∣ x ∣[ n + 1 ]
  refl-trunc-id-family = trunc-id-backward-map x ∣ refl ∣[ n ]

  identity-on-trunc-to-family : (v : ∥ X ∥[ n + 1 ])
                              → ∣ x ∣[ n + 1 ] ＝ v
                              → trunc-id-family-type v
  identity-on-trunc-to-family .(∣ x ∣[ n + 1 ]) refl = refl-trunc-id-family

  trunc-id-family-is-identity-system : is-contr (Σ trunc-id-family-type)
  trunc-id-family-is-identity-system =
   ((∣ x ∣[ n + 1 ] , refl-trunc-id-family) , trunc-id-fam-is-central)
   where
    I : (x' : X) (p : x ＝ x')
      → (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
       ＝[ Σ trunc-id-family-type ]
        (∣ x' ∣[ n + 1 ] , trunc-id-backward-map x' ∣ p ∣[ n ])
    I x' refl = refl

    II : (x' : X) (q' : ∥ x ＝ x' ∥[ n ])
       → (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
        ＝[ Σ trunc-id-family-type ]
         (∣ x' ∣[ n + 1 ] , trunc-id-backward-map x' q')
    II x' = ∥∥ₙ-ind (λ s → truncated-types-closed-under-Σ
                            trunc-id-family-type
                            ∥∥ₙ-is-truncated
                            (λ v → truncation-levels-are-upper-closed
                                    (trunc-id-family-level v))
                            (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
                            (∣ x' ∣[ n + 1 ] , trunc-id-backward-map x' s))
                      (I x')

    III : (x' : X) (q : trunc-id-family-type ∣ x' ∣[ n + 1 ])
        → (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
          ＝[ Σ trunc-id-family-type ]
          (∣ x' ∣[ n + 1 ] , q)
    III x' q = transport (λ - → (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
                                ＝[ Σ trunc-id-family-type ]
                                (∣ x' ∣[ n + 1 ] , -))
                         (trunc-id-back-is-retraction x' q)
                         (II x' (trunc-id-forward-map x' q))

    IV : (v : ∥ X ∥[ n + 1 ]) (q : trunc-id-family-type v)
       → (∣ x ∣[ n + 1 ] , refl-trunc-id-family) ＝ (v , q)
    IV =
     ∥∥ₙ-ind
      (λ s → truncated-types-closed-under-Π
              (λ q → (∣ x ∣[ n + 1 ] , refl-trunc-id-family) ＝ (s , q))
              (λ q → truncated-types-closed-under-Σ
                      trunc-id-family-type
                       (truncation-levels-are-upper-closed ∥∥ₙ-is-truncated)
                       (λ v → truncation-levels-are-upper-closed
                               (truncation-levels-are-upper-closed
                                 (trunc-id-family-level v)))
                       (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
                       (s , q)))
              III

    trunc-id-fam-is-central : is-central (Σ trunc-id-family-type)
                                         (∣ x ∣[ n + 1 ] , refl-trunc-id-family)
    trunc-id-fam-is-central (v , q) = IV v q

 trunc-identity-characterization : {X : 𝓤 ̇ } {n : ℕ₋₂}
                                 → (ua : is-univalent 𝓤)
                                 → (x : X) (v : ∥ X ∥[ n + 1 ])
                                 → (∣ x ∣[ n + 1 ] ＝ v)
                                 ≃ trunc-id-family-type ua x v
 trunc-identity-characterization {𝓤} {X} {n} ua x v =
  (identity-on-trunc-to-family ua x v ,
   Yoneda-Theorem-forth ∣ x ∣[ n + 1 ]
    (identity-on-trunc-to-family ua x)
    (trunc-id-family-is-identity-system ua x) v)

 eliminated-trunc-identity-char : {X : 𝓤 ̇ } {x x' : X} {n : ℕ₋₂}
                                → (ua : is-univalent 𝓤)
                                → ∥ x ＝ x' ∥[ n ]
                                ≃ (∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ])
 eliminated-trunc-identity-char {𝓤} {X} {x} {x'} {n} ua =
  ≃-comp (idtoeq ∥ x ＝ x' ∥[ n ]
                 (trunc-id-family-type ua x ∣ x' ∣[ n + 1 ])
                 (trunc-id-family-computes ua x x' ⁻¹))
         (≃-sym (trunc-identity-characterization ua x ∣ x' ∣[ n + 1 ]))

 forth-trunc-id-char : {X : 𝓤 ̇ } {x x' : X} {n : ℕ₋₂}
                     → (ua : is-univalent 𝓤)
                     → ∥ x ＝ x' ∥[ n ]
                     → (∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ])
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
