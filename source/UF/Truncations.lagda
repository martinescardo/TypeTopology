Ian Ray, 07/23/2024

Using records we define the general truncation of a type which will include
constructor, induction principle and a computation rule (up to identification).
We then proceed to develop some machinary derived from the induction principle
and explore relationships, closure properties and finally characterize the
identity type of truncations. Note that we explicitly include the assumption of
univalence for the characterization of idenity types but not globally as many
important notion hold in the absence of univalence.

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
open import UF.Yoneda
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order

module UF.Truncations (fe : Fun-Ext)
                      (pt : propositional-truncations-exist)
                       where

open import UF.H-Levels fe 

\end{code}

We define the notion of a k-truncation using record types.

\begin{code}

record H-level-truncations-exist : 𝓤ω where
 field
  ∥_∥[_] : {𝓤 : Universe} → 𝓤 ̇ → ℕ → 𝓤 ̇
  ∥∥ₙ-h-level : {𝓤 : Universe} {X : 𝓤 ̇ } (n : ℕ) → ∥ X ∥[ n ] is-of-hlevel n
  ∣_∣[_] :  {𝓤 : Universe} {X : 𝓤 ̇ } → X → (n : ℕ) → ∥ X ∥[ n ]
  ∥∥ₙ-ind : {X : 𝓤 ̇ } {n : ℕ} {P : ∥ X ∥[ n ] → 𝓥 ̇}
          → ((s : ∥ X ∥[ n ]) → (P s) is-of-hlevel n)
          → ((x : X) → P (∣ x ∣[ n ]))
          → (s : ∥ X ∥[ n ]) → P s
  ∥∥ₙ-ind-comp : {X : 𝓤 ̇ } {n : ℕ} {P : ∥ X ∥[ n ] → 𝓥 ̇ }
               → (m : (s : ∥ X ∥[ n ]) → (P s) is-of-hlevel n)
               → (g : (x : X) → P (∣ x ∣[ n ]))
               → (x : X) → ∥∥ₙ-ind m g (∣ x ∣[ n ]) ＝ g x
 infix 0 ∥_∥[_]
 infix 0 ∣_∣[_]

\end{code}

We now add some some machinary that will prove usefule: truncation recursion
and uniqueness, indduction/recursion for two arguments and all associated
computation rules.

\begin{code}

module GeneralTruncations
        (te : H-level-truncations-exist)
       where

 open H-level-truncations-exist te

 ∥∥ₙ-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
         → Y is-of-hlevel n
         → (X → Y)
         → ∥ X ∥[ n ] → Y
 ∥∥ₙ-rec {𝓤} {𝓥} {X} {Y} {n} Y-h-level f s =
  ∥∥ₙ-ind (λ - → Y-h-level) f s

 ∥∥ₙ-uniqueness : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                → Y is-of-hlevel n
                → (f g : ∥ X ∥[ n ] → Y)
                → ((x : X) → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                → (s : ∥ X ∥[ n ]) → f s ＝ g s
 ∥∥ₙ-uniqueness {𝓤} {𝓥} {X} {Y} {n} Y-h-lev f g H =
  ∥∥ₙ-ind (λ s → hlevels-are-closed-under-id n Y-h-lev (f s) (g s)) H

 ∥∥ₙ-rec-comp : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
              → (m : Y is-of-hlevel n)
              → (g : X → Y)
              → (x : X) → ∥∥ₙ-rec m g ∣ x ∣[ n ] ＝ g x
 ∥∥ₙ-rec-comp m g = ∥∥ₙ-ind-comp (λ - → m) g

 ∥∥ₙ-rec₂ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
          → Z is-of-hlevel n
          → (X → Y → Z)
          → ∥ X ∥[ n ] → ∥ Y ∥[ n ] → Z
 ∥∥ₙ-rec₂ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} Z-h-level g =
  ∥∥ₙ-rec (hlevel-closed-under-→ n Z-h-level)
          (λ x → ∥∥ₙ-rec Z-h-level (λ y → g x y))

 ∥∥ₙ-rec-comp₂ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
               → (m : Z is-of-hlevel n)
               → (g : X → Y → Z)
               → (x : X) → (y : Y)
               → ∥∥ₙ-rec₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
 ∥∥ₙ-rec-comp₂ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} m g x y =
  ∥∥ₙ-rec₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ I ⟩
  ∥∥ₙ-rec m (λ y → g x y) ∣ y ∣[ n ] ＝⟨ ∥∥ₙ-rec-comp m (λ y → g x y) y ⟩
  g x y                              ∎
   where
    I = happly (∥∥ₙ-rec-comp (hlevel-closed-under-→ n m)
                (λ x → ∥∥ₙ-rec m (λ y → g x y)) x)
               ∣ y ∣[ n ]

 abstract
  ∥∥ₙ-ind₂ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
             {P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇ } 
           → ((u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ])
           → (P u v) is-of-hlevel n)
           → ((x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
           → (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → P u v
  ∥∥ₙ-ind₂ {𝓤} {𝓥} {𝓦} {X} {Y} {n} {P} P-h-level f =
   ∥∥ₙ-ind (λ u → hlevel-closed-under-Π n (P u) (λ v → P-h-level u v))
           (λ x → ∥∥ₙ-ind (λ v → P-h-level ∣ x ∣[ n ] v) (λ y → f x y))

  ∥∥ₙ-ind-comp₂ : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                  {P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇ } 
                → (m : (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ])
                → (P u v) is-of-hlevel n)
                → (g : (x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
                → (x : X) → (y : Y)
                → ∥∥ₙ-ind₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
  ∥∥ₙ-ind-comp₂ {𝓤} {𝓥} {𝓦} {X} {Y} {n} {P} m g x y =
   ∥∥ₙ-ind₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ]                        ＝⟨ I ⟩
   ∥∥ₙ-ind (λ v → m ∣ x ∣[ n ] v) (λ y' → g x y') ∣ y ∣[ n ] ＝⟨ II ⟩
   g x y                                                     ∎
    where
     I : ∥∥ₙ-ind₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ]
         ＝ ∥∥ₙ-ind (λ v → m ∣ x ∣[ n ] v) (λ y' → g x y') ∣ y ∣[ n ]
     I = happly
          (∥∥ₙ-ind-comp (λ u → hlevel-closed-under-Π n (P u) (λ v → m u v))
           (λ x' → ∥∥ₙ-ind (λ v → m ∣ x' ∣[ n ] v) (λ y' → g x' y')) x)
          ∣ y ∣[ n ]
     II : ∥∥ₙ-ind (λ v → m ∣ x ∣[ n ] v) (λ y' → g x y') ∣ y ∣[ n ]
          ＝ g x y
     II = ∥∥ₙ-ind-comp (λ v → m ∣ x ∣[ n ] v) (λ y' → g x y') y

\end{code}

We develop useful results related to general truncations. We characterize the
first couple levels of truncation (TODO: three-hlevel is a groupoid). 

\begin{code}

 zero-trunc-is-contr : {X : 𝓤 ̇ } → is-contr (∥ X ∥[ zero ])
 zero-trunc-is-contr = ∥∥ₙ-h-level zero

 one-trunc-is-prop : {X : 𝓤 ̇ } → is-prop (∥ X ∥[ succ zero ])
 one-trunc-is-prop = is-prop'-implies-is-prop (∥∥ₙ-h-level (succ zero))

 two-trunc-is-set : {X : 𝓤 ̇ } → is-set (∥ X ∥[ succ (succ zero) ])
 two-trunc-is-set {𝓤} {X} {x} {y} =
  is-prop'-implies-is-prop (∥∥ₙ-h-level (succ (succ zero)) x y)

\end{code}

We demonstrate the equivalence of one-truncation and propositional truncation:
  ∥ X ∥₁ ≃ ∥ X ∥

\begin{code}

 open propositional-truncations-exist pt

 one-trunc-to-prop-trunc : {X : 𝓤 ̇} → ∥ X ∥[ 1 ] → ∥ X ∥
 one-trunc-to-prop-trunc = ∥∥ₙ-rec (is-prop-implies-is-prop' ∥∥-is-prop) ∣_∣

 prop-trunc-to-one-trunc : {X : 𝓤 ̇} → ∥ X ∥ → ∥ X ∥[ 1 ]
 prop-trunc-to-one-trunc = ∥∥-rec one-trunc-is-prop (λ x → ∣ x ∣[ 1 ])

 one-trunc-≃-prop-trunc : {X : 𝓤 ̇}
                        → (∥ X ∥[ 1 ]) ≃ ∥ X ∥
 one-trunc-≃-prop-trunc {𝓤} {X} =
  logically-equivalent-props-are-equivalent one-trunc-is-prop ∥∥-is-prop
                                            one-trunc-to-prop-trunc
                                            prop-trunc-to-one-trunc

\end{code}

We provide the canonical predecessor map and show truncations are closed under
equivalence and succesive applications of truncation (TODO: other closure
conditions (?)).

\begin{code}
 canonical-pred-map : {X : 𝓤 ̇} {n : ℕ}
                    → ∥ X ∥[ succ n ] → ∥ X ∥[ n ]
 canonical-pred-map {𝓤} {X} {n} x =
  ∥∥ₙ-rec (hlevels-are-upper-closed n (∥ X ∥[ n ]) (∥∥ₙ-h-level n))
          (λ x → ∣ x ∣[ n ]) x

 canonical-pred-map-comp : {X : 𝓤 ̇} {n : ℕ} (x : X)
                         → canonical-pred-map (∣ x ∣[ succ n ]) ＝ (∣ x ∣[ n ])
 canonical-pred-map-comp {𝓤} {X} {n} x =
  ∥∥ₙ-rec-comp (hlevels-are-upper-closed n (∥ X ∥[ n ]) (∥∥ₙ-h-level n))
               (λ _ → ∣ _ ∣[ n ]) x

 truncation-closed-under-equiv : {𝓤 𝓥 : Universe} {n : ℕ} {X : 𝓤 ̇} {Y : 𝓥 ̇}
                               → X ≃ Y
                               → (∥ X ∥[ n ]) ≃ (∥ Y ∥[ n ])
 truncation-closed-under-equiv {𝓤} {𝓥} {n} {X} {Y} e = (f , (b , G) , (b , H))
  where
   f : ∥ X ∥[ n ] → ∥ Y ∥[ n ]
   f = ∥∥ₙ-rec (∥∥ₙ-h-level n) (λ x → ∣ (⌜ e ⌝ x) ∣[ n ])
   b : ∥ Y ∥[ n ] → ∥ X ∥[ n ]
   b = ∥∥ₙ-rec (∥∥ₙ-h-level n) (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ])
   H : b ∘ f ∼ id
   H = ∥∥ₙ-ind (λ s → hlevels-are-closed-under-id n (∥∥ₙ-h-level n) (b (f s)) s)
               H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))           ＝⟨ I ⟩
            b (∣ ⌜ e ⌝ x ∣[ n ])         ＝⟨ II ⟩
            (∣ ⌜ e ⌝⁻¹ (⌜ e ⌝ x) ∣[ n ]) ＝⟨ III ⟩
            (∣ x ∣[ n ])                 ∎
      where
       I = ap b (∥∥ₙ-rec-comp (∥∥ₙ-h-level n) (λ x → ∣ (⌜ e ⌝ x) ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp (∥∥ₙ-h-level n) (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) (⌜ e ⌝ x)
       III = ap (λ x → ∣ x ∣[ n ]) (inverses-are-retractions' e x)
   G : f ∘ b ∼ id
   G = ∥∥ₙ-ind (λ s → hlevels-are-closed-under-id n (∥∥ₙ-h-level n) (f (b s)) s)
               G'
    where
     G' : (y : Y) → f (b (∣ y ∣[ n ])) ＝ (∣ y ∣[ n ])
     G' y = f (b (∣ y ∣[ n ]))           ＝⟨ I ⟩
            f (∣ (⌜ e ⌝⁻¹ y) ∣[ n ])     ＝⟨ II ⟩
            (∣ ⌜ e ⌝ (⌜ e ⌝⁻¹ y) ∣[ n ]) ＝⟨ III ⟩
            (∣ y ∣[ n ])                 ∎
      where
       I = ap f (∥∥ₙ-rec-comp (∥∥ₙ-h-level n) (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) y)
       II = ∥∥ₙ-rec-comp (∥∥ₙ-h-level n) (λ x → ∣ ⌜ e ⌝ x ∣[ n ]) (⌜ e ⌝⁻¹ y)
       III = ap (λ y → ∣ y ∣[ n ]) (inverses-are-sections' e y)

 succesive-truncations-equiv : (X : 𝓤 ̇) (n : ℕ)
                             → (∥ X ∥[ n ]) ≃ (∥ (∥ X ∥[ succ n ]) ∥[ n ])
 succesive-truncations-equiv X n = (f , (b , G) , (b , H))
  where
   f : (∥ X ∥[ n ]) → (∥ (∥ X ∥[ succ n ]) ∥[ n ])
   f = ∥∥ₙ-rec (∥∥ₙ-h-level n) (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ])
   b : (∥ (∥ X ∥[ succ n ]) ∥[ n ]) → (∥ X ∥[ n ])
   b = ∥∥ₙ-rec (∥∥ₙ-h-level n) (canonical-pred-map)
   G : f ∘ b ∼ id
   G = ∥∥ₙ-ind (λ s → hlevels-are-closed-under-id n (∥∥ₙ-h-level n) (f (b s)) s)
               (∥∥ₙ-ind (λ t → hlevels-are-closed-under-id n
                                (hlevels-are-closed-under-id n
                                (∥∥ₙ-h-level n) (f (b (∣ t ∣[ n ])))
                                (∣ t ∣[ n ])))
                         G')
    where
     G' : (x : X)
        → f (b (∣ ∣ x ∣[ succ n ] ∣[ n ])) ＝ (∣ ∣ x ∣[ succ n ] ∣[ n ])
     G' x = f (b (∣ ∣ x ∣[ succ n ] ∣[ n ]))         ＝⟨ I ⟩
            f (canonical-pred-map (∣ x ∣[ succ n ])) ＝⟨ II ⟩
            f (∣ x ∣[ n ])                           ＝⟨ III ⟩
            (∣ ∣ x ∣[ succ n ] ∣[ n ])               ∎
      where
       I = ap f (∥∥ₙ-rec-comp (∥∥ₙ-h-level n) canonical-pred-map
                              (∣ x ∣[ succ n ]))
       II = ap f (canonical-pred-map-comp x)
       III = ∥∥ₙ-rec-comp (∥∥ₙ-h-level n) (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ]) x
   H : b ∘ f ∼ id
   H = ∥∥ₙ-ind (λ s → hlevels-are-closed-under-id n (∥∥ₙ-h-level n) (b (f s)) s)
               H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))                   ＝⟨ I ⟩
            b (∣ ∣ x ∣[ succ n ] ∣[ n ])         ＝⟨ II ⟩
            canonical-pred-map (∣ x ∣[ succ n ]) ＝⟨ canonical-pred-map-comp x ⟩
            (∣ x ∣[ n ])                         ∎
      where
       I = ap b (∥∥ₙ-rec-comp (∥∥ₙ-h-level n) (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp (∥∥ₙ-h-level n) canonical-pred-map (∣ x ∣[ succ n ])

\end{code}

We now define an equivalence that characterizes the truncated identity type
under the assumption of univalence.

\begin{code}

 canonical-identity-trunc-map : {𝓤 : Universe} {X : 𝓤 ̇} {x x' : X} {n : ℕ}
                              → ∥ x ＝ x' ∥[ n ]
                              → ∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ]
 canonical-identity-trunc-map {𝓤} {X} {x} {x'} {n} =
  ∥∥ₙ-rec (∥∥ₙ-h-level (succ n) ∣ x ∣[ succ n ] ∣ x' ∣[ succ n ])
          (ap (λ x → ∣ x ∣[ (succ n) ]))

 module _ {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
          (ua : Univalence) (x : X) 
           where

  trunc-id-family : ∥ X ∥[ succ n ] → ℍ n 𝓤
  trunc-id-family = ∥∥ₙ-rec {𝓤} {𝓤 ⁺} {X} {ℍ n 𝓤} {succ n}
                            (ℍ-is-of-next-hlevel n 𝓤 (ua 𝓤))
                            (λ x' → (∥ x ＝ x' ∥[ n ] , (∥∥ₙ-h-level n)))

  trunc-id-family-type : ∥ X ∥[ succ n ] → 𝓤 ̇
  trunc-id-family-type = pr₁ ∘ trunc-id-family

  trunc-id-family-level : (v : ∥ X ∥[ succ n ])
                        → (trunc-id-family-type v) is-of-hlevel n
  trunc-id-family-level = pr₂ ∘ trunc-id-family

  trunc-id-family-computes : (x' : X)
                           → trunc-id-family-type ∣ x' ∣[ succ n ]
                             ＝ ∥ x ＝ x' ∥[ n ]
  trunc-id-family-computes x' =
    ap pr₁ (∥∥ₙ-rec-comp (ℍ-is-of-next-hlevel n 𝓤 (ua 𝓤))
                         (λ x' → (∥ x ＝ x' ∥[ n ] , (∥∥ₙ-h-level n)))
                         x')

  trunc-id-forward-map : (x' : X)
                       → trunc-id-family-type ∣ x' ∣[ succ n ]
                       → ∥ x ＝ x' ∥[ n ]
  trunc-id-forward-map x' = transport id (trunc-id-family-computes x')

  trunc-id-backward-map : (x' : X)
                        → ∥ x ＝ x' ∥[ n ]
                        → trunc-id-family-type ∣ x' ∣[ succ n ]
  trunc-id-backward-map x' = transport⁻¹ id (trunc-id-family-computes x')

  trunc-id-back-is-retraction : (x' : X)
                              → trunc-id-backward-map x' ∘ trunc-id-forward-map x'
                               ∼ id
  trunc-id-back-is-retraction x' q =
   forth-and-back-transport (trunc-id-family-computes x')

  refl-trunc-id-family : trunc-id-family-type ∣ x ∣[ succ n ]
  refl-trunc-id-family = trunc-id-backward-map x ∣ refl ∣[ n ]

  identity-on-trunc-to-family : (v : ∥ X ∥[ succ n ])
                              → (∣ x ∣[ succ n ] ＝ v)
                              → trunc-id-family-type v
  identity-on-trunc-to-family .(∣ x ∣[ succ n ]) refl = refl-trunc-id-family

  trunc-id-family-is-identity-system : is-contr (Σ (trunc-id-family-type))
  trunc-id-family-is-identity-system =
   ((∣ x ∣[ succ n ] , refl-trunc-id-family) , center-Q)
   where
    I : (x' : X) (p : x ＝ x')
      → (∣ x ∣[ succ n ] , refl-trunc-id-family)
       ＝[ Σ (trunc-id-family-type) ]
        (∣ x' ∣[ succ n ] , trunc-id-backward-map x' ∣ p ∣[ n ])
    I x' refl = refl
    II : (x' : X) (q' : ∥ x ＝ x' ∥[ n ])
       → (∣ x ∣[ succ n ] , refl-trunc-id-family)
        ＝[ Σ (trunc-id-family-type) ]
         (∣ x' ∣[ succ n ] , trunc-id-backward-map x' q')
    II x' = ∥∥ₙ-ind (λ s → hlevel-closed-under-Σ (succ n)
                            trunc-id-family-type (∥∥ₙ-h-level (succ n))
                            (λ v → hlevels-are-upper-closed n
                                    (trunc-id-family-type v)
                                    (trunc-id-family-level v))
                            (∣ x ∣[ succ n ] , refl-trunc-id-family)
                            (∣ x' ∣[ succ n ] , trunc-id-backward-map x' s))
                     (I x')
    III : (x' : X) (q : trunc-id-family-type ∣ x' ∣[ succ n ])
        → (∣ x ∣[ succ n ] , refl-trunc-id-family)
          ＝[ Σ (trunc-id-family-type) ]
          (∣ x' ∣[ succ n ] , q)
    III x' q = transport (λ - → (∣ x ∣[ succ n ] , refl-trunc-id-family)
                                ＝[ Σ (trunc-id-family-type) ]
                                (∣ x' ∣[ succ n ] , -))
                         (trunc-id-back-is-retraction x' q)
                         (II x' (trunc-id-forward-map x' q))
    IV : (v : ∥ X ∥[ succ n ]) (q : trunc-id-family-type v)
       → (∣ x ∣[ succ n ] , refl-trunc-id-family) ＝ (v , q)
    IV =
     ∥∥ₙ-ind (λ s → hlevel-closed-under-Π (succ n) 
                     (λ q → (∣ x ∣[ succ n ] , refl-trunc-id-family) ＝ (s , q))
                     (λ q → hlevel-closed-under-Σ (succ (succ n)) 
                             trunc-id-family-type (hlevels-are-upper-closed
                                                   (succ n) ∥ X ∥[ succ n ]
                                                   (∥∥ₙ-h-level (succ n)))
                                                  (λ v → hlevels-are-upper-closed
                                                    (succ n)
                                                    (trunc-id-family-type v)
                                                    (hlevels-are-upper-closed n
                                                     (trunc-id-family-type v)
                                                     (trunc-id-family-level v)))
                                                  (∣ x ∣[ succ n ]
                                                   , refl-trunc-id-family)
                                                  (s , q)))
             III
    center-Q : is-central (Σ (trunc-id-family-type))
                          (∣ x ∣[ succ n ] , refl-trunc-id-family)
    center-Q (v , q) = IV v q 

 trunc-identity-characterization : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
                                 → (ua : Univalence)
                                 → (x : X) (v : ∥ X ∥[ succ n ])
                                 → (∣ x ∣[ succ n ] ＝ v)
                                 ≃ trunc-id-family-type ua x v
 trunc-identity-characterization {𝓤} {X} {n} ua x v =
  (identity-on-trunc-to-family ua x v , Yoneda-Theorem-forth ∣ x ∣[ succ n ]
                                      (identity-on-trunc-to-family ua x)
                                      (trunc-id-family-is-identity-system ua x) v)

 eliminated-trunc-identity-char : {𝓤 : Universe} {X : 𝓤 ̇} {x x' : X} {n : ℕ}
                                → (ua : Univalence)
                                → ∥ x ＝ x' ∥[ n ]
                                ≃ (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ])
 eliminated-trunc-identity-char {𝓤} {X} {x} {x'} {n} ua =
  ≃-comp (idtoeq ∥ x ＝ x' ∥[ n ] (trunc-id-family-type ua x ∣ x' ∣[ succ n ])
                 (trunc-id-family-computes ua x x' ⁻¹))
         (≃-sym (trunc-identity-characterization ua x ∣ x' ∣[ succ n ]))

 forth-trunc-id-char : {𝓤 : Universe} {X : 𝓤 ̇} {x x' : X} {n : ℕ}
                     → (ua : Univalence)
                     → ∥ x ＝ x' ∥[ n ]
                     → (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ])
 forth-trunc-id-char ua = ⌜ eliminated-trunc-identity-char ua ⌝

\end{code}
