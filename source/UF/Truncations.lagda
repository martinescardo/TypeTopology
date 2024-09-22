Ian Ray, 23 July 2024

Minor modifications by Tom de Jong on 4 September 2024

Using records we define the general truncation of a type which will include
a constructor, an induction principle and a computation rule
(up to identification). We then proceed to develop some machinery derived from
the induction principle and explore relationships, closure properties and finally
characterize the identity type of truncations. Note that we explicitly include
the assumption of univalence for the characterization of idenity types but not
globally as many important properties hold in the absence of univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Truncations (fe : Fun-Ext)
                       where

open import MLTT.Spartan

open import UF.Base
open import UF.Equiv
open import UF.H-Levels fe
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Univalence
open import UF.Yoneda

\end{code}

We define the notion of a n-truncation using record types.

\begin{code}

record H-level-truncations-exist : 𝓤ω where
 field
  ∥_∥[_] : 𝓤 ̇ → ℕ → 𝓤 ̇
  ∥∥ₙ-hlevel : {X : 𝓤 ̇ } {n : ℕ} → ∥ X ∥[ n ] is-of-hlevel n
  ∣_∣[_] :  {X : 𝓤 ̇ } → X → (n : ℕ) → ∥ X ∥[ n ]
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

We now add some some machinery that will prove useful: truncation recursion
and uniqueness, induction/recursion for two arguments and all associated
computation rules.

\begin{code}

 ∥∥ₙ-rec : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
         → Y is-of-hlevel n
         → (X → Y)
         → ∥ X ∥[ n ] → Y
 ∥∥ₙ-rec Y-h-level f s = ∥∥ₙ-ind (λ - → Y-h-level) f s

 ∥∥ₙ-uniqueness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                → Y is-of-hlevel n
                → (f g : ∥ X ∥[ n ] → Y)
                → ((x : X) → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                → f ∼ g
 ∥∥ₙ-uniqueness Y-h-lev f g =
  ∥∥ₙ-ind (λ s → hlevels-are-closed-under-id Y-h-lev (f s) (g s))

 ∥∥ₙ-rec-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
              → (m : Y is-of-hlevel n)
              → (g : X → Y)
              → (x : X) → ∥∥ₙ-rec m g ∣ x ∣[ n ] ＝ g x
 ∥∥ₙ-rec-comp m = ∥∥ₙ-ind-comp (λ - → m)

 ∥∥ₙ-rec₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
          → Z is-of-hlevel n
          → (X → Y → Z)
          → ∥ X ∥[ n ] → ∥ Y ∥[ n ] → Z
 ∥∥ₙ-rec₂ Z-h-level g = ∥∥ₙ-rec (hlevel-closed-under-→ Z-h-level)
                                (λ x → ∥∥ₙ-rec Z-h-level (g x))

 ∥∥ₙ-rec-comp₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
               → (m : Z is-of-hlevel n)
               → (g : X → Y → Z)
               → (x : X) → (y : Y)
               → ∥∥ₙ-rec₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
 ∥∥ₙ-rec-comp₂ {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} m g x y =
  ∥∥ₙ-rec₂ m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ I ⟩
  ∥∥ₙ-rec m (g x) ∣ y ∣[ n ] ＝⟨ ∥∥ₙ-rec-comp m (g x) y ⟩
  g x y                              ∎
   where
    I = happly (∥∥ₙ-rec-comp (hlevel-closed-under-→ m)
                (λ x → ∥∥ₙ-rec m (g x)) x)
               ∣ y ∣[ n ]

 abstract
  ∥∥ₙ-ind₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
           → (P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇)
           → ((u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → (P u v) is-of-hlevel n)
           → ((x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
           → (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → P u v
  ∥∥ₙ-ind₂ {𝓤} {𝓥} {𝓦} {X} {Y} {n} P P-h-level f =
   ∥∥ₙ-ind (λ u → hlevel-closed-under-Π (P u) (P-h-level u))
           (λ x → ∥∥ₙ-ind (λ v → P-h-level ∣ x ∣[ n ] v) (f x))
  ∥∥ₙ-ind-comp₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                → (P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇)
                → (m : (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ])
                 → (P u v) is-of-hlevel n)
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
          (∥∥ₙ-ind-comp (λ u → hlevel-closed-under-Π (P u) (m u))
           (λ x' → ∥∥ₙ-ind (m ∣ x' ∣[ n ]) (g x')) x)
          ∣ y ∣[ n ]
     II : ∥∥ₙ-ind (m ∣ x ∣[ n ]) (g x) ∣ y ∣[ n ] ＝ g x y
     II = ∥∥ₙ-ind-comp (m ∣ x ∣[ n ]) (g x) y

\end{code}

We characterize the first couple levels of truncation (TODO: three-hlevel is a
groupoid).

\begin{code}

 zero-trunc-is-contr : {X : 𝓤 ̇ } → is-contr (∥ X ∥[ 0 ])
 zero-trunc-is-contr = ∥∥ₙ-hlevel

 one-trunc-is-prop : {X : 𝓤 ̇ } → is-prop (∥ X ∥[ 1 ])
 one-trunc-is-prop = is-prop'-implies-is-prop ∥∥ₙ-hlevel

 two-trunc-is-set : {X : 𝓤 ̇ } → is-set (∥ X ∥[ 2 ])
 two-trunc-is-set {𝓤} {X} {x} {y} =
  is-prop'-implies-is-prop (∥∥ₙ-hlevel x y)

\end{code}

We demonstrate the equivalence of one-truncation and propositional truncation:
 ∥ X ∥₁ ≃ ∥ X ∥

\begin{code}

 module _ (pt : propositional-truncations-exist)
           where

  open propositional-truncations-exist pt

  one-trunc-to-prop-trunc : {X : 𝓤 ̇} → ∥ X ∥[ 1 ] → ∥ X ∥
  one-trunc-to-prop-trunc = ∥∥ₙ-rec (is-prop-implies-is-prop' ∥∥-is-prop) ∣_∣

  prop-trunc-to-one-trunc : {X : 𝓤 ̇} → ∥ X ∥ → ∥ X ∥[ 1 ]
  prop-trunc-to-one-trunc = ∥∥-rec one-trunc-is-prop (∣_∣[ 1 ])

  one-trunc-≃-prop-trunc : {X : 𝓤 ̇}
                         → (∥ X ∥[ 1 ]) ≃ ∥ X ∥
  one-trunc-≃-prop-trunc =
   logically-equivalent-props-are-equivalent one-trunc-is-prop ∥∥-is-prop
                                             one-trunc-to-prop-trunc
                                             prop-trunc-to-one-trunc

\end{code}

We provide the canonical predecessor map and show truncations are closed under
equivalence and successive applications of truncation (TODO: other closure
conditions (?)).

\begin{code}
 canonical-pred-map : {X : 𝓤 ̇} {n : ℕ}
                    → ∥ X ∥[ succ n ] → ∥ X ∥[ n ]
 canonical-pred-map {𝓤} {X} {n} x =
  ∥∥ₙ-rec (hlevels-are-upper-closed ∥∥ₙ-hlevel)
          (λ x → ∣ x ∣[ n ]) x

 canonical-pred-map-comp : {X : 𝓤 ̇} {n : ℕ} (x : X)
                         → canonical-pred-map (∣ x ∣[ succ n ]) ＝ (∣ x ∣[ n ])
 canonical-pred-map-comp {𝓤} {X} {n} x =
  ∥∥ₙ-rec-comp (hlevels-are-upper-closed ∥∥ₙ-hlevel)
               (λ _ → ∣ _ ∣[ n ]) x

 to-∼-of-maps-with-truncated-domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ}
                                    → (f g : ∥ X ∥[ n ] → Y)
                                    → Y is-of-hlevel n
                                    → ((x : X)
                                          → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                                    → f ∼ g
 to-∼-of-maps-with-truncated-domain f g Y-hlev =
  ∥∥ₙ-ind (λ - → hlevels-are-closed-under-id Y-hlev (f -) (g -))

 to-∼-of-maps-between-truncated-types : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ}
                                      → (f g : ∥ X ∥[ n ] → ∥ Y ∥[ n ])
                                      → ((x : X)
                                            → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                                      → f ∼ g
 to-∼-of-maps-between-truncated-types {𝓤} {𝓥} {X} {Y} {n} f g =
  to-∼-of-maps-with-truncated-domain f g ∥∥ₙ-hlevel

 truncation-closed-under-equiv : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ}
                               → X ≃ Y
                               → ∥ X ∥[ n ] ≃ ∥ Y ∥[ n ]
 truncation-closed-under-equiv {𝓤} {𝓥} {X} {Y} {n} e = (f , (b , G) , (b , H))
  where
   f : ∥ X ∥[ n ] → ∥ Y ∥[ n ]
   f = ∥∥ₙ-rec ∥∥ₙ-hlevel (λ x → ∣ ⌜ e ⌝ x ∣[ n ])
   b : ∥ Y ∥[ n ] → ∥ X ∥[ n ]
   b = ∥∥ₙ-rec ∥∥ₙ-hlevel (λ y → ∣ ⌜ e ⌝⁻¹ y ∣[ n ])
   H : b ∘ f ∼ id
   H = to-∼-of-maps-between-truncated-types (b ∘ f) id H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))           ＝⟨ I ⟩
            b (∣ ⌜ e ⌝ x ∣[ n ])         ＝⟨ II ⟩
            (∣ ⌜ e ⌝⁻¹ (⌜ e ⌝ x) ∣[ n ]) ＝⟨ III ⟩
            (∣ x ∣[ n ])                 ∎
      where
       I = ap b (∥∥ₙ-rec-comp ∥∥ₙ-hlevel (λ x → ∣ (⌜ e ⌝ x) ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-hlevel (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) (⌜ e ⌝ x)
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
       I = ap f (∥∥ₙ-rec-comp ∥∥ₙ-hlevel (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) y)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-hlevel (λ x → ∣ ⌜ e ⌝ x ∣[ n ]) (⌜ e ⌝⁻¹ y)
       III = ap (λ y → ∣ y ∣[ n ]) (inverses-are-sections' e y)

 successive-truncations-equiv : {X : 𝓤 ̇} {n : ℕ}
                              → (∥ X ∥[ n ]) ≃ (∥ (∥ X ∥[ succ n ]) ∥[ n ])
 successive-truncations-equiv {𝓤} {X} {n} = (f , (b , G) , (b , H))
  where
   f : ∥ X ∥[ n ] → ∥ ∥ X ∥[ succ n ] ∥[ n ]
   f = ∥∥ₙ-rec ∥∥ₙ-hlevel (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ])
   b : ∥ ∥ X ∥[ succ n ] ∥[ n ] → ∥ X ∥[ n ]
   b = ∥∥ₙ-rec ∥∥ₙ-hlevel canonical-pred-map
   G : f ∘ b ∼ id
   G = to-∼-of-maps-with-truncated-domain (f ∘ b) id ∥∥ₙ-hlevel
        (to-∼-of-maps-with-truncated-domain
          (f ∘ b ∘ ∣_∣[ n ])
          ∣_∣[ n ]
          (hlevels-are-upper-closed ∥∥ₙ-hlevel)
          G')
    where
     G' : (x : X)
        → f (b (∣ ∣ x ∣[ succ n ] ∣[ n ])) ＝ (∣ ∣ x ∣[ succ n ] ∣[ n ])
     G' x = f (b (∣ ∣ x ∣[ succ n ] ∣[ n ]))         ＝⟨ I ⟩
            f (canonical-pred-map (∣ x ∣[ succ n ])) ＝⟨ II ⟩
            f (∣ x ∣[ n ])                           ＝⟨ III ⟩
            (∣ ∣ x ∣[ succ n ] ∣[ n ])               ∎
      where
       I = ap f (∥∥ₙ-rec-comp ∥∥ₙ-hlevel canonical-pred-map
                              (∣ x ∣[ succ n ]))
       II = ap f (canonical-pred-map-comp x)
       III = ∥∥ₙ-rec-comp ∥∥ₙ-hlevel (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ]) x
   H : b ∘ f ∼ id
   H = to-∼-of-maps-with-truncated-domain (b ∘ f) id ∥∥ₙ-hlevel H'
    where
     H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
     H' x = b (f (∣ x ∣[ n ]))                   ＝⟨ I ⟩
            b (∣ ∣ x ∣[ succ n ] ∣[ n ])         ＝⟨ II ⟩
            canonical-pred-map (∣ x ∣[ succ n ]) ＝⟨ canonical-pred-map-comp x ⟩
            (∣ x ∣[ n ])                         ∎
      where
       I = ap b (∥∥ₙ-rec-comp ∥∥ₙ-hlevel (λ - → ∣ ∣ - ∣[ succ n ] ∣[ n ]) x)
       II = ∥∥ₙ-rec-comp ∥∥ₙ-hlevel canonical-pred-map (∣ x ∣[ succ n ])

\end{code}

We now define an equivalence that characterizes the truncated identity type
under the assumption of univalence. The following proof was inspired by
the agda unimath library -- although the development there is more thorough --
for details see: https://unimath.github.io/agda-unimath/foundation.truncations.

\begin{code}

 canonical-identity-trunc-map : {X : 𝓤 ̇} {x x' : X} {n : ℕ}
                              → ∥ x ＝ x' ∥[ n ]
                              → ∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ]
 canonical-identity-trunc-map {𝓤} {X} {x} {x'} {n} =
  ∥∥ₙ-rec (∥∥ₙ-hlevel ∣ x ∣[ succ n ] ∣ x' ∣[ succ n ])
          (ap (λ x → ∣ x ∣[ (succ n) ]))

 module _ {X : 𝓤 ̇} {n : ℕ}
          (ua : is-univalent 𝓤) (x : X)
           where

  trunc-id-family : ∥ X ∥[ succ n ] → ℍ n 𝓤
  trunc-id-family = ∥∥ₙ-rec (ℍ-is-of-next-hlevel ua)
                            (λ x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-hlevel))

  trunc-id-family-type : ∥ X ∥[ succ n ] → 𝓤 ̇
  trunc-id-family-type = pr₁ ∘ trunc-id-family

  trunc-id-family-level : (v : ∥ X ∥[ succ n ])
                        → (trunc-id-family-type v) is-of-hlevel n
  trunc-id-family-level = pr₂ ∘ trunc-id-family

  trunc-id-family-computes : (x' : X)
                           → trunc-id-family-type ∣ x' ∣[ succ n ]
                             ＝ ∥ x ＝ x' ∥[ n ]
  trunc-id-family-computes x' =
    ap pr₁ (∥∥ₙ-rec-comp (ℍ-is-of-next-hlevel ua)
                         (λ x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-hlevel))
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
    II x' = ∥∥ₙ-ind (λ s → hlevel-closed-under-Σ
                            trunc-id-family-type
                            ∥∥ₙ-hlevel
                            (λ v → hlevels-are-upper-closed
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
      (λ s → hlevel-closed-under-Π
              (λ q → (∣ x ∣[ succ n ] , refl-trunc-id-family) ＝ (s , q))
              (λ q → hlevel-closed-under-Σ
                      trunc-id-family-type
                       (hlevels-are-upper-closed ∥∥ₙ-hlevel)
                       (λ v → hlevels-are-upper-closed
                               (hlevels-are-upper-closed
                                 (trunc-id-family-level v)))
                       (∣ x ∣[ succ n ] , refl-trunc-id-family)
                       (s , q)))
              III

    trunc-id-fam-is-central : is-central (Σ trunc-id-family-type)
                                         (∣ x ∣[ succ n ] , refl-trunc-id-family)
    trunc-id-fam-is-central (v , q) = IV v q

 trunc-identity-characterization : {X : 𝓤 ̇} {n : ℕ}
                                 → (ua : is-univalent 𝓤)
                                 → (x : X) (v : ∥ X ∥[ succ n ])
                                 → (∣ x ∣[ succ n ] ＝ v)
                                 ≃ trunc-id-family-type ua x v
 trunc-identity-characterization {𝓤} {X} {n} ua x v =
  (identity-on-trunc-to-family ua x v ,
   Yoneda-Theorem-forth ∣ x ∣[ succ n ]
    (identity-on-trunc-to-family ua x)
    (trunc-id-family-is-identity-system ua x) v)

 eliminated-trunc-identity-char : {X : 𝓤 ̇} {x x' : X} {n : ℕ}
                                → (ua : is-univalent 𝓤)
                                → ∥ x ＝ x' ∥[ n ]
                                ≃ (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ])
 eliminated-trunc-identity-char {𝓤} {X} {x} {x'} {n} ua =
  ≃-comp (idtoeq ∥ x ＝ x' ∥[ n ]
                 (trunc-id-family-type ua x ∣ x' ∣[ succ n ])
                 (trunc-id-family-computes ua x x' ⁻¹))
         (≃-sym (trunc-identity-characterization ua x ∣ x' ∣[ succ n ]))

 forth-trunc-id-char : {X : 𝓤 ̇} {x x' : X} {n : ℕ}
                     → (ua : is-univalent 𝓤)
                     → ∥ x ＝ x' ∥[ n ]
                     → (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ])
 forth-trunc-id-char ua = ⌜ eliminated-trunc-identity-char ua ⌝

\end{code}

We show that the existence of propositional truncation follows from the existence
of general truncations. Notice this implication manifests as a function between
record types.

\begin{code}

H-level-truncations-give-propositional-truncations : H-level-truncations-exist
                                                   → propositional-truncations-exist
H-level-truncations-give-propositional-truncations te = record
 { ∥_∥        = ∥_∥[ 1 ]
 ; ∥∥-is-prop = is-prop'-implies-is-prop ∥∥ₙ-hlevel
 ; ∣_∣        = ∣_∣[ 1 ]
 ; ∥∥-rec     = λ - → ∥∥ₙ-rec (is-prop-implies-is-prop' -)
 }
 where
  open H-level-truncations-exist te

\end{code}
