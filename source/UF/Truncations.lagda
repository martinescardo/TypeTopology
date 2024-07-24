Ian Ray, 07/23/2024

Truncations...

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

module UF.Truncations (fe : FunExt)
                      (fe' : Fun-Ext)
                      (pt : propositional-truncations-exist)
                       where

open import UF.H-Levels fe fe' 

\end{code}

We define the notion of a k-truncation using record types.

\begin{code}

record H-level-truncations-exist : 𝓤ω where
 field
  ∥_∥[_] : {𝓤 : Universe} → 𝓤 ̇ → ℕ → 𝓤 ̇
  ∥∥ₙ-h-level : {𝓤 : Universe} {X : 𝓤 ̇ } {n : ℕ} → X is-of-hlevel n
  ∣_∣[_] :  {𝓤 : Universe} {X : 𝓤 ̇ } → X → (n : ℕ) → ∥ X ∥[ n ]
  ∥∥ₙ-ind : {X : 𝓤 ̇ } {n : ℕ} {P : ∥ X ∥[ n ] → 𝓥 ̇ }
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
        (ua : Univalence)
       where

 open H-level-truncations-exist te

 ∥∥ₙ-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
         → Y is-of-hlevel n → (X → Y) → ∥ X ∥[ n ] → Y
 ∥∥ₙ-rec {𝓤} {𝓥} {X} {Y} {n} Y-h-level f s = ∥∥ₙ-ind (λ - → Y-h-level) f s

 ∥∥ₙ-uniqueness : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                → Y is-of-hlevel n
                → (f g : ∥ X ∥[ n ] → Y)
                → ((x : X) → f (∣ x ∣[ n ]) ＝ g (∣ x ∣[ n ]))
                → (s : ∥ X ∥[ n ]) → f s ＝ g s
 ∥∥ₙ-uniqueness {𝓤} {𝓥} {X} {Y} {n} Y-h-lev f g H =
   ∥∥ₙ-ind (λ s → id-types-are-same-hlevel n Y-h-lev (f s) (g s)) H

 ∥∥ₙ-rec-comp : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
              → (m : Y is-of-hlevel n)
              → (g : X → Y)
              → (x : X) → ∥∥ₙ-rec m g ∣ x ∣[ n ] ＝ g x
 ∥∥ₙ-rec-comp m g = ∥∥ₙ-ind-comp (λ - → m) g

 ∥∥ₙ-rec-double : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
                → Z is-of-hlevel n
                → (X → Y → Z)
                → ∥ X ∥[ n ] → ∥ Y ∥[ n ] → Z
 ∥∥ₙ-rec-double {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} Z-h-level g =
  ∥∥ₙ-rec (hlevel-closed-under-→ n (∥ Y ∥[ n ]) Z Z-h-level)
          (λ x → ∥∥ₙ-rec Z-h-level (λ y → g x y))

 ∥∥ₙ-rec-double-comp : {𝓤 𝓥 𝓦 : Universe}
                       {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
                     → (m : Z is-of-hlevel n)
                     → (g : X → Y → Z)
                     → (x : X) → (y : Y)
                     → ∥∥ₙ-rec-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
 ∥∥ₙ-rec-double-comp {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} m g x y =
  ∥∥ₙ-rec-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ happly
                                              (∥∥ₙ-rec-comp
                                              (hlevel-closed-under-→ n
                                                (∥ Y ∥[ n ]) Z m)
                                              (λ x → ∥∥ₙ-rec m (λ y → g x y)) x)
                                              ∣ y ∣[ n ]  ⟩
  ∥∥ₙ-rec m (λ y → g x y) ∣ y ∣[ n ]       ＝⟨ ∥∥ₙ-rec-comp m (λ y → g x y) y ⟩
  g x y                                    ∎

 abstract
  ∥∥ₙ-ind-double : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                   {P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇ } 
                 → ((u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ])
                  → (P u v) is-of-hlevel n)
                 → ((x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
                 → (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ]) → P u v
  ∥∥ₙ-ind-double {𝓤} {𝓥} {𝓦} {X} {Y} {n} {P} P-h-level f =
   ∥∥ₙ-ind (λ u → hlevel-closed-under-Π n ∥ Y ∥[ n ] (P u)
                                        (λ v → P-h-level u v))
           (λ x → ∥∥ₙ-ind (λ v → P-h-level ∣ x ∣[ n ] v) (λ y → f x y))

  ∥∥ₙ-ind-double-comp : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                        {P : ∥ X ∥[ n ] → ∥ Y ∥[ n ] → 𝓦 ̇ } 
                      → (m : (u : ∥ X ∥[ n ]) → (v : ∥ Y ∥[ n ])
                       → (P u v) is-of-hlevel n)
                      → (g : (x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
                      → (x : X) → (y : Y)
                      → ∥∥ₙ-ind-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
  ∥∥ₙ-ind-double-comp {𝓤} {𝓥} {𝓦} {X} {Y} {n} {P} m g x y =
   ∥∥ₙ-ind-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ happly
                                                (∥∥ₙ-ind-comp
                                                 (λ u → hlevel-closed-under-Π
                                                  n ∥ Y ∥[ n ] (P u)
                                                  (λ v → m u v))
                                                 (λ x' → ∥∥ₙ-ind
                                                  (λ v → m ∣ x' ∣[ n ] v)
                                                  (λ y' → g x' y')) x)
                                                ∣ y ∣[ n ] ⟩
   ∥∥ₙ-ind (λ v → m ∣ x ∣[ n ] v)
           (λ y' → g x y') ∣ y ∣[ n ]       ＝⟨ ∥∥ₙ-ind-comp
                                                 (λ v → m ∣ x ∣[ n ] v)
                                                 (λ y' → g x y') y ⟩
   g x y                                    ∎

\end{code}

We develop useful results related to general truncations. We characterize the
first couple levels of truncation (TODO: three-hlevel is a groupoid). We
provide the canonical predecessor map and show truncations are closed under
equivalence and succesive applications of truncation.

\begin{code}

  zero-hlevel-is-contr : {X : 𝓤 ̇ } → is-contr (∥ X ∥[ zero ])
  zero-hlevel-is-contr = ∥∥ₙ-h-level 

  one-hlevel-is-prop : {X : 𝓤 ̇ } → is-prop (∥ X ∥[ succ zero ])
  one-hlevel-is-prop = is-prop'-implies-is-prop ∥∥ₙ-h-level 

  two-hlevel-is-set : {X : 𝓤 ̇ } → is-set (∥ X ∥[ succ (succ zero) ])
  two-hlevel-is-set {𝓤} {X} {x} {y} =
   is-prop'-implies-is-prop (∥∥ₙ-h-level x y)

  canonical-pred-map : {X : 𝓤 ̇} {n : ℕ}
                     → ∥ X ∥[ succ n ] → ∥ X ∥[ n ]
  canonical-pred-map {𝓤} {X} {n} x =
   ∥∥ₙ-rec (hlevels-are-upper-closed n (∥ X ∥[ n ]) ∥∥ₙ-h-level)
            (λ x → ∣ x ∣[ n ]) x

  canonical-pred-map-comp : {X : 𝓤 ̇} {n : ℕ} (x : X)
                          → canonical-pred-map (∣ x ∣[ succ n ]) ＝ (∣ x ∣[ n ])
  canonical-pred-map-comp {𝓤} {X} {n} x =
   ∥∥ₙ-rec-comp (hlevels-are-upper-closed n (∥ X ∥[ n ]) ∥∥ₙ-h-level)
                (λ _ → ∣ _ ∣[ n ]) x

  truncation-closed-under-equiv : {𝓤 𝓥 : Universe}
                                → (n : ℕ)
                                → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                → X ≃ Y
                                → (∥ X ∥[ n ]) ≃ (∥ Y ∥[ n ])
  truncation-closed-under-equiv n X Y e = (f , (b , G) , (b , H))
   where
    f : ∥ X ∥[ n ] → ∥ Y ∥[ n ]
    f = ∥∥ₙ-rec ∥∥ₙ-h-level (λ x → ∣ (⌜ e ⌝ x) ∣[ n ])
    b : ∥ Y ∥[ n ] → ∥ X ∥[ n ]
    b = ∥∥ₙ-rec ∥∥ₙ-h-level (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ])
    H : b ∘ f ∼ id
    H = ∥∥ₙ-ind (λ s → id-types-are-same-hlevel n ∥∥ₙ-h-level
                                                (b (f s)) s)
                H'
     where
      H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
      H' x = b (f (∣ x ∣[ n ]))         ＝⟨ ap b (∥∥ₙ-rec-comp ∥∥ₙ-h-level
                                                 (λ x → ∣ (⌜ e ⌝ x) ∣[ n ]) x) ⟩
             b (∣ ⌜ e ⌝ x ∣[ n ])       ＝⟨ ∥∥ₙ-rec-comp ∥∥ₙ-h-level
                                                (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ])
                                                (⌜ e ⌝ x) ⟩
             (∣ ⌜ e ⌝⁻¹ (⌜ e ⌝ x) ∣[ n ]) ＝⟨ ap (λ x → ∣ x ∣[ n ])
                                             (inverses-are-retractions' e x) ⟩
             (∣ x ∣[ n ])                ∎ 
    G : f ∘ b ∼ id
    G = ∥∥ₙ-ind (λ s → id-types-are-same-hlevel n ∥∥ₙ-h-level
                                                (f (b s)) s)
                G'
     where
      G' : (y : Y) → f (b (∣ y ∣[ n ])) ＝ (∣ y ∣[ n ])
      G' y = f (b (∣ y ∣[ n ]))         ＝⟨ ap f (∥∥ₙ-rec-comp ∥∥ₙ-h-level
                                               (λ y → ∣ (⌜ e ⌝⁻¹ y) ∣[ n ]) y) ⟩
             f (∣ (⌜ e ⌝⁻¹ y) ∣[ n ])   ＝⟨ ∥∥ₙ-rec-comp ∥∥ₙ-h-level
                                           (λ x → ∣ ⌜ e ⌝ x ∣[ n ]) (⌜ e ⌝⁻¹ y) ⟩
             (∣ ⌜ e ⌝ (⌜ e ⌝⁻¹ y) ∣[ n ]) ＝⟨ ap (λ y → ∣ y ∣[ n ])
                                                 (inverses-are-sections' e y) ⟩
             (∣ y ∣[ n ])               ∎ 

  succesive-truncations-equiv : (X : 𝓤 ̇) (n : ℕ)
                              → (∥ X ∥[ n ]) ≃ (∥ (∥ X ∥[ succ n ]) ∥[ n ])
  succesive-truncations-equiv X n = (f , (b , G) , (b , H))
   where
    f : (∥ X ∥[ n ]) → (∥ (∥ X ∥[ succ n ]) ∥[ n ])
    f = ∥∥ₙ-rec ∥∥ₙ-h-level (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ])
    b : (∥ (∥ X ∥[ succ n ]) ∥[ n ]) → (∥ X ∥[ n ])
    b = ∥∥ₙ-rec ∥∥ₙ-h-level (canonical-pred-map)
    G : f ∘ b ∼ id
    G = ∥∥ₙ-ind (λ s → id-types-are-same-hlevel n ∥∥ₙ-h-level
                                                 (f (b s)) s)
                (∥∥ₙ-ind (λ t → id-types-are-same-hlevel n
                                 (id-types-are-same-hlevel n
                                 ∥∥ₙ-h-level (f (b (∣ t ∣[ n ])))
                                              ((∣ t ∣[ n ]))))
                          G')
     where
      G' : (x : X)
         → f (b (∣ ∣ x ∣[ succ n ] ∣[ n ])) ＝ (∣ ∣ x ∣[ succ n ] ∣[ n ])
      G' x = f (b (∣ ∣ x ∣[ succ n ] ∣[ n ]))     ＝⟨ ap f (∥∥ₙ-rec-comp
                                                         ∥∥ₙ-h-level
                                                         canonical-pred-map
                                                         (∣ x ∣[ succ n ])) ⟩
             f (canonical-pred-map (∣ x ∣[ succ n ])) ＝⟨ ap f
                                                    (canonical-pred-map-comp x) ⟩
             f (∣ x ∣[ n ])             ＝⟨ ∥∥ₙ-rec-comp
                                             ∥∥ₙ-h-level
                                             (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ])
                                             x ⟩
             (∣ ∣ x ∣[ succ n ] ∣[ n ])   ∎
    H : b ∘ f ∼ id
    H = ∥∥ₙ-ind (λ s → id-types-are-same-hlevel n ∥∥ₙ-h-level
                                                (b (f s)) s)
                H'
     where
      H' : (x : X) → b (f (∣ x ∣[ n ])) ＝ (∣ x ∣[ n ])
      H' x = b (f (∣ x ∣[ n ]))       ＝⟨ ap b (∥∥ₙ-rec-comp ∥∥ₙ-h-level
                                            (λ x → ∣ ∣ x ∣[ succ n ] ∣[ n ]) x) ⟩
             b (∣ ∣ x ∣[ succ n ] ∣[ n ]) ＝⟨ ∥∥ₙ-rec-comp ∥∥ₙ-h-level
                                           canonical-pred-map (∣ x ∣[ succ n ]) ⟩
             canonical-pred-map (∣ x ∣[ succ n ]) ＝⟨ canonical-pred-map-comp x ⟩
             (∣ x ∣[ n ])                   ∎

\end{code}

We now define an equivalence that characterizes the truncated identity type.

\begin{code}

 canonical-id-trunc-map : {𝓤 : Universe} {X : 𝓤 ̇} {x y : X} {n : ℕ}
                        → ∥ x ＝ y ∥[ n ]
                        → ∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ]
 canonical-id-trunc-map {𝓤} {X} {x} {y} {n} =
  ∥∥ₙ-rec ∥∥ₙ-h-level (ap (λ x → ∣ x ∣[ (succ n) ]))

 private
  P' : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
    → ∥ X ∥[ succ n ] → ∥ X ∥[ succ n ] → ℍ n 𝓤
  P' {𝓤} {X} {n} =
   ∥∥ₙ-rec-double (ℍ-is-of-next-hlevel n 𝓤 (ua 𝓤))
                  (λ x x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-h-level))

  P : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
    → ∥ X ∥[ succ n ] → ∥ X ∥[ succ n ] → 𝓤 ̇
  P u v = pr₁ (P' u v)

  P-computes : {𝓤 : Universe} {X : 𝓤 ̇} {x y : X} {n : ℕ}
             → P ∣ x ∣[ succ n ] ∣ y ∣[ succ n ] ＝ ∥ x ＝ y ∥[ n ]
  P-computes {𝓤} {X} {x} {y} {n} =
   ap pr₁ (∥∥ₙ-rec-double-comp (ℍ-is-of-next-hlevel n 𝓤 (ua 𝓤))
        (λ x x' → (∥ x ＝ x' ∥[ n ] , ∥∥ₙ-h-level)) x y)

\end{code}

TODO: Current proof follows the HoTT book encode-decode method but it is
believed there is a better proof.

 gen-trunc-id-type-char : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
                        → (u v : ∥ X ∥[ succ n ])
                        → P u v ≃ (u ＝ v)
 gen-trunc-id-type-char {𝓤} {X} {n} u v =
  (decode u v , qinvs-are-equivs (decode u v) (encode u v , H u v , G u v))
  where
   decode : (u v : ∥ X ∥[ succ n ])
          → P u v → u ＝ v
   decode =
    ∥∥ₙ-ind-double (λ u v → hlevel-closed-under-→ (succ n) (P u v) (u ＝ v)
                                                   (∥∥ₙ-h-level))
                    (λ x y → transport (λ T →
                                        T → ∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ])
                                       (P-computes ⁻¹)
                                       canonical-id-trunc-map)
   P-refl : (u : ∥ X ∥[ succ n ]) → P u u
   P-refl = ∥∥ₙ-ind (λ - → ∥∥ₙ-h-level)
                    (λ x → transport (λ - → -) (P-computes ⁻¹) ∣ refl ∣[ n ] )
   encode : (u v : ∥ X ∥[ succ n ])
          → u ＝ v → P u v
   encode u v p = transport (λ v' → P u v') p (P-refl u)
   H : (u v : ∥ X ∥[ succ n ]) → encode u v ∘ decode u v ∼ id
   H = ∥∥ₙ-ind-double {𝓤} {𝓤} {𝓤} {X} {X} {succ n}
                      {λ u v → encode u v ∘ decode u v ∼ id}
                      (λ - - → (λ - - → ∥∥ₙ-h-level)) H'
    where
     H' : (x y : X) (s : P ∣ x ∣[ succ n ] ∣ y ∣[ succ n ])
        → encode ∣ x ∣[ succ n ] ∣ y ∣[ succ n ]
          (decode ∣ x ∣[ succ n ] ∣ y ∣[ succ n ] s)
          ＝ s
     H' x y s =
      encode ∣ x ∣[ succ n ] ∣ y ∣[ succ n ]
       (decode ∣ x ∣[ succ n ] ∣ y ∣[ succ n ] s)＝⟨ ap
                                                    (encode ∣ x ∣[ succ n ]
                                                    ∣ y ∣[ succ n ]) refl ⟩
      encode ∣ x ∣[ succ n ] ∣ y ∣[ succ n ]
       ((transport (λ T →
        T → ∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ])
        (P-computes ⁻¹)
        canonical-id-trunc-map) s)               ＝⟨ refl ⟩
      transport (λ v' → P ∣ x ∣[ succ n ] v')
                 ((transport (λ T →
                  T → ∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ])
                 (P-computes ⁻¹)
                 canonical-id-trunc-map) s)
                (P-refl ∣ x ∣[ succ n ])         ＝⟨ {!!} ⟩
      {!!}
   G : (u v : ∥ X ∥[ succ n ]) → decode u v ∘ encode u v ∼ id 
   G u .u refl = ∥∥ₙ-ind {𝓤} {𝓤} {X} {succ n}
                         {λ u → (decode u u ∘ encode u u) refl ＝ refl}
                         (λ - → ∥∥ₙ-h-level) G' u
    where
     G' : (x : X) → decode ∣ x ∣[ succ n ] ∣ x ∣[ succ n ]
                    (encode ∣ x ∣[ succ n ] ∣ x ∣[ succ n ] refl)
                  ＝ refl
     G' x =
      decode ∣ x ∣[ succ n ] ∣ x ∣[ succ n ]
       (encode ∣ x ∣[ succ n ] ∣ x ∣[ succ n ] refl)＝⟨ ap (decode
                                                            ∣ x ∣[ succ n ]
                                                            ∣ x ∣[ succ n ])
                                                            refl ⟩
      decode ∣ x ∣[ succ n ] ∣ x ∣[ succ n ]
       (P-refl ∣ x ∣[ succ n ])                     ＝⟨ happly refl
                                                       (P-refl ∣ x ∣[ succ n ]) ⟩
      transport
       (λ T → T → ∣ x ∣[ succ n ] ＝ ∣ x ∣[ succ n ])
       (P-computes ⁻¹)
       canonical-id-trunc-map
       (P-refl ∣ x ∣[ succ n ]) ＝⟨ {!!} ⟩
      {!!}

 trunc-id-type-char : {𝓤 : Universe} {X : 𝓤 ̇} {x y : X} {n : ℕ}
                    → ∥ x ＝ y ∥[ n ]
                    ≃ (∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ])
 trunc-id-type-char {𝓤} {X} {x} {y} {n} =
  ≃-comp (idtoeq ∥ x ＝ y ∥[ n ]
                 (P ∣ x ∣[ succ n ] ∣ y ∣[ succ n ])
                 (P-computes ⁻¹))
         (gen-trunc-id-type-char ∣ x ∣[ succ n ] ∣ y ∣[ succ n ])

\end{code}

{𝓤} {𝓤} {X} {succ n}
{λ u → (decode u u ∘ encode u u) refl ＝ refl}

We demonstrate the equivalence of 1-truncation and propositional truncation:
  ∥ X ∥₁ ≃ ∥ X ∥

\begin{code}

module 1-truncation-propositional-truncation-relationship
        (te : H-level-truncations-exist)
        (ua : Univalence)
         where

 open H-level-truncations-exist te
 open GeneralTruncations te ua
 open propositional-truncations-exist pt

 1-trunc-is-prop : {X : 𝓤 ̇} → is-prop (∥ X ∥[ 1 ])
 1-trunc-is-prop = is-prop'-implies-is-prop (∥∥ₙ-h-level)

 1-trunc-to-prop-trunc : {X : 𝓤 ̇} → ∥ X ∥[ 1 ] → ∥ X ∥
 1-trunc-to-prop-trunc = ∥∥ₙ-rec (is-prop-implies-is-prop' ∥∥-is-prop) ∣_∣

 prop-trunc-to-1-trunc : {X : 𝓤 ̇} → ∥ X ∥ → ∥ X ∥[ 1 ]
 prop-trunc-to-1-trunc = ∥∥-rec 1-trunc-is-prop (λ x → ∣ x ∣[ 1 ])

 1-trunc-≃-prop-trunc : {X : 𝓤 ̇}
                      → (∥ X ∥[ 1 ]) ≃ ∥ X ∥
 1-trunc-≃-prop-trunc {𝓤} {X} =
  logically-equivalent-props-are-equivalent 1-trunc-is-prop ∥∥-is-prop
                                            1-trunc-to-prop-trunc
                                            prop-trunc-to-1-trunc

\end{code}

