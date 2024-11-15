Ian Ray, 23rd July 2024

Modifications made by Ian Ray on 26th September 2024

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
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropTrunc
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Truncations fe
open import UF.TruncationLevels
open import UF.TruncatedTypes fe
open import UF.Univalence
open import UF.Yoneda

\end{code}

We now define the notion of connectedness for types and functions with respect
to truncation levels.

\begin{code}

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

module connectedness-results (te : general-truncations-exist) where

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

 being-connected-is-prop : {k : ℕ₋₂} {X : 𝓤 ̇} 
                         → is-prop (X is k connected) 
 being-connected-is-prop = being-truncated-is-prop

 being-connected-map-is-prop : {k : ℕ₋₂} {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                             → is-prop (f is k connected-map)
 being-connected-map-is-prop = Π-is-prop fe (λ y → being-connected-is-prop)

 connected-if-contr : {X : 𝓤 ̇} {k : ℕ₋₂}
                    → is-contr X
                    → X is k connected
 connected-if-contr {_} {X} {−2} X-is-contr = −2-trunc-is-contr
 connected-if-contr {_} {X} {succ k} (c , C) = (∣ c ∣[ k + 1 ] , C')
  where
   C'' : (x : X) → ∣ c ∣[ k + 1 ] ＝ ∣ x ∣[ k + 1 ]
   C'' x = canonical-identity-trunc-map ∣ C x ∣[ k ]
   C' : is-central ∥ X ∥[ k + 1 ] ∣ c ∣[ k + 1 ]
   C' = ∥∥ₙ-ind (λ v → λ p q → truncation-levels-closed-under-Id
                 (∥∥ₙ-is-truncated ∣ c ∣[ succ k ] v) p q) C''

\end{code}

TODO: show that connectedness as defined elsewhere in the library is
a special case of k-connectedness. Connectedness typically means set
connectedness, by our convention it will mean 0-connectedness.

We directly prove a characterization of connectedness from the HoTT book
(see Corollary 7.5.9.).

NOTE: We will NOT state the corallary as an iff statement due to a large
quantification issue.

\begin{code}

 private
  consts : {X : 𝓤 ̇} {Y : 𝓥 ̇}
         → Y → (X → Y)
  consts y x = y

 maps-from-connected-type-to-truncated-type-const : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ₋₂}
                                                  → X is n connected
                                                  → Y is n truncated
                                                  → Y ≃ (X → Y)
 maps-from-connected-type-to-truncated-type-const {𝓤} {_} {X} {Y} {n}
  X-conn Y-trunc = e
  where
   e : Y ≃ (X → Y)
   e = Y                ≃⟨ 𝟙→ fe ⟩
       (𝟙 {𝓤} → Y)      ≃⟨ →cong'' fe fe I ⟩
       (∥ X ∥[ n ] → Y) ≃⟨ ∥∥ₙ-universal-property Y-trunc ⟩
       (X → Y)          ■
    where
     I : 𝟙 {𝓤} ≃ ∥ X ∥[ n ]
     I = singleton-≃-𝟙' X-conn
   observation : consts ＝ ⌜ e ⌝
   observation = refl

 Cor-7-5-9i : {X : 𝓤 ̇} {n : ℕ₋₂}
            → X is n connected
            → (Y : 𝓥 ̇)
            → Y is n truncated
            → is-equiv consts
 Cor-7-5-9i X-conn Y Y-trunc =
  ⌜⌝-is-equiv (maps-from-connected-type-to-truncated-type-const X-conn Y-trunc)

 Cor-7-5-9ii : {X : 𝓤 ̇} {n : ℕ₋₂}
             → ({𝓥 : Universe} (Y : 𝓥 ̇)
               → Y is n truncated
               → is-equiv {𝓥} {𝓤 ⊔ 𝓥} {Y} {X → Y} consts)
             → X is n connected
 Cor-7-5-9ii {𝓤} {X} {n} is-equiv-from-trunc = (c , G)
  where
   s : (X → ∥ X ∥[ n ]) → ∥ X ∥[ n ]
   s = section-of consts (equivs-have-sections consts
        (is-equiv-from-trunc ∥ X ∥[ n ] ∥∥ₙ-is-truncated))
   H : consts ∘ s ∼ id
   H = section-equation consts (equivs-have-sections consts
        (is-equiv-from-trunc ∥ X ∥[ n ] ∥∥ₙ-is-truncated))
   c : ∥ X ∥[ n ]
   c = s ∣_∣[ n ]
   H' : consts c ＝ ∣_∣[ n ]
   H' = H ∣_∣[ n ]
   G : (v : ∥ X ∥[ n ]) → c ＝ v
   G = ∥∥ₙ-ind (λ - → truncation-levels-are-upper-closed ∥∥ₙ-is-truncated c -)
               (λ x → happly H' x)

\end{code}

We will now prove a general result from the HoTT book the characterizes when
a map is connected (see Lemma 7.5.7.)

\begin{code}

 dependent-equiv-from-truncated-fam-connected-map : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                                                    {P : Y → 𝓦 ̇} {n : ℕ₋₂} 
                                                  → ((y : Y)
                                                   → (P y) is n truncated)
                                                  → f is n connected-map
                                                  → ((y : Y) → P y)
                                                   ≃ ((x : X) → P (f x))
 dependent-equiv-from-truncated-fam-connected-map {_} {_} {𝓦} {X} {Y} {f} {P} {n}
  P-trunc f-conn = e
  where
   e : ((y : Y) → P y) ≃ ((x : X) → P (f x))
   e = ((y : Y) → P y)                                         ≃⟨ I ⟩
       ((y : Y) → (fiber f y → P y))                           ≃⟨ II ⟩
       ((y : Y) → (x : X) → (p : f x ＝ y) → P y)              ≃⟨ Π-flip' ⟩
       ((x : X) → (y : Y) → (p : f x ＝ y) → P y)              ≃⟨ III ⟩
       ((x : X) → P (f x))                                     ■
    where
     I = Π-cong fe fe (λ - → maps-from-connected-type-to-truncated-type-const
                       (f-conn -) (P-trunc -))
     II = Π-cong fe fe (λ - → curry-uncurry' fe fe)
     III = Π-cong fe fe (λ - → ≃-sym (Yoneda-equivalence fe' (f -) P))
   observation : ⌜ e ⌝ ＝ dprecomp P f
   observation = refl

 Lemma7-5-7-i : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {P : Y → 𝓦 ̇} {n : ℕ₋₂} 
              → ((y : Y) → (P y) is n truncated)
              → f is n connected-map
              → is-equiv (dprecomp P f)
 Lemma7-5-7-i {_} {_} {_} {X} {Y} {f} {P} {n} P-trunc f-conn =
  ⌜⌝-is-equiv (dependent-equiv-from-truncated-fam-connected-map P-trunc f-conn)

 Lemma7-5-7-ii : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {P : Y → 𝓦 ̇} 
               → is-equiv (dprecomp P f)
               → has-section (dprecomp P f)
 Lemma7-5-7-ii {_} {_} {_} {_} {_} {f} {P} =
  equivs-have-sections (dprecomp P f)

 Lemma7-5-7-iii : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {n : ℕ₋₂} 
                → ({𝓦 : Universe} {P : Y → 𝓦 ̇}
                  → ((y : Y) → (P y) is n truncated)
                  → has-section (dprecomp P f))
                → f is n connected-map
 Lemma7-5-7-iii {𝓤} {𝓥} {X} {Y} {f} {n} sec-from-trunc y = (c y , C)
  where
   Q : Y → 𝓤 ⊔ 𝓥 ̇
   Q y = ∥ fiber f y ∥[ n ]
   c' : ((x : X) → ∥ fiber f (f x) ∥[ n ])
      → ((y : Y) → ∥ fiber f y ∥[ n ])
   c' = section-of (dprecomp Q f) (sec-from-trunc (λ - → ∥∥ₙ-is-truncated))
   c : (y : Y) → ∥ fiber f y ∥[ n ]
   c = c' (λ - → ∣ (- , refl) ∣[ n ])
   H' : (dprecomp Q f) ∘ c' ∼ id
   H' = section-equation (dprecomp Q f)
                         (sec-from-trunc (λ - → ∥∥ₙ-is-truncated))
   H : (x : X) → c (f x) ＝ ∣ (x , refl) ∣[ n ]
   H = happly' ((dprecomp Q f ∘ c') (λ - → ∣ (- , refl) ∣[ n ]))
               (λ - → ∣ (- , refl) ∣[ n ]) (H' (λ - → ∣ (- , refl) ∣[ n ]))
   C : (w : ∥ fiber f y ∥[ n ]) → c y ＝ w
   C = ∥∥ₙ-ind (λ - → truncation-levels-are-upper-closed ∥∥ₙ-is-truncated (c y) -)
               C'
    where
     C' : ((x , p) : fiber f y) → c y ＝ ∣ (x , p) ∣[ n ]
     C' (x , refl) = H x
                

\end{code}

We show that the canonical n-truncation map is n-connected.

\begin{code}

 canonical-trunc-map-is-connected : {X : 𝓤 ̇} {n : ℕ₋₂}
                                  → ∣_∣[ n ] is n connected-map
 canonical-trunc-map-is-connected {_} {X} {n} = Lemma7-5-7-iii has-sec
  where
   has-sec : {𝓦 : Universe} {P : ∥ X ∥[ n ] → 𝓦 ̇}
           → ((v : ∥ X ∥[ n ]) → P v is n truncated)
           → has-section (dprecomp P ∣_∣[ n ])
   has-sec {_} {P} P-trunc = (∥∥ₙ-ind P-trunc , comp-rule)
    where
     comp-rule : dprecomp P ∣_∣[ n ] ∘ ∥∥ₙ-ind P-trunc ∼ id
     comp-rule h = (dprecomp P ∣_∣[ n ]) (∥∥ₙ-ind P-trunc h) ＝⟨ refl ⟩
                   (∥∥ₙ-ind P-trunc h) ∘ ∣_∣[ n ]            ＝⟨ I ⟩
                   h                                         ∎
      where
       I = dfunext fe (∥∥ₙ-ind-comp P-trunc h)

\end{code}

We characterize −1-connected types as inhabited types and −1-connected maps as
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
 map-is-−1-connected-if-surj f-is-surj y =
  −1-connected-if-inhabited (f-is-surj y)

 map-is-−1-connected-iff-surj : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y}
                              → f is −1 connected-map ↔ is-surjection f
 map-is-−1-connected-iff-surj =
  (map-is-surj-if-−1-connected , map-is-−1-connected-if-surj)

\end{code}

We develop some closure conditions pertaining to connectedness. Connectedness
is closed under retracts and equivalence as expected, but more importantly
connectedness extends below:
more precisely if a type is k connected then it is l connected for all l ≤ k.
We provide a few incarnations of this fact below which may prove useful. 

\begin{code}

 connectedness-is-closed-under-retract : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ₋₂}
                                       → retract Y of X
                                       → X is k connected
                                       → Y is k connected
 connectedness-is-closed-under-retract R X-conn =
  retract-of-singleton (truncation-closed-under-retract R) X-conn

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
                               → X is (k + 1) connected
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
   p = k       ＝⟨ subtraction-ℕ₋₂-identification l k o ⁻¹ ⟩
       l + m   ∎

 map-connectedness-is-lower-closed : {X : 𝓤 ̇} {Y : 𝓥 ̇} {f : X → Y} {k l : ℕ₋₂}
                                   → (l ≤ k)
                                   → f is k connected-map
                                   → f is l connected-map
 map-connectedness-is-lower-closed o f-k-con y =
  connectedness-is-lower-closed' o (f-k-con y)

\end{code}

We characterize connected types in terms of inhabitedness and connectedness of
the identity type at one level below. We will assume univalence only when necessary.

\begin{code}

 inhabited-if-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                        → X is (k + 1) connected → ∥ X ∥
 inhabited-if-connected {_} {_} {k} X-conn =
  inhabited-if-−1-connected (connectedness-is-lower-closed' ⋆ X-conn)

 _is-locally_connected : (X : 𝓤 ̇) (k : ℕ₋₂) → 𝓤  ̇
 X is-locally k connected = (x y : X) → (x ＝ y) is k connected

 connected-types-are-locally-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                       → is-univalent 𝓤
                                       → X is (k + 1) connected
                                       → X is-locally k connected
 connected-types-are-locally-connected {_} {_} {k} ua X-conn x y =
  equiv-to-singleton (eliminated-trunc-identity-char ua)
   (is-prop-implies-is-prop' (singletons-are-props X-conn)
    ∣ x ∣[ succ k ] ∣ y ∣[ succ k ])

 connected-types-are-inhabited-and-locally-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                                     → is-univalent 𝓤
                                                     → X is (k + 1) connected
                                                     → ∥ X ∥
                                                     × X is-locally k connected
 connected-types-are-inhabited-and-locally-connected ua X-conn =
  (inhabited-if-connected X-conn , connected-types-are-locally-connected ua X-conn)

 inhabited-and-locally-connected-types-are-connected : {X : 𝓤 ̇} {k : ℕ₋₂}
                                                     → is-univalent 𝓤
                                                     → ∥ X ∥
                                                     → X is-locally k connected
                                                     → X is (k + 1) connected
 inhabited-and-locally-connected-types-are-connected
  {_} {_} {−2} ua anon-x id-conn =
  pointed-props-are-singletons (prop-trunc-to-−1-trunc pt anon-x) −1-trunc-is-prop
 inhabited-and-locally-connected-types-are-connected
  {_} {_} {succ k} ua anon-x id-conn =
  ∥∥-rec (being-singleton-is-prop fe)
         (λ x → (∣ x ∣[ (k + 1) + 1 ]
          , ∥∥ₙ-ind (λ v → truncation-levels-are-upper-closed
           (λ p q → ∥∥ₙ-is-truncated ∣ x ∣[ (k + 1) + 1 ] v p q)) 
            (λ y → forth-trunc-id-char ua (center (id-conn x y)))))
         anon-x

 connected-characterization : {X : 𝓤 ̇} {k : ℕ₋₂}
                            → is-univalent 𝓤
                            → X is (k + 1) connected
                            ↔ ∥ X ∥ × X is-locally k connected
 connected-characterization ua =
  (connected-types-are-inhabited-and-locally-connected ua
   , uncurry (inhabited-and-locally-connected-types-are-connected ua))

 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} {k : ℕ₋₂} 
                      → (ua : is-univalent (𝓤 ⊔ 𝓥))
                      → (f : X → Y)
                      → f is (k + 1) connected-map
                      → {x x' : X}
                      → (ap f {x} {x'}) is k connected-map
 ap-is-less-connected ua f f-conn {x} {x'} p =
  equiv-to-singleton (truncation-closed-under-equiv (fiber-of-ap-≃ f p))
   (connected-types-are-locally-connected ua (f-conn (f x'))
    (x , p) (x' , refl))

\end{code}

We postulate a results from 7.5. of the HoTT book.

TODO: Formalize this.

\begin{code}

 basepoint-map-is-less-connected-result : {𝓤 : Universe} → (𝓤 ⁺)  ̇
 basepoint-map-is-less-connected-result {𝓤} = {X : 𝓤 ̇} {n : ℕ₋₂}
                                            → (x₀ : 𝟙 {𝓤} → X)
                                            → X is (n + 1) connected
                                            → x₀ is n connected-map
                                 
\end{code}
