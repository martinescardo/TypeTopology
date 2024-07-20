Martin Escardo and Ian Ray, 06/02/2024

We develop H-levels (a la Voevodsky). In Homotopy Type Theory there is a
natural stratification of types defined inductively starting with contractible
types and saying the an (n+1)-type has an identity type that is an n-type.
Voevodsky introduced the notion of H-level where contractible types are at
level n = 0. Alternatively, in book HoTT, truncated types are defined so that
contractible types are at level k = -2. Of course, the two notions are
equivalent as they are indexed by equivalent types, that is ℕ ≃ ℤ₋₂, but it is
important to be aware of the fact that concepts are 'off by 2' when translating
between conventions. 

In this file we will assume function extensionality globally but not univalence.
The final result of the file will be proved in the local presence of univalence.

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
open import Naturals.Order

module UF.H-Levels (fe : FunExt)
                   (fe' : Fun-Ext)
                   (pt : propositional-truncations-exist)
                    where

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel zero = is-contr X
X is-of-hlevel succ n = (x x' : X) → (x ＝ x') is-of-hlevel n

hlevel-relation-is-prop : {𝓤 : Universe} (n : ℕ) (X : 𝓤 ̇ )
                        → is-prop (X is-of-hlevel n)
hlevel-relation-is-prop {𝓤} zero X = being-singleton-is-prop (fe 𝓤 𝓤)
hlevel-relation-is-prop {𝓤} (succ n) X =
  Π₂-is-prop fe'
             (λ x x' → hlevel-relation-is-prop n (x ＝ x'))

\end{code}

H-Levels are cumulative.

\begin{code}

hlevels-are-upper-closed : (n : ℕ) (X : 𝓤 ̇)
                         → (X is-of-hlevel n)
                         → (X is-of-hlevel succ n)
hlevels-are-upper-closed zero X h-level = base h-level
 where
  base : is-contr X → (x x' : X) → is-contr (x ＝ x')
  base (c , C) x x' = (((C x)⁻¹ ∙ C x') , D)
   where
    D : is-central (x ＝ x') (C x ⁻¹ ∙ C x')
    D refl = left-inverse (C x)
hlevels-are-upper-closed (succ n) X h-level = step
 where
  step : (x x' : X) (p q : x ＝ x') → (p ＝ q) is-of-hlevel n
  step x x' p q = hlevels-are-upper-closed n (x ＝ x') (h-level x x') p q

\end{code}

We will now give some closure results about H-levels.

\begin{code}

hlevel-closed-under-retract : (n : ℕ)
                            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                            → retract X of Y
                            → Y is-of-hlevel n
                            → X is-of-hlevel n
hlevel-closed-under-retract zero X Y X-retract-Y Y-contr =
  singleton-closed-under-retract X Y X-retract-Y Y-contr
hlevel-closed-under-retract (succ n) X Y (r , s , H) Y-h-level x x' =
  hlevel-closed-under-retract n (x ＝ x') (s x ＝ s x') retr
                              (Y-h-level (s x) (s x'))
 where
  t : (s x ＝ s x') → x ＝ x'
  t q = H x ⁻¹ ∙ ap r q ∙ H x'
  G : (p : x ＝ x') → H x ⁻¹ ∙ ap r (ap s p) ∙ H x' ＝ p
  G refl = left-inverse (H x)
  retr : retract x ＝ x' of (s x ＝ s x')
  retr = (t , ap s , G)

hlevel-closed-under-equiv : (n : ℕ)
                          → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                          → X ≃ Y
                          → Y is-of-hlevel n
                          → X is-of-hlevel n
hlevel-closed-under-equiv n X Y e =
  hlevel-closed-under-retract n X Y (≃-gives-◁ e)

\end{code}

We can prove closure under embeddings as a consequence of the previous result.

\begin{code}

hlevel-closed-under-embedding : (n : ℕ)
                              → 1 ≤ℕ n
                              → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                              → X ↪ Y
                              → Y is-of-hlevel n
                              → X is-of-hlevel n
hlevel-closed-under-embedding
  (succ n) n-above-one X Y (e , is-emb) Y-h-level x x' =
    hlevel-closed-under-equiv n (x ＝ x') (e x ＝ e x')
                              (ap e , embedding-gives-embedding' e is-emb x x')
                              (Y-h-level (e x) (e x'))

\end{code}

Using closure under equivalence we can show closure under Σ and Π.

\begin{code}

hlevel-closed-under-Σ : (n : ℕ)
                      → (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                      → X is-of-hlevel n
                      → ((x : X) → (Y x) is-of-hlevel n)
                      → (Σ Y) is-of-hlevel n
hlevel-closed-under-Σ zero X Y l m = Σ-is-singleton l m
hlevel-closed-under-Σ (succ n) X Y l m (x , y) (x' , y') =
  hlevel-closed-under-equiv n ((x , y) ＝ (x' , y'))
                            (Σ p ꞉ x ＝ x' , transport Y p y ＝ y') Σ-＝-≃
                            (hlevel-closed-under-Σ n (x ＝ x')
                                                   (λ p → transport Y p y ＝ y')
                                                   (l x x')
                                                   (λ p → m x'
                                                            (transport Y p y)
                                                            y'))

hlevel-closed-under-Π : {𝓤 𝓥 : Universe}
                      → (n : ℕ)
                      → (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                      → ((x : X) → (Y x) is-of-hlevel n)
                      → (Π Y) is-of-hlevel n
hlevel-closed-under-Π {𝓤} {𝓥} zero X Y m = Π-is-singleton (fe 𝓤 𝓥) m
hlevel-closed-under-Π {𝓤} {𝓥} (succ n) X Y m f g = 
  hlevel-closed-under-equiv n (f ＝ g) (f ∼ g) (happly-≃ (fe 𝓤 𝓥))
                            (hlevel-closed-under-Π n X (λ x → f x ＝ g x)
                                                   (λ x → m x (f x) (g x)))

hlevel-closed-under-→ : {𝓤 𝓥 : Universe}
                      → (n : ℕ)
                      → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                      → Y is-of-hlevel n
                      → (X → Y) is-of-hlevel n
hlevel-closed-under-→ n X Y m = hlevel-closed-under-Π n X (λ - → Y) (λ - → m)

\end{code}

The subuniverse of types of hlevel n is defined as follows.

\begin{code}

ℍ : ℕ → (𝓤 : Universe) → 𝓤 ⁺ ̇
ℍ n 𝓤 = Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n

\end{code}

Being of hlevel one is equivalent to being a proposition.
We will quickly demonstrate this fact. 

\begin{code}

is-prop' : (X : 𝓤 ̇) → 𝓤  ̇
is-prop' X = X is-of-hlevel (succ zero)

being-prop'-is-prop : (X : 𝓤 ̇) → is-prop (is-prop' X)
being-prop'-is-prop X = hlevel-relation-is-prop (succ zero) X

is-prop-implies-is-prop' : {X : 𝓤 ̇} → is-prop X → is-prop' X
is-prop-implies-is-prop' X-is-prop x x' =
  pointed-props-are-singletons (X-is-prop x x') (props-are-sets X-is-prop)

is-prop'-implies-is-prop : {X : 𝓤 ̇} → is-prop' X → is-prop X
is-prop'-implies-is-prop X-is-prop' x x' = center (X-is-prop' x x')

is-prop-equiv-is-prop' : {𝓤 : Universe} {X :  𝓤 ̇} → is-prop X ≃ is-prop' X
is-prop-equiv-is-prop' {𝓤} {X} =
  logically-equivalent-props-are-equivalent (being-prop-is-prop (fe 𝓤 𝓤))
                                            (being-prop'-is-prop X)
                                            is-prop-implies-is-prop'
                                            is-prop'-implies-is-prop

\end{code}

From Univalence we can show that (ℍ n) is of level (n + 1), for all n : ℕ.

\begin{code}

ℍ-is-of-next-hlevel : (n : ℕ)
                    → (𝓤 : Universe)
                    → is-univalent 𝓤
                    → (ℍ n 𝓤) is-of-hlevel (succ n)
ℍ-is-of-next-hlevel zero 𝓤 ua = C
 where
  C : (X X' : ℍ zero 𝓤) → is-contr (X ＝ X')
  C (X , X-is-contr) (X' , X'-is-contr) =
    hlevel-closed-under-equiv zero ((X , X-is-contr) ＝ (X' , X'-is-contr))
                              (X ≃ X') e C'
   where
    e = ((X , X-is-contr) ＝ (X' , X'-is-contr)) ≃⟨ ≃-sym (to-subtype-＝-≃
                                                  (λ X → being-singleton-is-prop
                                                         (fe 𝓤 𝓤))) ⟩
        (X ＝ X')                                ≃⟨ univalence-≃ ua X X' ⟩
        (X ≃ X')                                 ■
    P : is-prop (X ≃ X')
    P = ≃-is-prop fe (is-prop'-implies-is-prop
                        (hlevels-are-upper-closed zero X' X'-is-contr))
    C' : is-contr (X ≃ X')
    C' = pointed-props-are-singletons (singleton-≃ X-is-contr X'-is-contr) P
ℍ-is-of-next-hlevel (succ n) 𝓤 ua (X , l) (X' , l') =
  hlevel-closed-under-equiv (succ n) ((X , l) ＝ (X' , l')) (X ≃ X') e
      (hlevel-closed-under-embedding (succ n) ⋆ (X ≃ X') (X → X') e'
                                     (hlevel-closed-under-Π (succ n) X
                                                            (λ _ → X')
                                                            (λ x x' → l' x')))
  where
   e = ((X , l) ＝ (X' , l')) ≃⟨ ≃-sym (to-subtype-＝-≃
                                  (λ _ → Π-is-prop (fe 𝓤 𝓤)
                                  (λ x → Π-is-prop (fe 𝓤 𝓤)
                                  (λ x' → hlevel-relation-is-prop
                                            n (x ＝ x'))))) ⟩
       (X ＝ X')              ≃⟨ univalence-≃ ua X X' ⟩
       (X ≃ X')               ■

   e' : (X ≃ X') ↪ (X → X')
   e' = (pr₁ , pr₁-is-embedding (λ f → being-equiv-is-prop fe f))

\end{code}

We now define the notion of a k-truncation using record types.

\begin{code}

record H-level-truncations-exist : 𝓤ω where
 field
  ∣∣_∣∣[_] : {𝓤 : Universe} → 𝓤 ̇ → ℕ → 𝓤 ̇
  ∣∣∣∣-h-level : {𝓤 : Universe} {X : 𝓤 ̇ } (n : ℕ) → X is-of-hlevel n
  ∣_∣[_] :  {𝓤 : Universe} {X : 𝓤 ̇ } → X → (n : ℕ) → ∣∣ X ∣∣[ n ]
  ∣∣∣∣-ind : {X : 𝓤 ̇ } {n : ℕ} {P : ∣∣ X ∣∣[ n ] → 𝓥 ̇ }
           → ((s : ∣∣ X ∣∣[ n ]) → (P s) is-of-hlevel n)
           → ((x : X) → P (∣ x ∣[ n ]))
           → (s : ∣∣ X ∣∣[ n ]) → P s
  ∣∣∣∣-ind-comp : {X : 𝓤 ̇ } {n : ℕ} {P : ∣∣ X ∣∣[ n ] → 𝓥 ̇ }
                → (m : (s : ∣∣ X ∣∣[ n ]) → (P s) is-of-hlevel n)
                → (g : (x : X) → P (∣ x ∣[ n ]))
                → (x : X) → ∣∣∣∣-ind m g (∣ x ∣[ n ]) ＝ g x
 infix 0 ∣∣_∣∣[_]
 infix 0 ∣_∣[_]

\end{code}

We add truncation recursion.

\begin{code}

module GeneralTruncations
        (te : H-level-truncations-exist)
        (ua : Univalence)
       where

 open H-level-truncations-exist te

 ∣∣∣∣-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
          → Y is-of-hlevel n → (X → Y) → ∣∣ X ∣∣[ n ] → Y
 ∣∣∣∣-rec {𝓤} {𝓥} {X} {Y} {n} Y-h-level f s = ∣∣∣∣-ind (λ - → Y-h-level) f s

 ∣∣∣∣-rec-comp : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
               → (m : Y is-of-hlevel n)
               → (g : X → Y)
               → (x : X) → ∣∣∣∣-rec m g ∣ x ∣[ n ] ＝ g x
 ∣∣∣∣-rec-comp m g = ∣∣∣∣-ind-comp (λ - → m) g

 ∣∣∣∣-rec-double : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
                 → Z is-of-hlevel n
                 → (X → Y → Z)
                 → ∣∣ X ∣∣[ n ] → ∣∣ Y ∣∣[ n ] → Z
 ∣∣∣∣-rec-double {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} Z-h-level g =
  ∣∣∣∣-rec (hlevel-closed-under-→ n (∣∣ Y ∣∣[ n ]) Z Z-h-level)
           (λ x → ∣∣∣∣-rec Z-h-level (λ y → g x y))

 ∣∣∣∣-rec-double-comp : {𝓤 𝓥 𝓦 : Universe}
                        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
                      → (m : Z is-of-hlevel n)
                      → (g : X → Y → Z)
                      → (x : X) → (y : Y)
                      → ∣∣∣∣-rec-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
 ∣∣∣∣-rec-double-comp {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {n} m g x y =
  ∣∣∣∣-rec-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ happly
                                              (∣∣∣∣-rec-comp
                                              (hlevel-closed-under-→ n
                                                (∣∣ Y ∣∣[ n ]) Z m)
                                              (λ x → ∣∣∣∣-rec m (λ y → g x y)) x)
                                              ∣ y ∣[ n ]  ⟩
  ∣∣∣∣-rec m (λ y → g x y) ∣ y ∣[ n ]       ＝⟨ ∣∣∣∣-rec-comp m (λ y → g x y) y ⟩
  g x y                                     ∎

 abstract
  ∣∣∣∣-ind-double : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                    {P : ∣∣ X ∣∣[ n ] → ∣∣ Y ∣∣[ n ] → 𝓦 ̇ } 
                  → ((u : ∣∣ X ∣∣[ n ]) → (v : ∣∣ Y ∣∣[ n ])
                   → (P u v) is-of-hlevel n)
                  → ((x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
                  → (u : ∣∣ X ∣∣[ n ]) → (v : ∣∣ Y ∣∣[ n ]) → P u v
  ∣∣∣∣-ind-double {𝓤} {𝓥} {𝓦} {X} {Y} {n} {P} P-h-level f =
   ∣∣∣∣-ind (λ u → hlevel-closed-under-Π n ∣∣ Y ∣∣[ n ] (P u)
                                         (λ v → P-h-level u v))
            (λ x → ∣∣∣∣-ind (λ v → P-h-level ∣ x ∣[ n ] v) (λ y → f x y))

  ∣∣∣∣-ind-double-comp : {𝓤 𝓥 𝓦 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
                         {P : ∣∣ X ∣∣[ n ] → ∣∣ Y ∣∣[ n ] → 𝓦 ̇ } 
                       → (m : (u : ∣∣ X ∣∣[ n ]) → (v : ∣∣ Y ∣∣[ n ])
                        → (P u v) is-of-hlevel n)
                       → (g : (x : X) → (y : Y) → P (∣ x ∣[ n ]) (∣ y ∣[ n ]))
                       → (x : X) → (y : Y)
                       → ∣∣∣∣-ind-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝ g x y
  ∣∣∣∣-ind-double-comp {𝓤} {𝓥} {𝓦} {X} {Y} {n} {P} m g x y =
   ∣∣∣∣-ind-double m g ∣ x ∣[ n ] ∣ y ∣[ n ] ＝⟨ happly
                                                (∣∣∣∣-ind-comp
                                                 (λ u → hlevel-closed-under-Π
                                                  n ∣∣ Y ∣∣[ n ] (P u)
                                                  (λ v → m u v))
                                                 (λ x' → ∣∣∣∣-ind
                                                  (λ v → m ∣ x' ∣[ n ] v)
                                                  (λ y' → g x' y')) x)
                                                ∣ y ∣[ n ] ⟩
   ∣∣∣∣-ind (λ v → m ∣ x ∣[ n ] v)
            (λ y' → g x y') ∣ y ∣[ n ]       ＝⟨ ∣∣∣∣-ind-comp
                                                 (λ v → m ∣ x ∣[ n ] v)
                                                 (λ y' → g x y') y ⟩
   g x y                                     ∎

\end{code}

We now set out to define a critical eqeuivalence that characterizes the
truncated identity type.

\begin{code}

 canonical-id-trunc-map : {𝓤 : Universe} {X : 𝓤 ̇} {x y : X} {n : ℕ}
                        → ∣∣ x ＝ y ∣∣[ n ]
                        → ∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ]
 canonical-id-trunc-map {𝓤} {X} {x} {y} {n} =
  ∣∣∣∣-rec (∣∣∣∣-h-level n) (ap (λ x → ∣ x ∣[ (succ n) ]))

 private
  P' : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
    → ∣∣ X ∣∣[ succ n ] → ∣∣ X ∣∣[ succ n ] → ℍ n 𝓤
  P' {𝓤} {X} {n} =
   ∣∣∣∣-rec-double (ℍ-is-of-next-hlevel n 𝓤 (ua 𝓤))
                   (λ x x' → (∣∣ x ＝ x' ∣∣[ n ] , ∣∣∣∣-h-level n))

  P : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
    → ∣∣ X ∣∣[ succ n ] → ∣∣ X ∣∣[ succ n ] → 𝓤 ̇
  P u v = pr₁ (P' u v)

  P-computes : {𝓤 : Universe} {X : 𝓤 ̇} {x y : X} {n : ℕ}
             → P ∣ x ∣[ succ n ] ∣ y ∣[ succ n ] ＝ ∣∣ x ＝ y ∣∣[ n ]
  P-computes {𝓤} {X} {x} {y} {n} =
   ap pr₁ (∣∣∣∣-rec-double-comp (ℍ-is-of-next-hlevel n 𝓤 (ua 𝓤))
        (λ x x' → (∣∣ x ＝ x' ∣∣[ n ] , ∣∣∣∣-h-level n)) x y)

 gen-trunc-id-type-char : {𝓤 : Universe} {X : 𝓤 ̇} {n : ℕ}
                        → (u v : ∣∣ X ∣∣[ succ n ])
                        → P u v ≃ (u ＝ v)
 gen-trunc-id-type-char {𝓤} {X} {n} u v =
  (decode u v , qinvs-are-equivs (decode u v) (encode u v , H u v , G u v))
  where
   decode : (u v : ∣∣ X ∣∣[ succ n ])
          → P u v → u ＝ v
   decode =
    ∣∣∣∣-ind-double (λ u v → hlevel-closed-under-→ (succ n) (P u v) (u ＝ v)
                                                   (∣∣∣∣-h-level (succ n)))
                    (λ x y → transport (λ T →
                                        T → ∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ])
                                       (P-computes ⁻¹)
                                       canonical-id-trunc-map)
   P-refl : (u : ∣∣ X ∣∣[ succ n ]) → P u u
   P-refl = ∣∣∣∣-ind (λ - → ∣∣∣∣-h-level (succ n))
                     (λ x → transport (λ - → -) (P-computes ⁻¹) ∣ refl ∣[ n ] )
   encode : (u v : ∣∣ X ∣∣[ succ n ])
          → u ＝ v → P u v
   encode u v p = transport (λ v' → P u v') p (P-refl u)
   H : (u v : ∣∣ X ∣∣[ succ n ]) → encode u v ∘ decode u v ∼ id
   H = ∣∣∣∣-ind-double {𝓤} {𝓤} {𝓤} {X} {X} {succ n}
                       {λ u v → encode u v ∘ decode u v ∼ id}
                       (λ - - → (λ - - → ∣∣∣∣-h-level n)) H'
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
   G : (u v : ∣∣ X ∣∣[ succ n ]) → decode u v ∘ encode u v ∼ id 
   G u .u refl = ∣∣∣∣-ind {𝓤} {𝓤} {X} {succ n}
                          {λ u → (decode u u ∘ encode u u) refl ＝ refl}
                          (λ - → ∣∣∣∣-h-level (succ n)) G' u
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
                    → ∣∣ x ＝ y ∣∣[ n ]
                    ≃ (∣ x ∣[ succ n ] ＝ ∣ y ∣[ succ n ])
 trunc-id-type-char {𝓤} {X} {x} {y} {n} =
  ≃-comp (idtoeq ∣∣ x ＝ y ∣∣[ n ]
                 (P ∣ x ∣[ succ n ] ∣ y ∣[ succ n ])
                 (P-computes ⁻¹))
         (gen-trunc-id-type-char ∣ x ∣[ succ n ] ∣ y ∣[ succ n ])

\end{code}

{𝓤} {𝓤} {X} {succ n}
{λ u → (decode u u ∘ encode u u) refl ＝ refl}

We now add some code that allows us to identify the 1-truncation and
propositional truncation:
  ∣∣ X ∣∣₁ ≃ ∥ X ∥

\begin{code}

module _ (te : H-level-truncations-exist)
         (pt : propositional-truncations-exist)
         (ua : Univalence)
          where

 open H-level-truncations-exist te
 open GeneralTruncations te ua
 open propositional-truncations-exist pt

 1-trunc-is-prop : {X : 𝓤 ̇} → is-prop (∣∣ X ∣∣[ 1 ])
 1-trunc-is-prop = is-prop'-implies-is-prop (∣∣∣∣-h-level 1)

 1-trunc-≃-prop-trunc : {X : 𝓤 ̇}
                      → (∣∣ X ∣∣[ 1 ]) ≃ ∥ X ∥
 1-trunc-≃-prop-trunc {𝓤} {X} =
  logically-equivalent-props-are-equivalent 1-trunc-is-prop ∥∥-is-prop ϕ ψ
  where
   ϕ : ∣∣ X ∣∣[ 1 ] → ∥ X ∥
   ϕ = ∣∣∣∣-rec (is-prop-implies-is-prop' ∥∥-is-prop) ∣_∣
   ψ : ∥ X ∥ → ∣∣ X ∣∣[ 1 ]
   ψ = ∥∥-rec 1-trunc-is-prop (λ x → ∣ x ∣[ 1 ])

\end{code}

We now add the notion of k-connectedness of type and functions with respect to
H-levels. TODO: Show that connectedness as defined elsewhere in the
library is a special case of what follows.

\begin{code}

module k-connectedness
        (te : H-level-truncations-exist)
        (ua : Univalence)
       where

 open H-level-truncations-exist te

 _is_connected : 𝓤 ̇ → ℕ → 𝓤 ̇
 X is k connected = is-contr (∣∣ X ∣∣[ k ])

 map_is_connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ → 𝓤 ⊔ 𝓥 ̇
 map f is k connected = (y : codomain f) → (fiber f y) is k connected

\end{code}

We now add some results about connectedness.

\begin{code}

 open propositional-truncations-exist pt
 open GeneralTruncations te ua

 connected-characterization : {X : 𝓤 ̇} {n : ℕ}
                            → X is (succ n) connected
                            ↔ ∥ X ∥ × ((x y : X) → (x ＝ y) is n connected)
 connected-characterization {𝓤} {X} {zero} = (left-to-right , {!!})
  where
   left-to-right : X is 1 connected
                 → ∥ X ∥ × ((x y : X) → (x ＝ y) is zero connected)
   left-to-right X-is-conn =
    (center (equiv-to-singleton' (1-trunc-≃-prop-trunc te pt ua) X-is-conn)
     , {!!})
 connected-characterization {𝓤} {X} {succ n} = ({!!} , {!!})


 ap-is-less-connected : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y)
                      → (n : ℕ)
                      → map f is (succ n) connected
                      → map (ap f) is n connected
 ap-is-less-connected = {!!}

\end{code}
