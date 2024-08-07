Martin Escardo and Ian Ray, 06/02/2024

We develop H-levels (a la Voevodsky). In Homotopy Type Theory there is a
natural stratification of types defined inductively; with contractible
types as the base and saying an (n+1)-type has identity type that is an n-type.
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
open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.Order

module UF.H-Levels (fe : FunExt)
                   (fe' : Fun-Ext)
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

map_is-of-hlevel_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ → 𝓤 ⊔ 𝓥 ̇
map f is-of-hlevel n = (y : codomain f) → (fiber f y) is-of-hlevel n

\end{code}

H-Levels are cumulative.

\begin{code}

contr-implies-id-contr : {X : 𝓤 ̇} → is-contr X → (x x' : X) → is-contr (x ＝ x')
contr-implies-id-contr (c , C) x x' = (((C x)⁻¹ ∙ C x') , D)
 where
  D : is-central (x ＝ x') (C x ⁻¹ ∙ C x')
  D refl = left-inverse (C x)

hlevels-are-upper-closed : (n : ℕ) (X : 𝓤 ̇)
                         → (X is-of-hlevel n)
                         → (X is-of-hlevel succ n)
hlevels-are-upper-closed zero X h-level = contr-implies-id-contr h-level

hlevels-are-upper-closed (succ n) X h-level = step
 where
  step : (x x' : X) (p q : x ＝ x') → (p ＝ q) is-of-hlevel n
  step x x' p q = hlevels-are-upper-closed n (x ＝ x') (h-level x x') p q

id-types-are-same-hlevel : {X : 𝓤 ̇ } (n : ℕ)
                         → X is-of-hlevel n
                         → (x x' : X) → (x ＝ x') is-of-hlevel n
id-types-are-same-hlevel zero X-hlev x x' = contr-implies-id-contr X-hlev x x'
id-types-are-same-hlevel (succ n) X-hlev x x' =
  hlevels-are-upper-closed n (x ＝ x') (X-hlev x x')

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

