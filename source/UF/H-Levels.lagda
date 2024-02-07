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

In this file we will assume function extensionality but not univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.IdentitySystems
open import UF.Retracts
open import UF.Sets
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.UA-FunExt
open import Naturals.Order

module UF.H-Levels (fe : FunExt) (fe' : Fun-Ext) where

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

Some of the next results, left-inv and base, SHOULD be somewhere but I can't
find them...

\begin{code}

hlevel-is-cummulative : (n : ℕ) (X : 𝓤 ̇)
                      → (X is-of-hlevel n)
                      → (X is-of-hlevel succ n)
hlevel-is-cummulative zero X h-level = base h-level
 where
  base : is-contr X → (x x' : X) → is-contr (x ＝ x')
  base (c , C) x x' = (((C x)⁻¹ ∙ C x') , D)
   where
    D : is-central (x ＝ x') (C x ⁻¹ ∙ C x')
    D refl = left-inverse (C x)
hlevel-is-cummulative (succ n) X h-level = step
 where
  step : (x x' : X) (p q : x ＝ x') → (p ＝ q) is-of-hlevel n
  step x x' p q = hlevel-is-cummulative n (x ＝ x') (h-level x x') p q

\end{code}

We will now give some closure results about H-levels.

\begin{code}

hlevel-closed-under-retracts : (n : ℕ)
                             → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                             → retract X of Y
                             → Y is-of-hlevel n
                             → X is-of-hlevel n
hlevel-closed-under-retracts zero X Y X-retract-Y Y-contr =
  singleton-closed-under-retract X Y X-retract-Y Y-contr
hlevel-closed-under-retracts (succ n) X Y (r , s , H) Y-h-level x x' =
  hlevel-closed-under-retracts n (x ＝ x') (s x ＝ s x') retr
                               (Y-h-level (s x) (s x'))
 where
  t : (s x ＝ s x') → x ＝ x'
  t q = H x ⁻¹ ∙ ap r q ∙ H x'
  G : (p : x ＝ x') → H x ⁻¹ ∙ ap r (ap s p) ∙ H x' ＝ p
  G refl = left-inverse (H x)
  retr : retract x ＝ x' of (s x ＝ s x')
  retr = (t , ap s , {!G!})

hlevel-closed-under-equiv : (n : ℕ)
                          → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                          → X ≃ Y
                          → Y is-of-hlevel n
                          → X is-of-hlevel n
hlevel-closed-under-equiv n X Y (f , has-sec , g , is-sec) =
  hlevel-closed-under-retracts n X Y (g , f , is-sec)

\end{code}

The above would be conceptually clearer if we had

  X ≃ Y → retract X of Y

\begin{code}

hlevels-closed-under-embeddings : (n : ℕ)
                                → 1 ≤ℕ n
                                → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                                → X ↪ Y
                                → Y is-of-hlevel n
                                → X is-of-hlevel n
hlevels-closed-under-embeddings
  (succ n) n-above-one X Y (e , is-emb) Y-h-level x x' =
    hlevel-closed-under-equiv n (x ＝ x') (e x ＝ e x')
                              (ap e , embedding-gives-embedding' e is-emb x x')
                              (Y-h-level (e x) (e x'))

\end{code}

Using closure under equivalence we can show closure under Σ and Π.

\begin{code}

hlevel-closed-under-Σ : (n : ℕ)
                      → (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
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

hlevel-closed-under-Π : {𝓤 : Universe}
                       → (n : ℕ)
                       → (X : 𝓤 ̇ ) (Y : X → 𝓤 ̇ )
                       → ((x : X) → (Y x) is-of-hlevel n)
                       → (Π Y) is-of-hlevel n
hlevel-closed-under-Π {𝓤} zero X Y m = Π-is-singleton (fe 𝓤 𝓤) m
hlevel-closed-under-Π {𝓤} (succ n) X Y m f g =
  hlevel-closed-under-equiv n (f ＝ g) (f ∼ g) (happly-≃ (fe 𝓤 𝓤))
                            (hlevel-closed-under-Π n X (λ x → f x ＝ g x)
                                                   (λ x → m x (f x) (g x)))

\end{code}

The subuniverse of types of hlevel n:

\begin{code}

ℍ : ℕ → (𝓤 : Universe) → 𝓤 ⁺ ̇
ℍ n 𝓤 = Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n

\end{code}
