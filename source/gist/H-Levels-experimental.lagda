Ian Ray, 2 June 2024

Experimental modification by Martin Escardo 11 September 2024

Minor modifications by Tom de Jong on 4 September 2024

We develop H-levels (a la Voevodsky). In Homotopy Type Theory there is a
natural stratification of types defined inductively; with contractible
types as the base and saying an (n+1)-type is a type whose identity types
are all n-types. Voevodsky introduced the notion of H-level where contractible
types are at level n = 0. Alternatively, in book HoTT, truncated types are
defined so that contractible types are at level k = -2. Of course, the two
notions are equivalent as they are indexed by equivalent types, that is
ℕ ≃ ℤ₋₂, but it is important to be aware of the fact that concepts are 'off by
2' when translating between conventions.

In this file we will assume function extensionality globally but not univalence.
The final result of the file will be proved in the local presence of univalence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module gist.H-Levels-experimental
        (fe : Fun-Ext)
       where

open import MLTT.Spartan

open import Naturals.Order

open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Retracts
open import UF.Singleton-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence


open import gist.FromMinus2
open import Notation.Order

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

_is-of-hlevel_ : 𝓤 ̇ → ℕ₋₂ → 𝓤 ̇
X is-of-hlevel −2       = is-contr X
X is-of-hlevel minus1 n = (x x' : X) → (x ＝ x') is-of-hlevel minus2 n

hlevel-relation-is-prop : {𝓤 : Universe} {n : ℕ₋₂} {X : 𝓤 ̇ }
                        → is-prop (X is-of-hlevel n)
hlevel-relation-is-prop {𝓤} {−2}       = being-singleton-is-prop fe
hlevel-relation-is-prop {𝓤} {minus1 n} =
  Π₂-is-prop fe (λ x x' → hlevel-relation-is-prop)

map_is-of-hlevel_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (f : X → Y) → ℕ₋₂ → 𝓤 ⊔ 𝓥 ̇
map f is-of-hlevel n = each-fiber-of f (λ - → - is-of-hlevel n)

\end{code}

Being of hlevel one is equivalent to being a proposition.

\begin{code}

is-prop' : (X : 𝓤 ̇) → 𝓤  ̇
is-prop' X = X is-of-hlevel −1

being-prop'-is-prop : (X : 𝓤 ̇) → is-prop (is-prop' X)
being-prop'-is-prop X = hlevel-relation-is-prop

is-prop-implies-is-prop' : {X : 𝓤 ̇} → is-prop X → is-prop' X
is-prop-implies-is-prop' X-is-prop x x' =
 pointed-props-are-singletons (X-is-prop x x') (props-are-sets X-is-prop)

is-prop'-implies-is-prop : {X : 𝓤 ̇} → is-prop' X → is-prop X
is-prop'-implies-is-prop X-is-prop' x x' = center (X-is-prop' x x')

is-prop-equiv-is-prop' : {X : 𝓤 ̇} → is-prop X ≃ is-prop' X
is-prop-equiv-is-prop' {𝓤} {X} =
 logically-equivalent-props-are-equivalent (being-prop-is-prop fe)
                                           (being-prop'-is-prop X)
                                           is-prop-implies-is-prop'
                                           is-prop'-implies-is-prop

\end{code}

H-Levels are cumulative.

\begin{code}

contr-implies-id-contr : {X : 𝓤 ̇} → is-contr X → is-prop' X
contr-implies-id-contr = is-prop-implies-is-prop' ∘ singletons-are-props

hlevels-are-upper-closed : {n : ℕ₋₂} {X : 𝓤 ̇ }
                         → X is-of-hlevel n
                         → X is-of-hlevel (suc n)
hlevels-are-upper-closed {𝓤} {−2} = contr-implies-id-contr
hlevels-are-upper-closed {𝓤} {minus1 n} h-level x x' =
 hlevels-are-upper-closed (h-level x x')

hlevels-are-closed-under-id : {n : ℕ₋₂} {X : 𝓤 ̇ }
                            → X is-of-hlevel n
                            → (x x' : X) → (x ＝ x') is-of-hlevel n
hlevels-are-closed-under-id {𝓤} {−2} = contr-implies-id-contr
hlevels-are-closed-under-id {𝓤} {minus1 n} X-hlev x x' =
  hlevels-are-upper-closed (X-hlev x x')

\end{code}

We will now give some closure results about H-levels.

\begin{code}

hlevel-closed-under-retract : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → retract X of Y
                            → Y is-of-hlevel n
                            → X is-of-hlevel n
hlevel-closed-under-retract {𝓤} {𝓥} {−2} {X} {Y} X-retract-Y Y-contr =
 singleton-closed-under-retract X Y X-retract-Y Y-contr
hlevel-closed-under-retract {𝓤} {𝓥} {minus1 n} (r , s , H) Y-h-level x x' =
 hlevel-closed-under-retract (＝-retract s (r , H) x x') (Y-h-level (s x) (s x'))

hlevel-closed-under-equiv : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → X ≃ Y
                          → Y is-of-hlevel n
                          → X is-of-hlevel n
hlevel-closed-under-equiv e = hlevel-closed-under-retract (≃-gives-◁ e)

\end{code}

We can prove closure under embeddings as a consequence of the previous result.

\begin{code}

hlevel-closed-under-embedding : {n : ℕ₋₂}
                              → −1 ≤ n
                              → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                              → X ↪ Y
                              → Y is-of-hlevel n
                              → X is-of-hlevel n
hlevel-closed-under-embedding {𝓤} {𝓥} {minus1 n} _ (e , is-emb) Y-h-level x x' =
 hlevel-closed-under-equiv (ap e , embedding-gives-embedding' e is-emb x x')
                           (Y-h-level (e x) (e x'))

\end{code}

Using closure under equivalence we can show closure under Σ and Π.

\begin{code}

hlevel-closed-under-Σ : {n : ℕ₋₂} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
                      → X is-of-hlevel n
                      → ((x : X) → (Y x) is-of-hlevel n)
                      → (Σ Y) is-of-hlevel n
hlevel-closed-under-Σ {𝓤} {𝓥} {−2} Y l m = Σ-is-singleton l m
hlevel-closed-under-Σ {𝓤} {𝓥} {minus1 n} Y l m (x , y) (x' , y') =
 hlevel-closed-under-equiv Σ-＝-≃
  (hlevel-closed-under-Σ
   (λ p → transport Y p y ＝ y')
   (l x x')
   (λ p → m x' (transport Y p y) y'))

hlevel-closed-under-Π : {n : ℕ₋₂} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ )
                      → ((x : X) → (Y x) is-of-hlevel n)
                      → (Π Y) is-of-hlevel n
hlevel-closed-under-Π {𝓤} {𝓥} {−2} Y m = Π-is-singleton fe m
hlevel-closed-under-Π {𝓤} {𝓥} {minus1 n} Y m f g =
 hlevel-closed-under-equiv (happly-≃ fe)
  (hlevel-closed-under-Π (λ x → f x ＝ g x)
  (λ x → m x (f x) (g x)))

hlevel-closed-under-→ : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → Y is-of-hlevel n
                      → (X → Y) is-of-hlevel n
hlevel-closed-under-→ {𝓤} {𝓥} {n} {X} {Y} m =
 hlevel-closed-under-Π (λ - → Y) (λ - → m)

\end{code}

The subuniverse of types of hlevel n is defined as follows.

\begin{code}

ℍ : ℕ₋₂ → (𝓤 : Universe) → 𝓤 ⁺ ̇
ℍ n 𝓤 = Σ X ꞉ 𝓤 ̇ , X is-of-hlevel n

\end{code}

From univalence we can show that ℍ n is of level (n + 1), for all n : ℕ₋₂.

\begin{code}

equiv-preserves-hlevel : {n : ℕ₋₂} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                       → X is-of-hlevel n
                       → Y is-of-hlevel n
                       → (X ≃ Y) is-of-hlevel n
equiv-preserves-hlevel {𝓤} {𝓥} {−2} = ≃-is-singleton fe'
equiv-preserves-hlevel {𝓤} {𝓥} {minus1 n} {X} {Y} X-h-lev Y-h-lev =
 hlevel-closed-under-embedding ⋆ (equiv-embeds-into-function fe')
  (hlevel-closed-under-Π (λ _ → Y) (λ _ → Y-h-lev))

ℍ-is-of-next-hlevel : {n : ℕ₋₂} {𝓤 : Universe}
                    → is-univalent 𝓤
                    → (ℍ n 𝓤) is-of-hlevel suc n
ℍ-is-of-next-hlevel ua (X , l) (Y , l') =
 hlevel-closed-under-equiv I (equiv-preserves-hlevel l l')
 where
  I = ((X , l) ＝ (Y , l')) ≃⟨ II ⟩
       (X ＝ Y)             ≃⟨ univalence-≃ ua X Y ⟩
       (X ≃ Y)              ■
   where
    II = ≃-sym (to-subtype-＝-≃ (λ _ → hlevel-relation-is-prop))

\end{code}
