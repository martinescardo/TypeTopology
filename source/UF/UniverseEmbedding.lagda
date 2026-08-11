Martin Escardo, 29th January 2019

If univalence holds, then any universe is embedded into any larger
universe.

We do this without cumulativity, because it is not available in the
Martin-Löf type theory that we are working with in Agda.

Moreover, any map f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ with f X ≃ X for all X : 𝓤 ̇ is an
embedding, e.g. the map X ↦ X + 𝟘 {𝓥}.

(Here the notion of a map being an embedding is stronger than that of
being left-cancellable, and it means that the fibers of the map are
propositions, or subsingletons, as in HoTT/UF.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.UniverseEmbedding where

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.PairFun
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

is-universe-embedding : (𝓤 ̇ → 𝓥 ̇ ) → (𝓤 ⁺) ⊔ 𝓥 ̇
is-universe-embedding f = ∀ X → f X ≃ X

\end{code}

Of course:

\begin{code}

at-most-one-universe-embedding : Univalence
                               → (f g : 𝓤 ̇ → 𝓥 ̇ )
                               → is-universe-embedding f
                               → is-universe-embedding g
                               → f ＝ g
at-most-one-universe-embedding {𝓤} {𝓥} ua f g i j = p
 where
  h : ∀ X → f X ≃ g X
  h X = i X ● ≃-sym (j X)

  H : f ∼ g
  H X = eqtoid (ua 𝓥) (f X) (g X) (h X)

  p : f ＝ g
  p = dfunext (Univalence-gives-Fun-Ext ua) H

universe-embeddings-are-embeddings : Univalence
                                   → (𝓤 𝓥 : Universe)
                                     (f : 𝓤 ̇ → 𝓥 ̇ )
                                   → is-universe-embedding f
                                   → is-embedding f
universe-embeddings-are-embeddings ua 𝓤 𝓥 f i = δ
 where
  γ : (X X' : 𝓤 ̇ ) → (f X ＝ f X') ≃ (X ＝ X')
  γ X X' =  (f X ＝ f X')  ≃⟨ a ⟩
            (f X ≃ f X')  ≃⟨ b ⟩
            (X ≃ X')      ≃⟨ c ⟩
            (X ＝ X')      ■
   where
    a = univalence-≃ (ua 𝓥) (f X) (f X')
    b = ≃-cong (Univalence-gives-FunExt ua) (i X) (i X')
    c = ≃-sym (univalence-≃ (ua 𝓤) X X')

  δ : is-embedding f
  δ = embedding-criterion' f γ

\end{code}

For instance, the following function satisfies this condition and
hence is an embedding:

\begin{code}

Lift' : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Lift' 𝓥 X = X + 𝟘 {𝓥}

lift' : (𝓥 : Universe) {X : 𝓤 ̇ } → X → Lift' 𝓥 X
lift' 𝓥 = inl

lower' : {𝓥 : Universe} {X : 𝓤 ̇ } → Lift' 𝓥 X → X
lower' (inl x) = x
lower' (inr x) = 𝟘-elim x

Lift'-≃ : (𝓥 : Universe) (X : 𝓤 ̇ ) → Lift' 𝓥 X ≃ X
Lift'-≃ 𝓥 X = 𝟘-rneutral'

Lift'-is-embedding : Univalence → is-embedding (Lift' {𝓤} 𝓥)
Lift'-is-embedding {𝓤} {𝓥} ua =
 universe-embeddings-are-embeddings ua 𝓤 (𝓤 ⊔ 𝓥) (Lift' 𝓥) (Lift'-≃ 𝓥)
\end{code}

The following embedding has better definitional properties:

\begin{code}

Lift : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Lift 𝓥 X = X × 𝟙 {𝓥}

lift : (𝓥 : Universe) {X : 𝓤 ̇ } → X → Lift 𝓥 X
lift 𝓥 x = (x , ⋆)

lower : {X : 𝓤 ̇ } → Lift 𝓥 X → X
lower (x , ⋆) = x

η-Lift : (𝓥 : Universe) {X : 𝓤 ̇ } (𝔁 : Lift 𝓥 X)
       → lift 𝓥 (lower 𝔁) ＝ 𝔁
η-Lift  𝓥 𝔁 = refl

ε-Lift : (𝓥 : Universe) {X : 𝓤 ̇ } (x : X)
       → lower (lift 𝓥 x) ＝ x
ε-Lift  𝓥 x = refl

lower-is-equiv : {X : 𝓤 ̇ } → is-equiv (lower {𝓤} {𝓥} {X})
lower-is-equiv {𝓤} {𝓥} = (lift 𝓥 , ε-Lift 𝓥) , (lift 𝓥 , η-Lift 𝓥)

lift-is-equiv : {X : 𝓤 ̇ } → is-equiv (lift 𝓥 {X})
lift-is-equiv {𝓤} {𝓥} = (lower , η-Lift 𝓥) , lower , ε-Lift 𝓥

Lift-≃ : (𝓥 : Universe) (X : 𝓤 ̇ ) → Lift 𝓥 X ≃ X
Lift-≃ 𝓥 X = lower , lower-is-equiv

≃-Lift : (𝓥 : Universe) (X : 𝓤 ̇ ) → X ≃ Lift 𝓥 X
≃-Lift 𝓥 X = lift 𝓥 , lift-is-equiv

Lift-is-universe-embedding : (𝓥 : Universe) → is-universe-embedding (Lift {𝓤} 𝓥)
Lift-is-universe-embedding = Lift-≃

Lift-is-embedding : Univalence → is-embedding (Lift {𝓤} 𝓥)
Lift-is-embedding {𝓤} {𝓥} ua = universe-embeddings-are-embeddings ua 𝓤 (𝓤 ⊔ 𝓥)
                                (Lift 𝓥) (Lift-is-universe-embedding 𝓥)
\end{code}

Added 7th Feb 2019. Assuming propositional and functional
extensionality instead of univalence, then lift-fibers of propositions
are propositions. (For use in the module UF.Size.)

\begin{code}

prop-fiber-criterion : PropExt
                     → FunExt
                     → (𝓤 𝓥 : Universe)
                     → (f : 𝓤 ̇ → 𝓥 ̇ )
                     → is-universe-embedding f
                     → (Q : 𝓥 ̇ )
                     → is-prop Q
                     → is-prop (fiber f Q)
prop-fiber-criterion pe fe 𝓤 𝓥 f i Q j (P , r) = d (P , r)
 where
  _ : f P ＝ Q
  _ = r

  k : is-prop (f P)
  k = transport⁻¹ is-prop r j

  l : is-prop P
  l = equiv-to-prop (≃-sym (i P)) k

  a : (X : 𝓤 ̇ ) → (f X ＝ f P) ≃ (X ＝ P)
  a X = (f X ＝ f P)  ≃⟨ prop-univalent-≃ (pe 𝓥) (fe 𝓥 𝓥) (f X) (f P) k ⟩
        (f X ≃ f P)  ≃⟨ ≃-cong fe (i X) (i P) ⟩
        (X ≃ P)      ≃⟨ ≃-sym (prop-univalent-≃ (pe 𝓤) (fe 𝓤 𝓤) X P l) ⟩
        (X ＝ P)      ■

  b : (Σ X ꞉ 𝓤 ̇ , f X ＝ f P) ≃ (Σ X ꞉ 𝓤 ̇ , X ＝ P)
  b = Σ-cong a

  c : is-prop (Σ X ꞉ 𝓤 ̇ , f X ＝ f P)
  c = equiv-to-prop b (singleton-types'-are-props P)

  d : is-prop (Σ X ꞉ 𝓤 ̇ , f X ＝ Q)
  d = transport (λ - → is-prop (Σ X ꞉ 𝓤 ̇ , f X ＝ -)) r c

prop-fiber-Lift : PropExt
                → FunExt
                → (Q : 𝓤 ⊔ 𝓥 ̇ )
                → is-prop Q
                → is-prop (fiber (Lift 𝓥) Q)
prop-fiber-Lift {𝓤} {𝓥} pe fe = prop-fiber-criterion pe fe 𝓤 (𝓤 ⊔ 𝓥)
                                  (Lift {𝓤} 𝓥)
                                  (Lift-is-universe-embedding 𝓥)
\end{code}

Taken from the MGS'2019 lecture notes (22 December 2020):

\begin{code}

global-≃-ap' : Univalence
             → (F : Universe → Universe)
               (A : {𝓤 : Universe} → 𝓤 ̇ → (F 𝓤) ̇ )
             → ({𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X))
             → (X : 𝓤 ̇ )
               (Y : 𝓥 ̇ )
             → X ≃ Y
             → A X ≃ A Y
global-≃-ap' {𝓤} {𝓥} ua F A φ X Y e =

  A X          ≃⟨ φ X ⟩
  A (Lift 𝓥 X) ≃⟨ idtoeq (A (Lift 𝓥 X)) (A (Lift 𝓤 Y)) q ⟩
  A (Lift 𝓤 Y) ≃⟨ ≃-sym (φ Y) ⟩
  A Y          ■
 where
  d : Lift 𝓥 X ≃ Lift 𝓤 Y
  d = Lift 𝓥 X ≃⟨ Lift-is-universe-embedding 𝓥 X ⟩
      X        ≃⟨ e ⟩
      Y        ≃⟨ ≃-sym (Lift-is-universe-embedding 𝓤 Y) ⟩
      Lift 𝓤 Y ■

  p : Lift 𝓥 X ＝ Lift 𝓤 Y
  p = eqtoid (ua (𝓤 ⊔ 𝓥)) (Lift 𝓥 X) (Lift 𝓤 Y) d

  q : A (Lift 𝓥 X) ＝ A (Lift 𝓤 Y)
  q = ap A p

global-property-of-types : 𝓤ω
global-property-of-types = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇

global-property-of-types⁺ : 𝓤ω
global-property-of-types⁺ = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⁺ ̇

cumulative : global-property-of-types → 𝓤ω
cumulative A = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X)

cumulative⁺ : global-property-of-types⁺ → 𝓤ω
cumulative⁺ A = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X)

global-≃-ap : Univalence
            → (A : global-property-of-types)
            → cumulative A
            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y
global-≃-ap ua = global-≃-ap' ua (λ 𝓤 → 𝓤)

global-≃-ap⁺ : Univalence
            → (A : global-property-of-types⁺)
            → cumulative⁺ A
            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y
global-≃-ap⁺ ua = global-≃-ap' ua (_⁺)

\end{code}

Cumulativity in the above sense doesn't always hold. See the module
LawvereFPT for a counter-example.

Added 24th December 2020. Lifting of hSets.

\begin{code}

Lift-is-set : ∀ {𝓤} 𝓥 (X : 𝓤 ̇ ) → is-set X → is-set (Lift 𝓥 X)
Lift-is-set 𝓥 X X-is-set = equiv-to-set
                            (Lift-is-universe-embedding 𝓥 X)
                            X-is-set

Lift-hSet : (𝓥 : Universe) → hSet 𝓤 → hSet (𝓤 ⊔ 𝓥)
Lift-hSet 𝓥 = pair-fun (Lift 𝓥) (Lift-is-set 𝓥)

Lift-is-set-is-embedding : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                         → (X : 𝓤 ̇ )
                         → is-embedding (Lift-is-set 𝓥 X)
Lift-is-set-is-embedding {𝓤} {𝓥} fe X =
 maps-of-props-are-embeddings
 (Lift-is-set 𝓥 X)
 (being-set-is-prop (lower-funext 𝓥 𝓥 fe))
 (being-set-is-prop fe)

Lift-hSet-is-embedding : Univalence → is-embedding (Lift-hSet {𝓤} 𝓥)
Lift-hSet-is-embedding {𝓤} {𝓥} ua =
 pair-fun-is-embedding
 (Lift 𝓥)
 (Lift-is-set 𝓥)
 (Lift-is-embedding ua)
 (Lift-is-set-is-embedding
   (Univalence-gives-FunExt ua (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)))

is-hSet-embedding : (hSet 𝓤 → hSet 𝓥) → (𝓤 ⁺) ⊔ 𝓥 ̇
is-hSet-embedding {𝓤} {𝓥} f = (𝓧 : hSet 𝓤) → underlying-set (f 𝓧)
                                             ≃ underlying-set 𝓧

at-most-one-hSet-embedding : Univalence
                           → (f g : hSet 𝓤 → hSet 𝓥)
                           → is-hSet-embedding f
                           → is-hSet-embedding g
                           → f ＝ g
at-most-one-hSet-embedding {𝓤} {𝓥} ua f g i j = p
 where
  h : ∀ 𝓧 → underlying-set (f 𝓧) ≃ underlying-set (g 𝓧)
  h 𝓧 = i 𝓧 ● ≃-sym (j 𝓧)

  H : f ∼ g
  H 𝓧 = to-subtype-＝
          (λ 𝓨 → being-set-is-prop (univalence-gives-funext (ua 𝓥)))
          (eqtoid (ua 𝓥) (underlying-set (f 𝓧)) (underlying-set (g 𝓧)) (h 𝓧))

  p : f ＝ g
  p = dfunext (Univalence-gives-FunExt ua (𝓤 ⁺) (𝓥 ⁺)) H

the-only-hSet-embedding-is-Lift-hSet : Univalence
                                     → (f : hSet 𝓤 → hSet (𝓤 ⊔ 𝓥))
                                     → is-hSet-embedding f
                                     → f ＝ Lift-hSet 𝓥
the-only-hSet-embedding-is-Lift-hSet {𝓤} {𝓥} ua f i =
 at-most-one-hSet-embedding ua f
  (Lift-hSet 𝓥) i
  (λ 𝓧 → Lift-is-universe-embedding 𝓥 (underlying-set 𝓧))

hSet-embeddings-are-embeddings : Univalence
                               → (f : hSet 𝓤 → hSet (𝓤 ⊔ 𝓥))
                               → is-hSet-embedding f
                               → is-embedding f
hSet-embeddings-are-embeddings {𝓤} {𝓥} ua f i =
 transport is-embedding
  ((the-only-hSet-embedding-is-Lift-hSet ua f i)⁻¹)
  (Lift-hSet-is-embedding {𝓤} {𝓥} ua)

\end{code}
