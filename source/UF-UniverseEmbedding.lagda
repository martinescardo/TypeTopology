Martin Escardo, 29th January 2019

If univalence holds, then any universe is embedded into any larger universe.

We do this without cumulativity, because it is not available in the
Martin-Löf type theory that we are working with in Agda.

Moreover, any map f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ with f X ≃ X for all X : 𝓤 ̇ is an
embedding, e.g. the map X ↦ X + 𝟘 {𝓥}.

(Here the notion of a map being an embedding is stronger than that of
being left-cancellable, and it means that the fibers of the map are
propositions, or subsingletons, as in HoTT/UF.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module UF-UniverseEmbedding where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Equiv-FunExt
open import UF-UA-FunExt

universe-embedding-criterion : Univalence
                             → (𝓤 𝓥 : Universe) (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
                             → ((X : 𝓤 ̇ ) → f X ≃ X)
                             → is-embedding f
universe-embedding-criterion ua 𝓤 𝓥 f i = embedding-criterion' f γ
 where
  γ : (X X' : 𝓤 ̇ ) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' =  (f X ≡ f X')  ≃⟨ univalence-≃ (ua (𝓤 ⊔ 𝓥)) (f X) (f X') ⟩
            (f X ≃ f X')  ≃⟨ Eq-Eq-cong (FunExt-from-Univalence ua) (i X) (i X') ⟩
            (X ≃ X')      ≃⟨ ≃-sym (univalence-≃ (ua 𝓤) X X') ⟩
            (X ≡ X')      ■

\end{code}

For instance, the following function satisfies this condition and
hence is an embedding:

\begin{code}

Lift' : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Lift' 𝓥 X = X + 𝟘 {𝓥}

lift' : (𝓥 : Universe) {X : 𝓤 ̇ } → X → Lift' 𝓥 X
lift' 𝓥 = inl

Lift'-≃ : (𝓥 : Universe) (X : 𝓤 ̇ ) → Lift' 𝓥 X ≃ X
Lift'-≃ 𝓥 X = 𝟘-rneutral'

Lift'-is-embedding : Univalence → is-embedding (Lift' {𝓤} 𝓥)
Lift'-is-embedding {𝓤} {𝓥} ua = universe-embedding-criterion ua 𝓤 𝓥 (Lift' 𝓥) (Lift'-≃ 𝓥)

\end{code}

The following embedding has better definitional properties:

\begin{code}

Lift : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
Lift 𝓥 X = X × 𝟙 {𝓥}

lift : (𝓥 : Universe) {X : 𝓤 ̇ } → X → Lift 𝓥 X
lift 𝓥 x = (x , *)

Lift-≃ : (𝓥 : Universe) (X : 𝓤 ̇ ) → Lift 𝓥 X ≃ X
Lift-≃ 𝓥 X = 𝟙-rneutral

Lift-is-embedding : Univalence → is-embedding (Lift {𝓤} 𝓥)
Lift-is-embedding {𝓤} {𝓥} ua = universe-embedding-criterion ua 𝓤 𝓥 (Lift 𝓥) (Lift-≃ 𝓥)

\end{code}

Added 7th Feb 2019. Assuming propositional and functional
extensionality instead of univalence, the lift fibers of propositions
are propositions. (For use in the module UF-Resize.)

\begin{code}

prop-fiber-criterion : PropExt
                     → FunExt
                     → (𝓤 𝓥 : Universe)
                     → (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ )
                     → ((X : 𝓤 ̇ ) → f X ≃ X)
                     → (Q : 𝓤 ⊔ 𝓥 ̇ ) → is-prop Q → is-prop (fiber f Q)
prop-fiber-criterion pe fe 𝓤 𝓥 f i Q j (P , r) = d (P , r)
 where
  k : is-prop (f P)
  k = back-transport is-prop r j

  l : is-prop P
  l = equiv-to-prop (≃-sym (i P)) k

  a : (X : 𝓤 ̇ ) → (f X ≡ f P) ≃ (X ≡ P)
  a X = (f X ≡ f P)  ≃⟨ prop-univalent-≃ (pe (𝓤 ⊔ 𝓥)) (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (f X) (f P) k ⟩
        (f X ≃ f P)  ≃⟨ Eq-Eq-cong fe (i X) (i P) ⟩
        (X ≃ P)      ≃⟨ ≃-sym (prop-univalent-≃ (pe 𝓤) (fe 𝓤 𝓤) X P l) ⟩
        (X ≡ P)      ■

  b : (Σ X ꞉ 𝓤 ̇ , f X ≡ f P) ≃ (Σ X ꞉ 𝓤 ̇  , X ≡ P)
  b = Σ-cong a

  c : is-prop (Σ X ꞉ 𝓤 ̇ , f X ≡ f P)
  c = equiv-to-prop b (singleton-types'-are-props P)

  d : is-prop (Σ X ꞉ 𝓤 ̇ , f X ≡ Q)
  d = transport (λ - → is-prop (Σ X ꞉ 𝓤 ̇ , f X ≡ -)) r c

prop-fiber-Lift : PropExt → FunExt → (Q : 𝓤 ⊔ 𝓥 ̇ ) → is-prop Q → is-prop (fiber (Lift 𝓥) Q)
prop-fiber-Lift {𝓤} {𝓥} pe fe = prop-fiber-criterion pe fe 𝓤 𝓥 (Lift {𝓤} 𝓥) (Lift-≃ 𝓥)

\end{code}

Taken from the MGS'2019 lecture notes (22 December 2020):

\begin{code}

global-property-of-types : 𝓤ω
global-property-of-types = {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇

cumulative : global-property-of-types → 𝓤ω
cumulative A = {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X)

global-≃-ap : Univalence
            → (A : global-property-of-types)
            → cumulative A
            → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y

global-≃-ap' : Univalence
             → (F : Universe → Universe)
             → (A : {𝓤 : Universe} → 𝓤 ̇ → (F 𝓤) ̇ )
             → ({𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) → A X ≃ A (Lift 𝓥 X))
             → (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → A X ≃ A Y

global-≃-ap' {𝓤} {𝓥} ua F A φ X Y e =

  A X          ≃⟨ φ X ⟩
  A (Lift 𝓥 X) ≃⟨ idtoeq (A (Lift 𝓥 X)) (A (Lift 𝓤 Y)) q ⟩
  A (Lift 𝓤 Y) ≃⟨ ≃-sym (φ Y) ⟩
  A Y          ■
 where
  d : Lift 𝓥 X ≃ Lift 𝓤 Y
  d = Lift 𝓥 X ≃⟨ Lift-≃ 𝓥 X ⟩
      X        ≃⟨ e ⟩
      Y        ≃⟨ ≃-sym (Lift-≃ 𝓤 Y) ⟩
      Lift 𝓤 Y ■

  p : Lift 𝓥 X ≡ Lift 𝓤 Y
  p = eqtoid (ua (𝓤 ⊔ 𝓥)) (Lift 𝓥 X) (Lift 𝓤 Y) d

  q : A (Lift 𝓥 X) ≡ A (Lift 𝓤 Y)
  q = ap A p

global-≃-ap ua = global-≃-ap' ua id


\end{code}
