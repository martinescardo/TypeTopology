Martin Escardo, 29th January 2019

If univalence holds, then any universe is embedded into any larger universe.

We do this without cumulativity, because it is not available in the
Martin-Löf type theory that we are working with in Agda.

Moreover, any map f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ with f X ≃ X for all X : 𝓤 ̇ is an
embedding, for example X ↦ X + 𝟘 {𝓥}.

(Here the notion of a map being an embedding is stronger than that of
left-cancellability, namely that the fibers of the map are
propositions or subsingletons, as in HoTT/UF.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module UF-UniverseEmbedding (ua : Univalence) where

open import SpartanMLTT
open import UF-Base
open import UF-Embedding
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Equiv-FunExt
open import UF-UA-FunExt

\end{code}

The above is global univalence (univalence for all universes), which
gives global function extensionality (extensionality for functions of
types of any two universes). We tried to use localized univalence and
function extensionality, and we succeeded, but then, for example, one
lemma got five function extensionality assumptions for various
combinations of universes, which is distracting and cumbersome.

\begin{code}

private
 fe : FunExt
 fe = FunExt-from-univalence ua

 nfe : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ∼ g → f ≡ g
 nfe {𝓤} {𝓥} = dfunext (fe 𝓤 𝓥)

\end{code}

We begin with some general results about equivalences which probably
should be moved to other univalent foundations modules in the future
as they are potentially of general use, independently of the
particular application developed here.

\begin{code}

inverse-involutive : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (e : is-equiv f)
                   → inverse (inverse f e) (inverse-is-equiv f e) ≡ f
inverse-involutive f e = refl

\end{code}

That the above proof is refl is an accident of our choice of notion of
equivalence as primary.

\begin{code}

≃-sym-involutive : {X : 𝓤 ̇} {Y : 𝓥 ̇} (ε : X ≃ Y)
                 → ≃-sym (≃-sym ε) ≡ ε
≃-sym-involutive {𝓤} {𝓥} {X} {Y} (f , e) = to-Σ-≡ (p , being-equiv-is-a-prop fe f _ e)
 where
  p : inverse (inverse f e) (inverse-is-equiv f e) ≡ f
  p = inverse-involutive f e

≃-Sym : {X : 𝓤 ̇} {Y : 𝓥 ̇}
      → (X ≃ Y) ≃ (Y ≃ X)
≃-Sym {𝓤} {𝓥} {X} {Y} = qinveq ≃-sym (≃-sym , ≃-sym-involutive , ≃-sym-involutive)

≃-sym-is-left-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                      → (κ : X ≃ Y) (δ : Y ≃ Z)
                      → ≃-trans (≃-sym κ) (≃-trans κ δ) ≡ δ
≃-sym-is-left-inverse (f , e) (g , d) = to-Σ-≡ (p , being-equiv-is-a-prop fe g _ d)
   where
    p : g ∘ f ∘ inverse f e ≡ g
    p = ap (g ∘_) (nfe (inverse-is-section f e))

≃-sym-is-right-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
                       → (κ : X ≃ Y) (ε : X ≃ Z)
                       → ≃-trans κ (≃-trans (≃-sym κ) ε) ≡ ε
≃-sym-is-right-inverse (f , e) (h , c) = to-Σ-≡ (p , being-equiv-is-a-prop fe h _ c)
   where
    p : h ∘ inverse f e ∘ f ≡ h
    p = ap (h ∘_) (nfe (inverse-is-retraction f e))

≃-Trans : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇}
        → X ≃ Y → (Y ≃ Z) ≃ (X ≃ Z)
≃-Trans κ = qinveq (≃-trans κ) (≃-trans (≃-sym κ) , ≃-sym-is-left-inverse κ , ≃-sym-is-right-inverse κ)

Id-is-Eq-congruence : (X Y : 𝓤 ̇) (A B : 𝓥 ̇)
                    → X ≃ A → Y ≃ B → (X ≡ Y) ≃ (A ≡ B)
Id-is-Eq-congruence {𝓤} {𝓥} X Y A B d e =
 (X ≡ Y) ≃⟨ is-univalent-≃ (ua 𝓤) X Y ⟩
 (X ≃ Y) ≃⟨ ≃-Trans (≃-sym d) ⟩
 (A ≃ Y) ≃⟨ ≃-Sym ⟩
 (Y ≃ A) ≃⟨ ≃-Trans (≃-sym e) ⟩
 (B ≃ A) ≃⟨ ≃-Sym ⟩
 (A ≃ B) ≃⟨ ≃-sym (is-univalent-≃ (ua 𝓥) A B) ⟩
 (A ≡ B)  ■

Id-is-Eq-congruence' : (X Y : 𝓤 ̇) (A B : 𝓥 ̇)
                     → Eq X A → Eq Y B → Eq (Id X Y) (Id A B)
Id-is-Eq-congruence' = Id-is-Eq-congruence

\end{code}

With this, we can prove the promised result:

\begin{code}

universe-embedding-criterion : (𝓤 𝓥 : Universe) (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇)
                             → ((X : 𝓤 ̇) → f X ≃ X)
                             → is-embedding f
universe-embedding-criterion 𝓤 𝓥 f i = embedding-criterion' f γ
 where
  γ : (X X' : 𝓤 ̇) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' = Id-is-Eq-congruence (f X) (f X') X X' (i X) (i X')

\end{code}

For instance, the function X ↦ X + 𝟘 is an embedding of the universe 𝓤
into the universe 𝓤 ⊔ 𝓥, where 𝟘 is taken to live in the universe 𝓥:

\begin{code}

module example where

 universe-up : (𝓤 𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 universe-up 𝓤 𝓥 X = X + 𝟘 {𝓥}

 universe-up-is-embedding : is-embedding (universe-up 𝓤 𝓥)
 universe-up-is-embedding {𝓤} {𝓥} = universe-embedding-criterion 𝓤 𝓥
                                      (universe-up 𝓤 𝓥)
                                      (λ X → 𝟘-rneutral' {𝓤} {𝓥} {X})

\end{code}

But, of course, there are many other naturally occurring embeddings

𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇, such as e.g. X ↦ X × 𝟙 {𝓥}, or the one provided in the
Agda standard library (called 'Lift'), defined as a record.
