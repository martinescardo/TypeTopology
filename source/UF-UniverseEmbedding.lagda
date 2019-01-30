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

The above module assumption "ua" is global univalence (univalence for
all universes), which gives global function extensionality
(extensionality for functions of types of any two universes). We
initially tried to use localized univalence and function
extensionality, and we succeeded, but then, for example, one lemma got
five function extensionality assumptions for various combinations of
universes, which is distracting and cumbersome.

\begin{code}

private
 fe : FunExt
 fe = FunExt-from-univalence ua

 nfe : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {f g : Π A} → f ∼ g → f ≡ g
 nfe {𝓤} {𝓥} = dfunext (fe 𝓤 𝓥)

\end{code}

We begin with some general results about equivalences, which probably
should be moved to other univalent foundations modules in the future
as they are potentially of wider use, independently of the particular
application developed here.

\begin{code}

inverse-involutive : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) (e : is-equiv f)
                   → inverse (inverse f e) (inverse-is-equiv f e) ≡ f
inverse-involutive f e = refl

\end{code}

That the above proof is refl is an accident of our choice of notion of
equivalence as primary.

\begin{code}

≃-assoc : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {T : 𝓣 ̇}
          (α : X ≃ Y) (β : Y ≃ Z) (γ : Z ≃ T)
        → α ● (β ● γ) ≡ (α ● β) ● γ
≃-assoc (f , a) (g , b) (h , c) = to-Σ-≡ (p , q)
 where
  p : (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
  p = refl

  d e : is-equiv (h ∘ g ∘ f)
  d = ∘-is-equiv a (∘-is-equiv b c)
  e = ∘-is-equiv (∘-is-equiv a b) c

  q : transport is-equiv p d ≡ e
  q = being-equiv-is-a-prop fe (h ∘ g ∘ f) _ _

\end{code}

The above proof can be condensed to one line in the style of the
following two proofs, which exploit the fact that the identity map is
a neutral element for ordinary function composition, definitionally:

\begin{code}

≃-refl-left : {X : 𝓤 ̇} {Y : 𝓥 ̇} (α : X ≃ Y) → ≃-refl X ● α ≡ α
≃-refl-left α = to-Σ-≡ (refl , being-equiv-is-a-prop fe _ _ _)

≃-refl-right : {X : 𝓤 ̇} {Y : 𝓥 ̇} (α : X ≃ Y) → α ● ≃-refl Y ≡ α
≃-refl-right α = to-Σ-≡ (refl , being-equiv-is-a-prop fe _ _ _)

≃-sym-involutive : {X : 𝓤 ̇} {Y : 𝓥 ̇} (α : X ≃ Y) → ≃-sym (≃-sym α) ≡ α
≃-sym-involutive (f , a) = to-Σ-≡ (p , being-equiv-is-a-prop fe f _ a)
 where
  p : inverse (inverse f a) (inverse-is-equiv f a) ≡ f
  p = inverse-involutive f a

≃-Sym : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X ≃ Y) ≃ (Y ≃ X)
≃-Sym = qinveq ≃-sym (≃-sym , ≃-sym-involutive , ≃-sym-involutive)

≃-sym-left-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (α : X ≃ Y) → ≃-sym α ● α ≡ ≃-refl Y
≃-sym-left-inverse (f , e) = to-Σ-≡ (p , being-equiv-is-a-prop fe _ _ _)
 where
  p : f ∘ inverse f e ≡ id
  p = nfe (inverse-is-section f e)

≃-sym-right-inverse : {X : 𝓤 ̇} {Y : 𝓥 ̇} (α : X ≃ Y) → α ● ≃-sym α ≡ ≃-refl X
≃-sym-right-inverse (f , e) = to-Σ-≡ (p , being-equiv-is-a-prop fe _ _ _)
 where
  p : inverse f e ∘ f ≡ id
  p = nfe (inverse-is-retraction f e)

≃-Comp : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ≃ Y → (Y ≃ Z) ≃ (X ≃ Z)
≃-Comp α = qinveq (α ●_) ((≃-sym α ●_), p , q)
 where
  p = λ β → ≃-sym α ● (α ● β) ≡⟨ ≃-assoc (≃-sym α) α β ⟩
            (≃-sym α ● α) ● β ≡⟨ ap (_● β) (≃-sym-left-inverse α) ⟩
            ≃-refl _ ● β      ≡⟨ ≃-refl-left _ ⟩
            β                 ∎

  q = λ γ → α ● (≃-sym α ● γ) ≡⟨ ≃-assoc α (≃-sym α) γ ⟩
            (α ● ≃-sym α) ● γ ≡⟨ ap (_● γ) (≃-sym-right-inverse α) ⟩
            ≃-refl _ ● γ      ≡⟨ ≃-refl-left _ ⟩
            γ ∎

\end{code}

One could be tempted to attempt prove the following by instead
assuming, with the aid of univalence, X ≡ A and Y ≡ B and then using
identity-type induction. However, in the absence of cumulativity, the
expressions "X ≡ A" and "Y ≡ B" don't make sense as they are not
well-typed. A similar remark applies to the above development.

\begin{code}

Id-Eq-congruence : (X Y : 𝓤 ̇) (A B : 𝓥 ̇)
                    → X ≃ A → Y ≃ B → (X ≡ Y) ≃ (A ≡ B)
Id-Eq-congruence {𝓤} {𝓥} X Y A B α β =
 (X ≡ Y) ≃⟨ is-univalent-≃ (ua 𝓤) X Y ⟩
 (X ≃ Y) ≃⟨ ≃-Comp (≃-sym α) ⟩
 (A ≃ Y) ≃⟨ ≃-Sym ⟩
 (Y ≃ A) ≃⟨ ≃-Comp (≃-sym β) ⟩
 (B ≃ A) ≃⟨ ≃-Sym ⟩
 (A ≃ B) ≃⟨ ≃-sym (is-univalent-≃ (ua 𝓥) A B) ⟩
 (A ≡ B)  ■

\end{code}

The terminology for the above construction is perhaps clearer with the
following reformulation of its statement:

\begin{code}

Id-Eq-congruence' : (X Y : 𝓤 ̇) (A B : 𝓥 ̇)
                     → Eq X A → Eq Y B → Eq (Id X Y) (Id A B)
Id-Eq-congruence' = Id-Eq-congruence

\end{code}

With this, we can prove the promised result:

\begin{code}

universe-embedding-criterion : (𝓤 𝓥 : Universe) (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇)
                             → ((X : 𝓤 ̇) → f X ≃ X)
                             → is-embedding f
universe-embedding-criterion 𝓤 𝓥 f i = embedding-criterion' f γ
 where
  γ : (X X' : 𝓤 ̇) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' = Id-Eq-congruence (f X) (f X') X X' (i X) (i X')

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
