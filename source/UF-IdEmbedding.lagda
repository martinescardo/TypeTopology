Martin Escardo, 2015, formalized December 2017.

Id : X → (X → U) is an embedding assuming functional extensionality,
and either univalence or K, in fact the Yoneda Embedding.

The Id-fiber of A:X→𝓤 ̇ says that A is representable, which is
equivalent to the contractibility of ΣA, which is a
proposition. (Hence the injective types are the retracts of the
exponential powers of the universe.)

This works as follows in outline:

If A : X → 𝓤 ̇ then the Id-fiber of A is Σ x ꞉ X , Id x ≡ A.

If the pair (x,p) is in the fiber for x : X and p : Id x = A, then

   ap Σ p : Σ (Id x) = Σ A,

and hence, being equal to a contractible type, the type Σ A is
contractible.

Next we have (*)

 A x ≃ Nat (Id x) A             (yoneda)
     = (y : X) → Id x y → A y   (definition)
     ≃ (y : X) → Id x y ≃ A y   (because Σ A is contractible (Yoneda corollary))
     ≃ (y : X) → Id x y ≡ A y   (by univalence)
     ≃ Id x ≡ A                 (by function extensionality)

Applying Σ to both sides, Σ A ≃ (Σ x ꞉ X , Id x ≡ A), and because
the type Σ A is contractible so is Σ x ꞉ X , Id x ≡ A, which shows
that the map Id : X → (X → U) is an embedding.

2017:

This relies on univalence. But less than that suffices
(https://groups.google.com/forum/#!topic/homotopytypetheory/bKti7krHM-c)

First, Evan Cavallo showed that it is enough to assume funext and that
the canonical map X ≡ Y → X ≃ Y is an embedding. Then, using this idea
and the above proof outline, we further generalized this to assume
that the canonical map X ≡ Y → (X → Y) is left-cancellable (which is
much weaker than assuming that it is an embedding).

This is what we record next (9th December 2017), using the original
idea (*) in the weakened form discussed above.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF-IdEmbedding where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Embeddings
open import UF-Yoneda
open import UF-LeftCancellable
open import UF-Univalence
open import UF-EquivalenceExamples

\end{code}

The Id Embedding Lemma. The idea is to show that the type
T := Σ x ꞉ X , Id x ≡ A is a proposition by showing that there is a
left-cancellable map from it to a proposition, namely the contractible
type Σ A.

\begin{code}

Id-Embedding-Lemma : FunExt
                   → {X : 𝓤 ̇ }
                   → ((x y : X) (A : X → 𝓤 ̇ )
                   → left-cancellable (idtofun (Id x y) (A y)))
                   → is-embedding(Id {𝓤} {X})
Id-Embedding-Lemma {𝓤} fe {X} iflc A (x₀ , p₀) = h (x₀ , p₀)
 where
  T = Σ x ꞉ X , Id x ≡ A
  q : Σ (Id x₀) ≡ Σ A
  q = ap Σ p₀
  c : ∃! A
  c = yoneda-nat (singleton-type x₀) is-singleton (singleton-types-are-singletons x₀) (Σ A) q
  f₀ : (x : X) → Id x ≡ A → (y : X) → Id x y ≡ A y
  f₀ x = happly
  f₁ : (x : X) → ((y : X) → Id x y ≡ A y) → Nat (Id x) A
  f₁ x = NatΠ (λ y → idtofun (Id x y) (A y))
  f₂ : (x : X) → Nat (Id x) A → A x
  f₂ x = yoneda-elem x A
  f : (x : X) → Id x ≡ A → A x
  f x = f₂ x ∘ f₁ x ∘ f₀ x
  f₀-lc : (x : X) → left-cancellable(f₀ x)
  f₀-lc x = happly-lc (fe 𝓤 (𝓤 ⁺)) (Id x) A
  f₁-lc : (x : X) → left-cancellable(f₁ x)
  f₁-lc x = g
    where
      l : ∀ {φ φ'} → f₁ x φ ≡ f₁ x φ' → (x : X) → φ x ≡ φ' x
      l {φ} {φ'} = NatΠ-lc (λ y → idtofun (Id x y) (A y)) (λ y → iflc x y A)
      g : ∀ {φ φ'} → f₁ x φ ≡ f₁ x φ' → φ ≡ φ'
      g p = dfunext (fe 𝓤 (𝓤 ⁺)) (l p)
  f₂-lc : (x : X) → left-cancellable(f₂ x)
  f₂-lc x {η} {η'} p = dfunext (fe 𝓤 𝓤) (λ y → dfunext (fe 𝓤 𝓤) (l y))
    where
      l : η ≈ η'
      l = yoneda-elem-lc η η' p
  f-lc : (x : X) → left-cancellable(f x)
  f-lc x = left-cancellable-closed-under-∘
               (f₀ x)
               (f₂ x ∘ f₁ x)
               (f₀-lc x)
               (left-cancellable-closed-under-∘ (f₁ x) (f₂ x) (f₁-lc x) (f₂-lc x))
  g : T → Σ A
  g = NatΣ f
  g-lc : left-cancellable g
  g-lc = NatΣ-lc f f-lc
  h : is-prop T
  h = left-cancellable-reflects-is-prop g g-lc (singletons-are-props c)

\end{code}

univalence implies that the function Id {𝓤} {X} : X → (X → 𝓤 ̇ ) is an embedding.

The map eqtofun is left-cancellable assuming univalence (and function
extensionality, which is a consequence of univalence, but we don't
bother):

\begin{code}

eqtofun-lc : is-univalent 𝓤
           → FunExt
           → (X Y : 𝓤 ̇ ) → left-cancellable(Eqtofun X Y)
eqtofun-lc ua fe X Y {f , jef} {g , jeg} p = γ
 where
  q : yoneda-nat f is-equiv jef g p ≡ jeg
  q = being-equiv-is-prop fe g _ _
  γ : f , jef ≡ g , jeg
  γ = to-Σ-Id (p , q)

\end{code}

The map idtofun is left-cancellable assuming univalence (and funext):

\begin{code}

is-univalent-idtofun-lc : is-univalent 𝓤
                        → FunExt
                        → (X Y : 𝓤 ̇ ) → left-cancellable(idtofun X Y)
is-univalent-idtofun-lc  ua fe X Y = left-cancellable-closed-under-∘
                                        (idtoeq X Y)
                                        (Eqtofun X Y)
                                        (is-univalent-idtoeq-lc ua X Y) (eqtofun-lc ua fe X Y)

UA-Id-embedding : is-univalent 𝓤
                → FunExt
                → {X : 𝓤 ̇ } → is-embedding(Id {𝓤} {X})
UA-Id-embedding {𝓤} ua fe {X} = Id-Embedding-Lemma fe
                                            (λ x y a → is-univalent-idtofun-lc ua fe (Id x y) (a y))

\end{code}

The K axiom and function extensionality together imply that the
function Id : X → (X → U) is an embedding.

\begin{code}

K-Id-embedding' : K-axiom (𝓤 ⁺)
                → FunExt
                → {X : 𝓤 ̇ } → is-embedding(Id {𝓤} {X})
K-Id-embedding' {𝓤} k fe {X} = Id-Embedding-Lemma fe (K-idtofun-lc k)

\end{code}

But actually function extensionality is not needed for this: K alone suffices.

\begin{code}

Id-lc : {X : 𝓤 ̇ } → left-cancellable (Id {𝓤} {X})
Id-lc {𝓤} {X} {x} {y} p = idtofun (Id y y) (Id x y) (happly (p ⁻¹) y) refl

K-Id-embedding : K-axiom (𝓤 ⁺) → {X : 𝓤 ̇ } → is-embedding(Id {𝓤} {X})
K-Id-embedding {𝓤} k {X} = lc-maps-are-embeddings-with-K Id Id-lc k

\end{code}

Added 7th Feb 2019.

\begin{code}

Id-set : {X : 𝓤 ̇ } → is-set X → X → (X → Ω 𝓤)
Id-set i x y = (x ≡ y) , i

Id-set-lc : funext  𝓤 (𝓤 ⁺)
          → {X : 𝓤 ̇ } (i : is-set X)
          → left-cancellable (Id-set i)
Id-set-lc fe {X} i {x} {y} e = Id-lc d
 where
  d : Id x ≡ Id y
  d = dfunext fe (λ z → ap pr₁ (happly e z))

Id-set-is-embedding : funext  𝓤 (𝓤 ⁺)
                    → propext 𝓤
                    → {X : 𝓤 ̇ } (i : is-set X) → is-embedding (Id-set i)
Id-set-is-embedding {𝓤} fe pe {X} i = lc-maps-into-sets-are-embeddings
                                        (Id-set i)
                                        (Id-set-lc (lower-funext 𝓤 (𝓤 ⁺) fe) i)
                                        (Π-is-set fe (λ x → Ω-is-set (lower-funext 𝓤 (𝓤 ⁺) fe) pe))
\end{code}
