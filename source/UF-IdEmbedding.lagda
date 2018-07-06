Martin Escardo, 2015, formalized December 2017.

Id : X → (X → U) is an embedding assuming functional extensionality,
and either univalence or K, in fact the Yoneda Embedding.

The Id-fiber of A:X→U ̇ says that A is representable, which is
equivalent to the contractibility of ΣA, which is a
proposition. (Hence the injective types are the retracts of the
exponential powers of the universe.)

This works as follows in outline:

If A : X → U ̇ then the Id-fiber of A is Σ \(x : X) → Id x ≡ A.

If the pair (x : X , p : Id x = A) is in the fiber, then

   ap Σ p : Σ (Id x) = Σ A,

and hence, being equal to a contractible type, Σ A is
contractible.

Next we have (*)

 A x ≃ Nat (Id x) A             (yoneda)
     = (y : X) → Id x y → A y   (definition)
     ≃ (y : X) → Id x y ≃ A y   (because Σ A is contractible (Yoneda corollary))
     ≃ (y : X) → Id x y ≡ A y   (by univalence)
     ≃ Id x ≡ A                 (by function extensionality)

Applying Σ to both sides, Σ A ≃ (Σ \(x : X), Id x ≡ A), and because Σ
A is contractible so is Σ \(x : X), Id x ≡ A, which shows that the map
Id : X → (X → U) is an embedding.

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

module UF-IdEmbedding where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Embedding
open import UF-Yoneda
open import UF-LeftCancellable
open import UF-Univalence

\end{code}

The Id Embedding Lemma. The idea is to show that the type 
T := Σ \(x : X) → Id x ≡ A is a proposition by showing that there is a
left-cancellable map from it to a proposition, namely the contractible
type Σ A.

\begin{code}

Id-Embedding-Lemma : (∀ U V → funext U V) → ∀ {U} → {X : U ̇}
                  → ((x y : X) (A : X → U ̇)
                  → left-cancellable (idtofun (Id x y) (A y))) 
                  → is-embedding(Id {U} {X})
Id-Embedding-Lemma fe {U} {X} iflc A (x₀ , p₀) = h (x₀ , p₀)
 where
  T = Σ \(x : X) → Id x ≡ A
  q : Σ (Id x₀) ≡ Σ A
  q = ap Σ p₀
  c : is-singleton(Σ A)
  c = yoneda-nat (identifications-from x₀) is-singleton (identifications-from-singleton x₀) (Σ A) q
  f₀ : (x : X) → Id x ≡ A → (y : X) → Id x y ≡ A y
  f₀ x = happly
  f₁ : (x : X) → ((y : X) → Id x y ≡ A y) → Nat (Id x) A
  f₁ x = NatΠ (λ y → idtofun (Id x y) (A y))
  f₂ : (x : X) → Nat (Id x) A → A x
  f₂ x = yoneda-elem x A
  f : (x : X) → Id x ≡ A → A x
  f x = f₂ x ∘ f₁ x ∘ f₀ x
  f₀-lc : (x : X) → left-cancellable(f₀ x)
  f₀-lc x = happly-lc (fe U (U ′)) (Id x) A
  f₁-lc : (x : X) → left-cancellable(f₁ x)
  f₁-lc x = g
    where
      l : ∀ {φ φ'} → f₁ x φ ≡ f₁ x φ' → (x : X) → φ x ≡ φ' x
      l {φ} {φ'} = NatΠ-lc (λ y → idtofun (Id x y) (A y)) (λ y → iflc x y A)
      g : ∀ {φ φ'} → f₁ x φ ≡ f₁ x φ' → φ ≡ φ'
      g p = dfunext (fe U (U ′)) (l p) 
  f₂-lc : (x : X) → left-cancellable(f₂ x)
  f₂-lc x {η} {η'} p = dfunext (fe U U) (λ y → dfunext (fe U U) (l y))
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
  g-lc = NatΣ-lc X (λ x → Id x ≡ A) A f f-lc 
  h : is-prop T
  h = left-cancellable-reflects-is-prop g g-lc (is-singleton-is-prop c)

\end{code}

univalence implies that the function Id {U} {X} : X → (X → U ̇) is an embedding.
  
The map eqtofun is left-cancellable assuming univalence (and function
extensionality, which is a consequence of univalence, but we don't
bother):

\begin{code}

eqtofun-lc : ∀ {U} → is-univalent U → (∀ U V → funext U V)
           → (X Y : U ̇) → left-cancellable(eqtofun X Y)
eqtofun-lc ua fe X Y {f , jef} {g , jeg} p = go
 where
  q : yoneda-nat f is-equiv jef g p ≡ jeg
  q = is-prop-is-equiv fe g _ _
  go : f , jef ≡ g , jeg
  go = to-Σ-Id (p , q)
  
\end{code}

The map idtofun is left-cancellable assuming univalence (and funext):

\begin{code}

is-univalent-idtofun-lc : ∀ {U} → is-univalent U → (∀ U V → funext U V) → (X Y : U ̇) 
                       → left-cancellable(idtofun X Y)
is-univalent-idtofun-lc  ua fe X Y = left-cancellable-closed-under-∘
                                        (idtoeq X Y)
                                        (eqtofun X Y)
                                        (is-univalent-idtoeq-lc ua X Y) (eqtofun-lc ua fe X Y)

UA-Id-embedding-Theorem : ∀ {U} → is-univalent U → (∀ U V → funext U V)
                       → {X : U ̇} → is-embedding(Id {U} {X})
UA-Id-embedding-Theorem {U} ua fe {X} = Id-Embedding-Lemma fe 
                                            (λ x y a → is-univalent-idtofun-lc ua fe (Id x y) (a y))

\end{code}

The K axiom and function extensionality together imply that the
function Id : X → (X → U) is an embedding.

\begin{code}

K-id-embedding-Theorem' : ∀ {U} → K (U ′) → (∀ U V → funext U V)
                       → {X : U ̇} → is-embedding(Id {U} {X})
K-id-embedding-Theorem' {U} k fe {X} = Id-Embedding-Lemma fe (K-idtofun-lc k) 

\end{code}

But actually function extensionality is not needed for this: K alone suffices.

\begin{code}

Id-lc : ∀ {U} {X : U ̇} → left-cancellable (Id {U} {X})
Id-lc {U} {X} {x} {y} p = idtofun (Id y y) (Id x y) (happly (p ⁻¹) y) refl

K-id-embedding-Theorem : ∀ {U} → K (U ′) → {X : U ̇} → is-embedding(Id {U} {X})
K-id-embedding-Theorem {U} k {X} = left-cancellable-maps-are-embeddings-with-K Id Id-lc k

\end{code}
