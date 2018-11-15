Martin Escardo, 27 April 2014, with later additions, completed in December 2017

We show that the injective types are the retracts of the exponential
powers of universes, where an exponential power of a type D is a type
of the form A → D for some type A. Injectivity is defined as
(functional) data rather than property.


Injectivity of the universe (2014)
----------------------------

Here we have definitions and proofs in Agda notation, which assume a
univalent mathematics background (e.g. given by the HoTT book),
preceded by informal (rigorous) discussion.

We show that the universe is (right-Kan) injective wrt embeddings. An
embedding is a map j:X→Y whose fibers are all univalent propositions.

In the remote past, I looked at injectivity in categories of spaces
and locales, with respect to various kinds of maps, and I wrote
several papers about that.

At present, I am looking at searchable sets in type theory
(corresponding to compact sets in topology), and I accidentally landed
in the same injectivity territory. This file is about
injectivity. Other files make use of this for searchability purposes,
which is not discussed here.

Abstractly, the general situation is

                   j
              X ------> Y
               \       /
                \     /
             f   \   / f/j
                  \ /
                   v
                   D

Given f and j, we want to find f/j making the diagram commute (that
is, f = f/j ∘ j). Of course, this "extension property" is not always
possible, and it depends on properties of f, j and D. Usually, one
requires j to be an embedding (of some sort).

Here I consider the case that D=𝓤, a universe, in which case, if one
doesn't want to assume univalence, then it makes sense to consider
commutation up to equivalence:

                   j
              X ------> Y
               \       /
                \  ≃  /
             f   \   / f/j
                  \ /
                   v
                   𝓤

But this can be the case only if j is an embedding in a suitable
sense. Otherwise, we only have a right-Kan extension

                   j
              X ------> Y
               \       /
                \  <- /
             f   \   / f/j
                  \ /
                   v
                   𝓤

in the sense that the natural transformations from "presheaves"
g : Y → 𝓤 to the "presheaf" f/j are naturally equivalent to the
natural transformations from g ∘ j to f:

     Nat g f/j ≃ Nat (g ∘ j) f

If j is an embedding (in the sense of univalent mathematics), then,
for any f, we can find f/j which is both a right-Kan extension and a
(proper) extension (up to equivalence).

All this dualizes with Π replaced by Σ and right replaced by left.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module UF-InjectiveTypes (fe : ∀ 𝓤 𝓥 → funext 𝓤 𝓥) where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Embedding
open import UF-Retracts
open import UF-EquivalenceExamples
open import UF-Univalence

\end{code}

Here is how we define f/j given f and j.

                   j
              X ------> Y
               \       /
                \  <- /
             f   \   / f' := f/j
                  \ /
                   v
                   𝓤

We have to apply the following constructions for 𝓤=𝓥=𝓦 for the above
triangles to make sense.

\begin{code}

module _ {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓦 ̇) (j : X → Y) where

  Π-extension Σ-extension : Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  Π-extension y = Π \(w : fiber j y) → f(pr₁ w)
  Σ-extension y = Σ \(w : fiber j y) → f(pr₁ w)

  private f/j f∖j : Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  f/j = Π-extension
  f∖j = Σ-extension

  Σ→Π : is-embedding j → Nat f∖j f/j
  Σ→Π e y ((x , p) , B) (x' , p') = transport f (embedding-lc j e (p ∙ p' ⁻¹)) B

\end{code}

  The natural transformation Σ→Π j itself should be a natural
  embedding (conjectural conjecture).

\begin{code}

  ηΠ : Nat (f/j ∘ j) f
  ηΠ x C = C(x , refl)

  ηΣ : Nat f (f∖j ∘ j)
  ηΣ x B = (x , refl) , B

\end{code}

  For arbitrary j:X→Y, this gives Kan extensions in the following
  sense:

\begin{code}

  Π-extension-right-Kan : (g : Y → 𝓤 ̇) → Nat g f/j ≃ Nat (g ∘ j) f
  Π-extension-right-Kan g = e
   where
    φ : (g : Y → 𝓤 ̇) → Nat (g ∘ j) f → Nat g f/j
    φ g η y C (x , p) = η x (back-transport g p C)

    ψ : (g : Y → 𝓤 ̇) → Nat g f/j → Nat (g ∘ j) f
    ψ g θ x C = θ (j x) C (x , refl)

    ψφ : (g : Y → 𝓤 ̇) (η : Nat (g ∘ j) f) (x : X) (C : g (j x)) → ψ g (φ g η) x C ≡ η x C
    ψφ g η x C = refl

    φψ : (g : Y → 𝓤 ̇) (θ : Nat g f/j) (y : Y) (C : g y) (w : fiber j y) → φ g (ψ g θ) y C w ≡ θ y C w
    φψ g θ y C (x , refl) = refl

    e : Nat g f/j ≃ Nat (g ∘ j) f
    e = ψ g , (φ g , λ η → dfunext (fe 𝓤 (𝓦 ⊔ 𝓤)) (λ x → dfunext (fe 𝓤 𝓦) (ψφ g η x )))
            , (φ g , λ θ → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ y → dfunext (fe 𝓤 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ C → dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (φψ g θ y C))))

  Σ-extension-left-Kan : (g : Y → 𝓤 ̇) → Nat f∖j g ≃ Nat f (g ∘ j)
  Σ-extension-left-Kan g = e
   where
    φ : (g : Y → 𝓤 ̇) → Nat f (g ∘ j) → Nat f∖j g
    φ g η y ((x , p) , C) = transport g p (η x C)

    ψ : (g : Y → 𝓤 ̇) → Nat f∖j g → Nat f (g ∘ j)
    ψ g θ x B = θ (j x) ((x , refl) , B)

    φψ : (g : Y → 𝓤 ̇) (θ : Nat f∖j g) (y : Y) (B : f∖j y) → φ g (ψ g θ) y B ≡ θ y B
    φψ g θ y ((x , refl) , B) = refl

    ψφ : (g : Y → 𝓤 ̇) (η : Nat f (g ∘ j)) (x : X) (B : f x) → ψ g (φ g η) x B ≡ η x B
    ψφ g η x B = refl

    e : Nat f∖j g ≃ Nat f (g ∘ j)
    e = ψ g , (φ g , λ η → dfunext (fe 𝓤 (𝓤 ⊔ 𝓦)) (λ x → dfunext (fe 𝓦 𝓤) (λ B → ψφ g η x B)))
            , (φ g , λ θ → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ y → dfunext (fe (𝓤 ⊔ 𝓥 ⊔ 𝓦) 𝓤) (λ C → φψ g θ y C)))

\end{code}

  Conjectural conjecture: the type

    Σ(f' : Y → 𝓤), Π(g : Y → 𝓤), Nat g f' = Nat (g∘f) f

  should be contractible assuming univalence. Similarly for left Kan
  extensions as discussed below.

  The above formula actually give extensions up to pointwise
  equivalence if j:X→Y is an embedding in the sense of univalent
  mathematics.

\begin{code}

  open import UF-PropIndexedPiSigma

  Π-extension-in-range : is-embedding j → (x : X) → f/j(j x) ≃ f x
  Π-extension-in-range e x = prop-indexed-product (fe (𝓤 ⊔ 𝓥) 𝓦) {fiber j (j x)} {λ (z : fiber j (j x)) → f (pr₁ z)} (e (j x)) (x , refl)

  Π-extension-equivalence : is-embedding j → (x : X) → is-equiv (λ (c : f/j (j x)) → c (x , refl))
  Π-extension-equivalence e x = pr₂ (Π-extension-in-range e x)

  Π-extension-out-of-range : ∀ {𝓦} (y : Y) → ((x : X) → j x ≢ y) → f/j(y) ≃ 𝟙 {𝓦}
  Π-extension-out-of-range y φ = prop-indexed-product-one (fe (𝓤 ⊔ 𝓥) 𝓦) (uncurry φ)

  Σ-extension-in-range : is-embedding j → (x : X) → f∖j(j x) ≃ f x
  Σ-extension-in-range e x = prop-indexed-sum (e(j x)) (x , refl)

  Σ-extension-out-of-range : (y : Y) → ((x : X) → j x ≢ y) → f∖j(y) ≃ 𝟘
  Σ-extension-out-of-range y φ = prop-indexed-sum-zero (uncurry φ)

\end{code}

  We now rewrite the Π-extension formula in an equivalent way:

\begin{code}

  2nd-Π-extension-formula : (y : Y) → f/j(y) ≃ Π \(x : X) → j x ≡ y → f x
  2nd-Π-extension-formula y = curry-uncurry fe

  2nd-Π-extension-formula' : (y : Y) → f/j(y) ≃ Nat (λ x → j x ≡ y) f
  2nd-Π-extension-formula' = 2nd-Π-extension-formula

  2nd-Σ-extension-formula : (y : Y) → f∖j(y) ≃ Σ \(x : X) → (j x ≡ y) × f x
  2nd-Σ-extension-formula y = Σ-assoc


\end{code}

  This is the Π-extension formula we actually used for (1) showing that
  the universe is indiscrete, and (2) defining the squashed sum and
  proving that it preserves searchability.

\begin{code}

  Π-observation : is-embedding j → (a : X) → f a ≃ (Π \(x : X) → j x ≡ j a → f x)
  Π-observation e a = ≃-sym (≃-trans (≃-sym (2nd-Π-extension-formula (j a)))
                                      (Π-extension-in-range e a))

  Σ-observation : is-embedding j → (a : X) → f a ≃ (Σ \(x : X) → (j x ≡ j a) × f x)
  Σ-observation e a = ≃-sym (≃-trans (≃-sym (2nd-Σ-extension-formula (j a)))
                                      (Σ-extension-in-range e a))

\end{code}

Added December 2017:

The extensions f/j and f∖j have the same product and sum as f
respectively:

\begin{code}

  same-Π : Π f ≃ Π f/j
  same-Π = F , (G , FG) , (G , GF)
    where
      F : Π f → Π f/j
      F φ y (x , p) = φ x

      G : Π f/j → Π f
      G ψ x = ψ (j x) (x , refl)

      FG' : (ψ : Π f/j) (y : Y) (σ : fiber j y) → F(G ψ) y σ ≡ ψ y σ
      FG' ψ x (_ , refl) = refl

      FG : (ψ : Π f/j) → F(G ψ) ≡ ψ
      FG ψ = dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ y → dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (FG' ψ y))

      GF : (φ : Π f) → G(F φ) ≡ φ
      GF φ = refl

  same-Σ : Σ f ≃ Σ f∖j
  same-Σ = F , (G , FG) , (G , GF)
    where
      F : Σ f → Σ f∖j
      F (x , y) = (j x , (x , refl) , y)

      G : Σ f∖j → Σ f
      G (y , (x , p) , y') = (x , y')

      FG : (σ : Σ f∖j) → F(G σ) ≡ σ
      FG (x , (_ , refl) , y') = refl

      GF : (σ : Σ f) → G(F σ) ≡ σ
      GF (x , y) = refl

\end{code}

(Conjectural conjecture (2nd July 2018): if j is an embedding, then we
have an embedding Σ f → Σ f/j.)

We now introduce the notations f / j and f ∖ j for the Π- and
Σ-extensions, outside the above anonymous module.

\begin{code}

_/_ _∖_ :  {X : 𝓤 ̇} {Y : 𝓥 ̇}
        → (X → 𝓦 ̇) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇)
f / j = Π-extension f j
f ∖ j = Σ-extension f j

\end{code}

Also added December 2017.

A different notation reflects a different view of these processes:

\begin{code}

inverse-image :  {X : 𝓤 ̇} {Y : 𝓥 ̇}
              → (X → Y) → (Y → 𝓦 ̇) → (X → 𝓦 ̇)

inverse-image f v = v ∘ f


Π-image Σ-image :  {X : 𝓤 ̇} {Y : 𝓥 ̇}
                → (X → Y) → ((X → 𝓦 ̇) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇))

Π-image j = λ f → Π-extension f j

Σ-image j = λ f → Σ-extension f j

\end{code}

Σ-images of singletons. Another way to see the following is with the
function same-Σ defined above. This and univalence give

 Σ (Id x) ≡ Σ (Id x ∖ j) = Σ-image j (Id x)

Hence

 is-singleton(Σ (Id x)) ≡ is-singleton(Σ-image j (Id x))

But the lhs holds, and hence is-singleton(Σ-image j (Id x)).

\begin{code}

Σ-image-of-singleton-lemma : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (j : X → Y) (x : X) (y : Y)
                           → Σ-image j (Id x) y ≃ Id (j x) y
Σ-image-of-singleton-lemma {𝓤} {𝓥} {X} {Y} j x y = (f , (g , fg) , (g , gf))
 where
  f : Σ-image j (Id x) y → Id (j x) y
  f ((x , refl) , refl) = refl

  g : Id (j x) y → Σ-image j (Id x) y
  g refl = (x , refl) , refl

  gf : (i : Σ-image j (Id x) y) → g(f i) ≡ i
  gf ((x , refl) , refl) = refl

  fg : (p : Id (j x) y) → f(g p) ≡ p
  fg refl = refl

Σ-image-of-singleton-lemma' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (j : X → Y) (x : X) (y : Y)
                            → (((Id x) ∖ j) y) ≃ (j x ≡ y)
Σ-image-of-singleton-lemma' = Σ-image-of-singleton-lemma

Σ-image-of-singleton : {X Y : 𝓤 ̇}
                     → is-univalent 𝓤
                     → (j : X → Y) (x : X) → Σ-image j (Id x) ≡ Id (j x)
Σ-image-of-singleton {𝓤} {X} {Y} ua j x = b
  where
   a : (y : Y) → Σ-image j (Id x) y ≡ Id (j x) y
   a y = eqtoid ua (Σ-image j (Id x) y) (Id (j x) y) (Σ-image-of-singleton-lemma j x y)

   b : Σ-image j (Id x) ≡ Id (j x)
   b = dfunext (fe 𝓤 (𝓤 ⁺)) a

Σ-image-of-singleton' : {X Y : 𝓤 ̇}
                      → is-univalent 𝓤
                      → (j : X → Y) (x : X) → (Id x) ∖ j ≡ Id (j x)
Σ-image-of-singleton' = Σ-image-of-singleton

\end{code}

There is more to do about this.

\begin{code}

Π-extension-is-extension : is-univalent 𝓤 → {X Y : 𝓤 ̇} (j : X → Y)
                         → is-embedding j
                         → (f : X → 𝓤 ̇) → (f / j) ∘ j ∼ f
Π-extension-is-extension ua j e f x = eqtoid ua _ _ (Π-extension-in-range f j e x)

Π-extension-is-extension' : is-univalent 𝓤 → funext 𝓤 (𝓤 ⁺)
                          → {X Y : 𝓤 ̇} (j : X → Y)
                          → is-embedding j
                          → (f : X → 𝓤 ̇) → (f / j) ∘ j ≡ f
Π-extension-is-extension' ua fe j e f = dfunext fe (Π-extension-is-extension ua j e f)

Π-extension-is-extension'' : is-univalent 𝓤 → funext 𝓤 (𝓤 ⁺) → funext (𝓤 ⁺) (𝓤 ⁺)
                           → {X Y : 𝓤 ̇} (j : X → Y)
                           → is-embedding j
                           → (λ f → (f / j) ∘ j) ≡ id
Π-extension-is-extension'' ua fe fe' j e = dfunext fe' (Π-extension-is-extension' ua fe j e)

\end{code}

We now consider injectivity, defined with Σ rather than ∃ (that is, as
data rather than property):

\begin{code}

injective-type : 𝓦 ̇ → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
injective-type {𝓤} {𝓥} D = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                         → (f : X → D) → Σ \(f' : Y → D) → f' ∘ j ∼ f

universes-are-injective-Π : is-univalent 𝓤 → injective-type {𝓤} {𝓤} (𝓤 ̇)
universes-are-injective-Π ua j e f = f / j , Π-extension-is-extension ua j e f

universes-are-injective-Σ : is-univalent 𝓤 → injective-type {𝓤} {𝓤} (𝓤 ̇)
universes-are-injective-Σ ua j e f = f ∖ j , λ x → eqtoid ua _ _ (Σ-extension-in-range f j e x)

retract-of-injective : {D : 𝓤 ̇} {D' : 𝓥 ̇}
                     → injective-type {𝓦} {𝓣} D
                     → retract D' Of D
                     → injective-type D'
retract-of-injective {𝓤} {𝓥} {𝓦} {𝓣} {D} {D'} i (r , ρ) {X} {Y} j e f = r ∘ g , go
  where
    s : D' → D
    s d' = pr₁ (ρ d')

    rs : r ∘ s ∼ id
    rs d' = pr₂(ρ d')

    g : Y → D
    g = pr₁(i j e (s ∘ f))

    h : g ∘ j ∼ s ∘ f
    h = pr₂(i j e (s ∘ f))

    go : r ∘ g ∘ j ∼ f
    go x = ap r (h x) ∙ rs (f x)

open import UF-IdEmbedding

injective-retract-of-power-of-universe : {D : 𝓤 ̇} → is-univalent 𝓤
                                       → injective-type D → retract D Of (D → 𝓤 ̇)
injective-retract-of-power-of-universe ua i = pr₁ a , λ y → Id y , pr₂ a y
  where
    a : Σ \r  → r ∘ Id ∼ id
    a = i Id (UA-Id-embedding ua fe) id

power-of-injective : {D : 𝓤 ̇} {A : 𝓥 ̇}
                   → injective-type {𝓦} {𝓣} D
                   → injective-type (A → D)
power-of-injective {𝓤} {𝓥} {𝓦} {𝓣} {D} {A} i {X} {Y} j e f = f' , g
  where
    l : (a : A) → Σ \(h : Y → D) → h ∘ j ∼ (λ x → f x a)
    l a = i j e (λ x → f x a)

    f' : Y → A → D
    f' y a = pr₁ (l a) y

    g : f' ∘ j ∼ f
    g x = dfunext (fe 𝓥 𝓤) (λ a → pr₂ (l a) x)

\end{code}

Added 18th July 2018. Notice that the function e : X → Y doesn't need
to be an embedding and that the proof is completely routine.

\begin{code}

retract-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X → 𝓦 ̇) (B : X → 𝓣 ̇) (e : X → Y)
               → ((x : X) → retract (A x) of (B x))
               → ((y : Y) → retract ((A / e) y) of ((B / e) y))
retract-extension {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} A B e ρ y = r , s , rs
 where
  R : (x : X) → B x → A x
  R x = pr₁(ρ x)
  S : (x : X) → A x → B x
  S x = pr₁(pr₂(ρ x))
  RS : (x : X) (a : A x) → R x (S x a) ≡ a
  RS x = pr₂(pr₂(ρ x))
  r : (B / e) y → (A / e) y
  r v (x , p) = R x (v (x , p))
  s : (A / e) y → (B / e) y
  s u (x , p) = S x (u (x , p))
  h : (u : (A / e) y) (σ : fiber e y) → r (s u) σ ≡ u σ
  h u (x , p) = RS x (u (x , p))
  rs : (u : (A / e) y) → r (s u) ≡ u
  rs u = dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (h u)

\end{code}

Added 25th July 2018.

\begin{code}

iterated-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {A : X → 𝓣 ̇}
                     (j : X → Y) (k : Y → Z)
                   → (z : Z) → ((A / j) / k) z ≃ (A / (k ∘ j)) z
iterated-extension {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {Z} {A} j k z = γ
 where
  f : ((A / j) / k) z → (A / (k ∘ j)) z
  f u (x , p) = u (j x , p) (x , refl)
  g : (A / (k ∘ j)) z → ((A / j) / k) z
  g v (.(j x) , q) (x , refl) = v (x , q)
  fg : (v : (A / (k ∘ j)) z) → f (g v) ≡ v
  fg v = refl
  gf' : (u : ((A / j) / k) z) (w : fiber k z) (t : fiber j (pr₁ w))
      → g (f u) w t ≡ u w t
  gf' u (.(j x) , q) (x , refl) = refl
  gf : (u : ((A / j) / k) z) → g (f u) ≡ u
  gf u = dfunext (fe (𝓥 ⊔ 𝓦) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
          (λ w → dfunext (fe (𝓤 ⊔ 𝓥) 𝓣) (gf' u w))
  γ : ((A / j) / k) z ≃ (A / (k ∘ j)) z
  γ = f , ((g , fg) , (g , gf))

\end{code}

Added 9th November 2018.

We want to show that f ↦ f/j is an embedding of (X → 𝓤) into (Y → 𝓤)
if j is an embedding.

                   j
              X ------> Y
               \       /
                \     /
             f   \   / f/j
                  \ /
                   v
                   𝓤

The simplest case is X = P and Y = 𝟙, where P is a proposition. Then
the map P → 𝟙 is an embedding.

                   j
              P ------> 𝟙
               \       /
                \     /
              f  \   / (f / j) (x) = Π (w : fiber j x) → f(pr₁ w)
                  \ /              ≃ Π (p : P) → j p ≡ x → f p
                   v               ≃ Π (p : P) → f p
                   𝓤

So in essence we are considering the map E : (P → 𝓤) → 𝓤 defined by

   E f = Π (p : P) → f p.

Then, for any A : 𝓤,

  fiber E A = Σ \(f : P → 𝓤) → Π (p : P) → f p

A few days pause. Now 15th Nov 2018 after a discussion in the HoTT list.
https://groups.google.com/d/topic/homotopytypetheory/xvx5hOEPnDs/discussion

Here is my take on the outcome of the discussion, following
independent solutions by Shulman and Capriotti.

\begin{code}

open import UF-Subsingletons

module extension-is-embedding-special-case
         (P : 𝓤 ̇)
         (i : is-prop P)
         (ua : is-univalent 𝓤)
 where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt

 s : (P → 𝓤 ̇) → 𝓤 ̇
 s = Π

 κ : (X : 𝓤 ̇) → X → (P → X)
 κ X x p = x

 M : 𝓤 ⁺ ̇

 M = Σ \(X : 𝓤 ̇) → is-equiv (κ X)

 φ : (P → 𝓤 ̇) → M
 φ A = s A , qinvs-are-equivs (κ (s A)) (δ , ε , η)
  where
   δ : (P → s A) → s A
   δ v p = v p p
   η : (v : P → s A) → κ (s A) (δ v) ≡ v
   η v = dfunext (fe 𝓤 𝓤) (λ p → dfunext (fe 𝓤 𝓤) (λ q → ap (λ - → v - q) (i q p)))
   ε : (u : Π A) → δ (κ (s A) u) ≡ u
   ε u = refl

 γ : M → (P → 𝓤 ̇)
 γ (X , i) p = X

 φγ : (m : M) → φ (γ m) ≡ m
 φγ (X , i) = to-Σ-≡ (eqtoid ua (P → X) X (≃-sym (κ X , i)) ,
                      being-equiv-is-a-prop fe (κ X) _ i)

 γφ : (A : P → 𝓤 ̇) → γ (φ A) ≡ A
 γφ A = dfunext (fe 𝓤 (𝓤 ⁺)) (λ p → eqtoid ua (s A) (A p) (prop-indexed-product (fe 𝓤 𝓤) i p))

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → 𝓤 ̇
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-embedding (λ X → being-equiv-is-a-prop fe (κ X))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding  : is-embedding s
 s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding

\end{code}

Additional information.

\begin{code}

 r :  𝓤 ̇ → (P → 𝓤 ̇)
 r X p = X

 rs : ∀ A → r (s A) ≡ A
 rs = γφ

 sr : ∀ X → s (r X) ≡ (P → X)
 sr X = refl

\end{code}

In general, sections are not embeddings (see Theorem 3.10 of Shulman's
paper "Idempotents in intensional type theory" https://arxiv.org/abs/1507.03634),
but in this case the section s : (P → 𝓤 ̇) → 𝓤 ̇ happens to be an embedding.

To be continued, now using this to prove that f ↦ f / j is an embedding for any embedding j:X→Y.
