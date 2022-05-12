Martin Escardo, 27 April 2014, with later additions, 2017, 2018, 2019.

This is a "blackboard" Agda file, which means that the ideas are
reported in the order they come to mind (with the very bad ideas
deleted, and with some intermediate useful ideas kept, even if they
are not intended to make their way to publication). See the file
InjectiveTypes-article for an organized presentation.

This introduction is incomplete and outdated / obsolete. Much more has
been done since 2014 that is not reported here.

We show that the injective types are the retracts of the exponential
powers of universes, where an exponential power of a type D is a type
of the form A → D for some type A. Injectivity is defined as
(functional) data rather than property.


Injectivity of the universe (2014)
----------------------------

Here we have definitions and proofs in Agda notation, which assume a
univalent mathematics background (e.g. given by the HoTT book),
preceded by informal (rigorous) discussion.

We show that the universe is (pointwise right-Kan) injective wrt
embeddings. An embedding is a map j:X→Y whose fibers are all univalent
propositions.

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
                \  ≳  /
             f   \   / f/j
                  \ /
                   v
                   𝓤

in the sense that the type of natural transformations from "presheaves"
g : Y → 𝓤 to the "presheaf" f/j, written

     g ≾ f/j,

is naturally equivalent to the type g∘j ≾ f of natural
transformations from g∘j to f:

     g ≾ f/j ≃ g∘j ≾ f

If j is an embedding (in the sense of univalent mathematics), then,
for any f, we can find f/j which is both a right-Kan extension and a
(proper) extension (up to equivalence).

All this dualizes with Π replaced by Σ and right replaced by left.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline  #-}

open import UF-FunExt

module InjectiveTypes (fe : FunExt) where

open import SpartanMLTT
open import Plus-Properties
open import PairFun

open import UF-Base
open import UF-Equiv
open import UF-Embeddings
open import UF-Retracts
open import UF-EquivalenceExamples
open import UF-Univalence
open import UF-IdEmbedding
open import UF-PropIndexedPiSigma
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Size
open import UF-PropTrunc
open import UF-UniverseEmbedding
open import UF-ExcludedMiddle
open import UF-Lower-FunExt

\end{code}

Here is how we define f/j given f and j.

                   j
              X ------> Y
               \       /
                \  ≳  /
             f   \   / f/j
                  \ /
                   v
                   𝓤

We have to apply the following constructions for 𝓤=𝓥=𝓦 for the above
triangles to make sense.

We rename the type of natural transformations:

\begin{code}

_≾_ : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
_≾_ = Nat

_≾_-explicitly : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
               → A ≾ B ≡ ((x : X) → A x → B x)
_≾_-explicitly A B = refl

\end{code}

We think of A and B as some sort ∞-presheaves, with the category of
sets replaced by a universe of ∞-groupoids.

Natural transformations are automatically natural: for all x,y: A and
p : x ≡ y,

                        τ x
               A x --------------→ B x
                |                   |
                |                   |
           A[p] |                   | B[p]
                |                   |
                |                   |
                ↓                   ↓
               A y --------------→ B y
                        τ y

\begin{code}

≾-naturality : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (τ : A ≾ B)
             → {x y : X} (p : x ≡ y) → τ y ∘ transport A p ≡ transport B p ∘ τ x
≾-naturality = Nats-are-natural

\end{code}

We now work with the following assumptions:

\begin{code}

module _ {X : 𝓤 ̇ }
         {Y : 𝓥 ̇ }
         (f : X → 𝓦 ̇ )
         (j : X → Y)
       where

  Π-extension Σ-extension : Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  Π-extension y = Π (x , _) ꞉ fiber j y , f x
  Σ-extension y = Σ (x , _) ꞉ fiber j y , f x

  private
   f/j f∖j : Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
   f/j = Π-extension
   f∖j = Σ-extension

  Σ→Π : is-embedding j → f∖j ≾ f/j
  Σ→Π e y ((x , p) , B) (x' , p') = transport f (embeddings-are-lc j e (p ∙ p' ⁻¹)) B

\end{code}

  The natural transformation Σ→Π j itself should be a natural
  embedding (conjectural conjecture).

\begin{code}

  ηΠ : f/j ∘ j ≾ f
  ηΠ x C = C (x , refl)

  ηΣ : f ≾ f∖j ∘ j
  ηΣ x B = (x , refl) , B

\end{code}

  For arbitrary j:X→Y, this gives Kan extensions in the following
  sense:

\begin{code}

  Π-extension-right-Kan : (g : Y → 𝓣 ̇ ) → (g ≾ f/j) ≃  (g ∘ j ≾ f)
  Π-extension-right-Kan {𝓣} g = qinveq (ψ g) (φ g , φψ' g , ψφ' g)
   where
    φ : (g : Y → 𝓣 ̇ ) → g ∘ j ≾ f → g ≾ f/j
    φ g η y C (x , p) = η x (transport⁻¹ g p C)

    ψ : (g : Y → 𝓣 ̇ ) → g ≾ f/j → g ∘ j ≾ f
    ψ g θ x C = θ (j x) C (x , refl)

    ψφ : (g : Y → 𝓣 ̇ ) (η : g ∘ j ≾ f) (x : X) (C : g (j x)) → ψ g (φ g η) x C ≡ η x C
    ψφ g η x C = refl

    ψφ' : (g : Y → 𝓣 ̇ ) (η : g ∘ j ≾ f) → ψ g (φ g η) ≡ η
    ψφ' g η = dfunext (fe 𝓤 (𝓦 ⊔ 𝓣)) (λ x → dfunext (fe 𝓣 𝓦) (ψφ g η x))

    φψ : (g : Y → 𝓣 ̇ ) (θ : g ≾ f/j) (y : Y) (C : g y) (w : fiber j y) → φ g (ψ g θ) y C w ≡ θ y C w
    φψ g θ y C (x , refl) = refl

    φψ' : (g : Y → 𝓣 ̇ ) (θ : g ≾ f/j) → φ g (ψ g θ) ≡ θ
    φψ' g θ = dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)) (λ y → dfunext (fe 𝓣 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ C → dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (φψ g θ y C)))

  Σ-extension-left-Kan : (g : Y → 𝓣 ̇ ) → (f∖j ≾ g) ≃ (f ≾ g ∘ j)
  Σ-extension-left-Kan {𝓣} g = e
   where
    φ : (g : Y → 𝓣 ̇ ) → f ≾ g ∘ j → f∖j ≾ g
    φ g η y ((x , p) , C) = transport g p (η x C)

    ψ : (g : Y → 𝓣 ̇ ) → f∖j ≾ g → f ≾ g ∘ j
    ψ g θ x B = θ (j x) ((x , refl) , B)

    φψ : (g : Y → 𝓣 ̇ ) (θ : f∖j ≾ g) (y : Y) (B : f∖j y) → φ g (ψ g θ) y B ≡ θ y B
    φψ g θ y ((x , refl) , B) = refl

    ψφ : (g : Y → 𝓣 ̇ ) (η : f ≾ g ∘ j) (x : X) (B : f x) → ψ g (φ g η) x B ≡ η x B
    ψφ g η x B = refl

    e : f∖j ≾ g ≃ f ≾ g ∘ j
    e = ψ g , (φ g , λ η → dfunext (fe 𝓤 (𝓦 ⊔ 𝓣)) (λ x → dfunext (fe 𝓦 𝓣) (λ B → ψφ g η x B)))
            , (φ g , λ θ → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)) (λ y → dfunext (fe (𝓤 ⊔ 𝓥 ⊔ 𝓦) 𝓣) (λ C → φψ g θ y C)))

\end{code}

  Conjectural conjecture: the type

    Σ (f' : Y → 𝓤), Π (g : Y → 𝓤), g ≾ f' ≃ g∘j ≾ f

  should be contractible assuming univalence. Similarly for left Kan
  extensions as discussed below.

  The above formula actually give extensions up to pointwise
  equivalence if j:X→Y is an embedding in the sense of univalent
  mathematics.

\begin{code}

  Π-extension-property : is-embedding j → (x : X) → f/j (j x) ≃ f x
  Π-extension-property e x = prop-indexed-product (fe (𝓤 ⊔ 𝓥) 𝓦)
                              {fiber j (j x)} {λ (z : fiber j (j x)) → f (fiber-point z)}
                              (e (j x))
                              (x , refl)

  Π-extension-equivalence : is-embedding j → (x : X) → is-equiv (Π-proj (x , refl))
  Π-extension-equivalence e x = pr₂ (Π-extension-property e x)

  Π-extension-out-of-range : ∀ {𝓦} (y : Y) → ((x : X) → j x ≢ y) → f/j (y) ≃ 𝟙 {𝓦}
  Π-extension-out-of-range y φ = prop-indexed-product-one (fe (𝓤 ⊔ 𝓥) 𝓦) (uncurry φ)

  Σ-extension-property : is-embedding j → (x : X) → f∖j (j x) ≃ f x
  Σ-extension-property e x = prop-indexed-sum (e (j x)) (x , refl)

  Σ-extension-out-of-range : (y : Y) → ((x : X) → j x ≢ y) → f∖j (y) ≃ 𝟘 {𝓦}
  Σ-extension-out-of-range y φ = prop-indexed-sum-zero (uncurry φ)

\end{code}

  We now rewrite the Π-extension formula in an equivalent way:

\begin{code}

  2nd-Π-extension-formula : (y : Y) → f/j (y) ≃ (Π x ꞉ X , (j x ≡ y → f x))
  2nd-Π-extension-formula y = curry-uncurry fe

  2nd-Π-extension-formula' : (y : Y) → f/j (y) ≃ (λ x → j x ≡ y) ≾ f
  2nd-Π-extension-formula' = 2nd-Π-extension-formula

  2nd-Σ-extension-formula : (y : Y) → f∖j (y) ≃ (Σ x ꞉ X , (j x ≡ y) × f x)
  2nd-Σ-extension-formula y = Σ-assoc


\end{code}

  This is the Π-extension formula we actually used for (1) showing that
  the universe is indiscrete, and (2) defining the squashed sum and
  proving that it preserves searchability.

\begin{code}

  Π-observation : is-embedding j → (a : X) → f a ≃ (Π x ꞉ X , (j x ≡ j a → f x))
  Π-observation e a = ≃-sym ((≃-sym (2nd-Π-extension-formula (j a))) ●
                                      (Π-extension-property e a))

  Σ-observation : is-embedding j → (a : X) → f a ≃ (Σ x ꞉ X , (j x ≡ j a) × f x)
  Σ-observation e a = ≃-sym ((≃-sym (2nd-Σ-extension-formula (j a))) ●
                                      (Σ-extension-property e a))

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

      FG' : (ψ : Π f/j) (y : Y) (σ : fiber j y) → F (G ψ) y σ ≡ ψ y σ
      FG' ψ x (_ , refl) = refl

      FG : (ψ : Π f/j) → F (G ψ) ≡ ψ
      FG ψ = dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ y → dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (FG' ψ y))

      GF : (φ : Π f) → G (F φ) ≡ φ
      GF φ = refl

  same-Σ : Σ f ≃ Σ f∖j
  same-Σ = F , (G , FG) , (G , GF)
    where
      F : Σ f → Σ f∖j
      F (x , y) = (j x , (x , refl) , y)

      G : Σ f∖j → Σ f
      G (y , (x , p) , y') = (x , y')

      FG : (σ : Σ f∖j) → F (G σ) ≡ σ
      FG (x , (_ , refl) , y') = refl

      GF : (σ : Σ f) → G (F σ) ≡ σ
      GF (x , y) = refl

\end{code}

We now introduce the notations f / j and f ∖ j for the Π- and
Σ-extensions, outside the above anonymous module.

\begin{code}

_/_ _∖_ :  {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
        → (X → 𝓦 ̇ ) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ )
f / j = Π-extension f j
f ∖ j = Σ-extension f j

infix 7 _/_

\end{code}

Also added December 2017.

A different notation reflects a different view of these processes:

\begin{code}

inverse-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (X → Y) → (Y → 𝓦 ̇ ) → (X → 𝓦 ̇ )
inverse-image f v = v ∘ f


Π-image Σ-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (X → Y)
                → ((X → 𝓦 ̇ ) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇ ))
Π-image j = λ f → Π-extension f j

Σ-image j = λ f → Σ-extension f j

\end{code}

Σ-images of singletons. Another way to see the following is with the
function same-Σ defined above. This and univalence give

 Σ (Id x) ≡ Σ (Id x ∖ j) = Σ-image j (Id x)

Hence

 is-singleton (Σ (Id x)) ≡ is-singleton (Σ-image j (Id x))

But the lhs holds, and hence is-singleton (Σ-image j (Id x)).

\begin{code}

Σ-image-of-singleton-lemma : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (j : X → Y) (x : X) (y : Y)
                           → Σ-image j (Id x) y ≃ Id (j x) y
Σ-image-of-singleton-lemma {𝓤} {𝓥} {X} {Y} j x y = (f , (g , fg) , (g , gf))
 where
  f : Σ-image j (Id x) y → Id (j x) y
  f ((x , refl) , refl) = refl

  g : Id (j x) y → Σ-image j (Id x) y
  g refl = (x , refl) , refl

  gf : (i : Σ-image j (Id x) y) → g (f i) ≡ i
  gf ((x , refl) , refl) = refl

  fg : (p : Id (j x) y) → f (g p) ≡ p
  fg refl = refl

Σ-image-of-singleton-lemma' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (j : X → Y) (x : X) (y : Y)
                            → (((Id x) ∖ j) y) ≃ (j x ≡ y)
Σ-image-of-singleton-lemma' = Σ-image-of-singleton-lemma

Σ-image-of-singleton : {X Y : 𝓤 ̇ }
                     → is-univalent 𝓤
                     → (j : X → Y) (x : X) → Σ-image j (Id x) ≡ Id (j x)
Σ-image-of-singleton {𝓤} {X} {Y} ua j x = b
  where
   a : (y : Y) → Σ-image j (Id x) y ≡ Id (j x) y
   a y = eqtoid ua (Σ-image j (Id x) y) (Id (j x) y) (Σ-image-of-singleton-lemma j x y)

   b : Σ-image j (Id x) ≡ Id (j x)
   b = dfunext (fe 𝓤 (𝓤 ⁺)) a

Σ-image-of-singleton' : {X Y : 𝓤 ̇ }
                      → is-univalent 𝓤
                      → (j : X → Y) (x : X) → (Id x) ∖ j ≡ Id (j x)
Σ-image-of-singleton' = Σ-image-of-singleton

\end{code}

There is more to do about this.

\begin{code}

Π-extension-is-extension : is-univalent (𝓤 ⊔ 𝓥) → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                         → is-embedding j
                         → (f : X → 𝓤 ⊔ 𝓥 ̇ ) → (f / j) ∘ j ∼ f
Π-extension-is-extension ua j e f x = eqtoid ua _ _ (Π-extension-property f j e x)

Π-extension-is-extension' : is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                          → is-embedding j
                          → (f : X → 𝓤 ⊔ 𝓥 ̇ ) → (f / j) ∘ j ≡ f
Π-extension-is-extension' ua fe j e f = dfunext fe (Π-extension-is-extension ua j e f)

Π-extension-is-extension'' : is-univalent (𝓤 ⊔ 𝓥)
                           → funext ((𝓤 ⊔ 𝓥)⁺) ((𝓤 ⊔ 𝓥)⁺)
                           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                           → is-embedding j
                           → (λ f → (f / j) ∘ j) ≡ id
Π-extension-is-extension'' {𝓤} {𝓥} ua fe j e = dfunext fe (Π-extension-is-extension' ua (lower-fun-ext 𝓤 fe) j e)

Σ-extension-is-extension : is-univalent (𝓤 ⊔ 𝓥) → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                         → is-embedding j
                         → (f : X → 𝓤 ⊔ 𝓥 ̇ ) → (f ∖ j) ∘ j ∼ f
Σ-extension-is-extension ua j e f x = eqtoid ua _ _ (Σ-extension-property f j e x)

Σ-extension-is-extension' : is-univalent (𝓤 ⊔ 𝓥)
                          → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                          → is-embedding j
                          → (f : X → 𝓤 ⊔ 𝓥 ̇ ) → (f ∖ j) ∘ j ≡ f
Σ-extension-is-extension' ua fe j e f = dfunext fe (Σ-extension-is-extension ua j e f)

Σ-extension-is-extension'' : is-univalent (𝓤 ⊔ 𝓥)
                           → funext ((𝓤 ⊔ 𝓥)⁺) ((𝓤 ⊔ 𝓥)⁺)
                           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y)
                           → is-embedding j
                           → (λ f → (f ∖ j) ∘ j) ≡ id
Σ-extension-is-extension'' {𝓤} {𝓥} ua fe j e = dfunext fe
                                                 (Σ-extension-is-extension' ua
                                                   (lower-fun-ext 𝓤 fe) j e)
\end{code}

We now consider injectivity, defined with Σ rather than ∃ (that is, as
data rather than property), called algebraic injectivity.

\begin{code}

ainjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
ainjective-type D 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y) → is-embedding j
                      → (f : X → D) → Σ f' ꞉ (Y → D) , f' ∘ j ∼ f

embedding-retract : (D : 𝓦 ̇ ) (Y : 𝓥 ̇ ) (j : D → Y)
                  → is-embedding j
                  → ainjective-type D 𝓦 𝓥
                  → retract D of Y
embedding-retract D Y j e i = pr₁ a , j , pr₂ a
 where
  a : Σ f' ꞉ (Y → D) , f' ∘ j ∼ id
  a = i j e id

retract-of-ainjective : (D' : 𝓦' ̇ ) (D : 𝓦 ̇ )
                      → ainjective-type D 𝓤 𝓥
                      → retract D' of D
                      → ainjective-type D' 𝓤 𝓥
retract-of-ainjective D' D i (r , (s , rs)) {X} {Y} j e f = φ a
  where
   a : Σ f' ꞉ (Y → D) , f' ∘ j ∼ s ∘ f
   a = i j e (s ∘ f)

   φ : (Σ f' ꞉ (Y → D) , f' ∘ j ∼ s ∘ f) → Σ f'' ꞉ (Y → D') , f'' ∘ j ∼ f
   φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))

equiv-to-ainjective : (D' : 𝓦' ̇ ) (D : 𝓦 ̇ )
                    → ainjective-type D 𝓤 𝓥
                    → D' ≃ D
                    → ainjective-type D' 𝓤 𝓥
equiv-to-ainjective D' D i e = retract-of-ainjective D' D i (≃-gives-◁ e)

universes-are-ainjective-Π : is-univalent (𝓤 ⊔ 𝓥) → ainjective-type (𝓤 ⊔ 𝓥 ̇ ) 𝓤 𝓥
universes-are-ainjective-Π ua j e f = f / j , Π-extension-is-extension ua j e f

universes-are-ainjective-Π' : is-univalent 𝓤 → ainjective-type (𝓤 ̇ ) 𝓤 𝓤
universes-are-ainjective-Π' = universes-are-ainjective-Π

universes-are-ainjective-Σ : is-univalent (𝓤 ⊔ 𝓥)
                           → ainjective-type (𝓤 ⊔ 𝓥 ̇ ) 𝓤 𝓥
universes-are-ainjective-Σ ua j e f = f ∖ j ,
                                      (λ x → eqtoid ua _ _ (Σ-extension-property f j e x))

ainjective-is-retract-of-power-of-universe : (D : 𝓤 ̇ ) → is-univalent 𝓤
                                           → ainjective-type D 𝓤  (𝓤 ⁺)
                                           → retract D of (D → 𝓤 ̇ )
ainjective-is-retract-of-power-of-universe {𝓤} D ua = embedding-retract D (D → 𝓤 ̇ ) Id (UA-Id-embedding ua fe)

Π-ainjective : {A : 𝓣 ̇ } {D : A → 𝓦 ̇ }
             → ((a : A) → ainjective-type (D a) 𝓤 𝓥)
             → ainjective-type (Π D) 𝓤 𝓥
Π-ainjective {𝓣}  {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = f' , g
  where
    l : (a : A) → Σ h ꞉ (Y → D a) , h ∘ j ∼ (λ x → f x a)
    l a = (i a) j e (λ x → f x a)

    f' : Y → (a : A) → D a
    f' y a = pr₁ (l a) y

    g : f' ∘ j ∼ f
    g x = dfunext (fe 𝓣 𝓦) (λ a → pr₂ (l a) x)

power-of-ainjective : {A : 𝓣 ̇ } {D : 𝓦 ̇ }
                    → ainjective-type D 𝓤 𝓥
                    → ainjective-type (A → D) 𝓤 𝓥
power-of-ainjective i = Π-ainjective (λ a → i)

\end{code}

The following is the first of a number of injectivity resizing
constructions:

\begin{code}

ainjective-resizing₀ : is-univalent 𝓤
                     → (D : 𝓤 ̇ ) → ainjective-type D 𝓤 (𝓤 ⁺) → ainjective-type D 𝓤 𝓤
ainjective-resizing₀ {𝓤} ua D i = φ (ainjective-is-retract-of-power-of-universe D ua i)
 where
  φ : retract D of (D → 𝓤 ̇ ) → ainjective-type D 𝓤 𝓤
  φ = retract-of-ainjective D (D → 𝓤 ̇ )
       (power-of-ainjective (universes-are-ainjective-Π ua))

\end{code}

Propositional resizing gives a much more general injectivity resizing
(see below).

Added 18th July 2018. Notice that the function e : X → Y doesn't need
to be an embedding and that the proof is completely routine.

\begin{code}

retract-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X → 𝓦 ̇ ) (B : X → 𝓣 ̇ ) (e : X → Y)
                  → ((x : X) → retract (A x) of (B x))
                  → ((y : Y) → retract ((A / e) y) of ((B / e) y))
retract-extension {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} A B e ρ y = r , s , rs
 where
  R : (x : X) → B x → A x
  R x = retraction (ρ x)

  S : (x : X) → A x → B x
  S x = section (ρ x)

  RS : (x : X) (a : A x) → R x (S x a) ≡ a
  RS x = retract-condition (ρ x)

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

iterated-extension : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {A : X → 𝓣 ̇ }
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

  gf' : (u : ((A / j) / k) z) (w : fiber k z) (t : fiber j (fiber-point w))
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
              f  \   / (f / j) (x) = Π (w : fiber j x) → f (fiber-point w)
                  \ /              ≃ Π (p : P) → j p ≡ x → f p
                   v               ≃ Π (p : P) → f p
                   𝓤

So in essence we are considering the map s : (P → 𝓤) → 𝓤 defined by

   s f = Π (p : P) → f p.

Then, for any X : 𝓤,

  fiber s X = Σ f ꞉ P → 𝓤 , (Π (p : P) → f p) ≡ X.

A few days pause. Now 15th Nov 2018 after a discussion in the HoTT list.
https://groups.google.com/d/topic/homotopytypetheory/xvx5hOEPnDs/discussion

Here is my take on the outcome of the discussion, following
independent solutions by Shulman and Capriotti.

\begin{code}

module /-extension-is-embedding-special-case
         (P : 𝓤 ̇ )
         (i : is-prop P)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-Equiv-FunExt
 open import UF-UA-FunExt

 feuu : funext 𝓤 𝓤
 feuu = univalence-gives-funext ua

 r :  𝓤 ̇ → (P → 𝓤 ̇ )
 r X p = X

 s : (P → 𝓤 ̇ ) → 𝓤 ̇
 s = Π

 rs : ∀ A → r (s A) ≡ A
 rs A = dfunext fe' (λ p → eqtoid ua (s A) (A p) (prop-indexed-product feuu i p))

 sr : ∀ X → s (r X) ≡ (P → X)
 sr X = refl

 κ : (X : 𝓤 ̇ ) → X → s (r X)
 κ X x p = x

 M : 𝓤 ⁺ ̇
 M = Σ X ꞉ 𝓤 ̇ , is-equiv (κ X)

 φ : (P → 𝓤 ̇ ) → M
 φ A = s A , qinvs-are-equivs (κ (s A)) (δ , ε , η)
  where
   δ : (P → s A) → s A
   δ v p = v p p

   η : (v : P → s A) → κ (s A) (δ v) ≡ v
   η v = dfunext feuu (λ p → dfunext feuu (λ q → ap (λ - → v - q) (i q p)))

   ε : (u : Π A) → δ (κ (s A) u) ≡ u
   ε u = refl

 γ : M → (P → 𝓤 ̇ )
 γ (X , i) = r X

 φγ : (m : M) → φ (γ m) ≡ m
 φγ (X , i) = to-Σ-≡ (eqtoid ua (P → X) X (≃-sym (κ X , i)) ,
                      being-equiv-is-prop fe (κ X) _ i)

 γφ : (A : P → 𝓤 ̇ ) → γ (φ A) ≡ A
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → 𝓤 ̇
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-is-embedding (λ X → being-equiv-is-prop fe (κ X))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = ∘-is-embedding φ-is-embedding ψ-is-embedding

\end{code}

Also 15th Nov 2018. We have a dual situation:

\begin{code}

module ∖-extension-is-embedding-special-case
         (P : 𝓤 ̇ )
         (i : is-prop P)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt

 s : (P → 𝓤 ̇ ) → 𝓤 ̇
 s = Σ

 r :  𝓤 ̇ → (P → 𝓤 ̇ )
 r X p = X

 rs : ∀ A → r (s A) ≡ A
 rs A = dfunext fe' (λ p → eqtoid ua (Σ A) (A p) (prop-indexed-sum i p))

 sr : ∀ X → s (r X) ≡ P × X
 sr X = refl

 κ : (X : 𝓤 ̇ ) → s (r X) → X
 κ X = pr₂

 C : 𝓤 ⁺ ̇
 C = Σ X ꞉ 𝓤 ̇ , is-equiv (κ X)

 φ : (P → 𝓤 ̇ ) → C
 φ A = s A , qinvs-are-equivs (κ (s A)) (δ , ε , η)
  where
   δ : s A → P × s A
   δ (p , a) = p , p , a

   η : (σ : s A) → κ (s A) (δ σ) ≡ σ
   η σ = refl

   ε : (τ : P × s A) → δ (κ (s A) τ) ≡ τ
   ε (p , q , a) = to-×-≡ (i q p) refl

 γ : C → (P → 𝓤 ̇ )
 γ (X , i) = r X

 φγ : (c : C) → φ (γ c) ≡ c
 φγ (X , i) = to-Σ-≡ (eqtoid ua (P × X) X (κ X , i) ,
                     (being-equiv-is-prop fe (κ X) _ i))

 γφ : (A : P → 𝓤 ̇ ) → γ (φ A) ≡ A
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : C → 𝓤 ̇
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-is-embedding (λ X → being-equiv-is-prop fe (κ X))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = ∘-is-embedding φ-is-embedding ψ-is-embedding

\end{code}

Added 20th November 2018.

\begin{code}

module /-extension-is-embedding
         (X Y : 𝓤 ̇ )
         (j : X → Y)
         (i : is-embedding j)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt
 open import UF-Subsingletons-FunExt
 open import UF-UA-FunExt

 feuu : funext 𝓤 𝓤
 feuu = univalence-gives-funext ua

 s : (X → 𝓤 ̇ ) → (Y → 𝓤 ̇ )
 s f = f / j

 r : (Y → 𝓤 ̇ ) → (X → 𝓤 ̇ )
 r g = g ∘ j

 rs : ∀ f → r (s f) ≡ f
 rs = Π-extension-is-extension' ua fe' j i

 sr : ∀ g → s (r g) ≡ (g ∘ j) / j
 sr g = refl

 κ : (g : Y → 𝓤 ̇ ) → g ≾ s (r g)
 κ g y C (x , p) = transport⁻¹ g p C

 M : (𝓤 ⁺) ̇
 M = Σ g ꞉ (Y → 𝓤 ̇ ), ((y : Y) → is-equiv (κ g y))

 φ : (X → 𝓤 ̇ ) → M
 φ f = s f , e
  where
   e : (y : Y) → is-equiv (κ (s f) y)
   e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
    where
     δ : (((f / j) ∘ j) / j) y → (f / j) y
     δ C (x , p) = C (x , p) (x , refl)

     η : (C : ((f / j ∘ j) / j) y) → κ (s f) y (δ C) ≡ C
     η C = dfunext feuu g
      where
       g : (w : fiber j y) → κ (s f) y (δ C) w ≡ C w
       g (x , refl) = dfunext feuu h
        where
         h : (t : fiber j (j x)) → C t (pr₁ t , refl) ≡ C (x , refl) t
         h (x' , p') = transport (λ - → C - (pr₁ - , refl) ≡ C (x , refl) -) q refl
          where
           q : (x , refl) ≡ (x' , p')
           q = i (j x) (x , refl) (x' , p')

     ε : (a : (f / j) y) → δ (κ (s f) y a) ≡ a
     ε a = dfunext feuu g
      where
       g : (w : fiber j y) → δ (κ (s f) y a) w ≡ a w
       g (x , refl) = refl

 γ : M → (X → 𝓤 ̇ )
 γ (g , e) = r g

 φγ : ∀ m → φ (γ m) ≡ m
 φγ (g , e) = to-Σ-≡
               (dfunext fe' (λ y → eqtoid ua (s (r g) y) (g y) (≃-sym (κ g y , e y))) ,
                Π-is-prop feuu (λ y → being-equiv-is-prop'' feuu (κ g y)) _ e)

 γφ : ∀ f → γ (φ f) ≡ f
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → (Y → 𝓤 ̇ )
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-is-embedding (λ g → Π-is-prop feuu (λ y → being-equiv-is-prop'' feuu (κ g y)))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = ∘-is-embedding φ-is-embedding ψ-is-embedding

\end{code}

Added 21th November 2018.

\begin{code}

module ∖-extension-is-embedding
         (X Y : 𝓤 ̇ )
         (j : X → Y)
         (i : is-embedding j)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt
 open import UF-Subsingletons-FunExt
 open import UF-UA-FunExt

 feuu : funext 𝓤 𝓤
 feuu = univalence-gives-funext ua

 s : (X → 𝓤 ̇ ) → (Y → 𝓤 ̇ )
 s f = f ∖ j

 r : (Y → 𝓤 ̇ ) → (X → 𝓤 ̇ )
 r g = g ∘ j

 rs : ∀ f → r (s f) ≡ f
 rs = Σ-extension-is-extension' ua fe' j i

 sr : ∀ g → s (r g) ≡ (g ∘ j) ∖ j
 sr g = refl

 κ : (g : Y → 𝓤 ̇ ) → s (r g) ≾ g
 κ g y ((x , p) , C) = transport g p C

 M : (𝓤 ⁺) ̇
 M = Σ g ꞉ (Y → 𝓤 ̇ ), ((y : Y) → is-equiv (κ g y))

 φ : (X → 𝓤 ̇ ) → M
 φ f = s f , e
  where
   e : (y : Y) → is-equiv (κ (s f) y)
   e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
    where
     δ : (Σ (x , _) ꞉ fiber j y , f x)
       → Σ t ꞉ fiber j y , Σ (x , _) ꞉ fiber j (j (pr₁ t)), f x
     δ ((x , p) , C) = (x , p) , (x , refl) , C

     η : (σ : s f y) → κ (s f) y (δ σ) ≡ σ
     η ((x , refl) , C) = refl

     ε : (τ : Σ (λ w → r (s f) (pr₁ w))) → δ (κ (s f) y τ) ≡ τ
     ε ((x , refl) , (x' , p') , C) = t x x' (pa x' x p') p' C (appa x x' p')
      where
        t : (x x' : X) (u : x' ≡ x) (p : j x' ≡ j x) (C : f x') → (ap j u ≡ p) →
            ((x' , p)    , (x' , refl) , C)
          ≡ (((x  , refl) , (x' , p)    , C) ∶ (Σ (x , _) ꞉  fiber j (j x) , r (s f) x))
        t x .x refl p C refl = refl

        ej' : ∀ x x' → qinv (ap j {x} {x'})
        ej' x x' = equivs-are-qinvs (ap j) (embedding-embedding' j i x x')

        pa : ∀ x x' → j x ≡ j x' → x ≡ x'
        pa x x' = pr₁ (ej' x x')

        appa : ∀ x x' p' → ap j (pa x' x p') ≡ p'
        appa x x' = pr₂ (pr₂ (ej' x' x))

 γ : M → (X → 𝓤 ̇ )
 γ (g , e) = r g

 φγ : ∀ m → φ (γ m) ≡ m
 φγ (g , e) = to-Σ-≡
               (dfunext fe' (λ y → eqtoid ua (s (r g) y) (g y) (κ g y , e y)) ,
                Π-is-prop feuu (λ y → being-equiv-is-prop'' feuu (κ g y)) _ e)

 γφ : ∀ f → γ (φ f) ≡ f
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → (Y → 𝓤 ̇ )
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-is-embedding
                     (λ g → Π-is-prop feuu (λ y → being-equiv-is-prop'' feuu (κ g y)))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = ∘-is-embedding φ-is-embedding ψ-is-embedding

\end{code}

Added 23rd Nov 2018, version of 21st January 2017:

The notion of flabbiness used in topos theory is defined with
truncated Σ, that is, ∃. We refer to the notion defined with Σ as
algebraic flabbiness.

\begin{code}

aflabby : 𝓦 ̇ → (𝓤 : Universe) → 𝓦 ⊔ 𝓤 ⁺ ̇
aflabby D 𝓤 = (P : 𝓤 ̇ ) → is-prop P → (f : P → D) → Σ d ꞉ D , ((p : P) → d ≡ f p)

aflabby-pointed : (D : 𝓦 ̇ ) → aflabby D 𝓤 → D
aflabby-pointed D φ = pr₁ (φ 𝟘 𝟘-is-prop unique-from-𝟘)


ainjective-types-are-aflabby : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → aflabby D 𝓤
ainjective-types-are-aflabby {𝓦} {𝓤} {𝓥} D i P isp f =
  pr₁ (i (λ p → ⋆) (prop-embedding P isp 𝓥) f) ⋆ ,
  pr₂ (i (λ p → ⋆) (prop-embedding P isp 𝓥) f)

aflabby-types-are-ainjective : (D : 𝓦 ̇ ) → aflabby D (𝓤 ⊔ 𝓥) → ainjective-type D 𝓤 𝓥
aflabby-types-are-ainjective D φ {X} {Y} j e f = f' , p
 where
  f' : Y → D
  f' y = pr₁ (φ (fiber j y) (e y) (f ∘ pr₁))

  p : (x : X) → f' (j x) ≡ f x
  p x = q (x , refl)
   where
    q : (w : fiber j (j x)) → f' (j x) ≡ f (pr₁ w)
    q = pr₂ (φ (fiber j (j x)) (e (j x)) (f ∘ pr₁))

\end{code}

Because Ω is a retract of 𝓤 via propositional truncation, it is
injective. But we can prove this directly without assumming
propositional truncations, and propositional and functional
extensionality (which give to propositional univalence) are enough,
whereas the injectivity of the universe requires full univalence.

\begin{code}

Ω-aflabby : propext (𝓤 ⊔ 𝓥) → aflabby (Ω (𝓤 ⊔ 𝓥)) 𝓤
Ω-aflabby {𝓤} {𝓥} pe P i f = (Q , j) , c
 where
  Q : 𝓤 ⊔ 𝓥 ̇
  Q = (p : P) → f p holds
  j : is-prop Q
  j = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥)) (λ p → holds-is-prop (f p))
  c : (p : P) → Q , j ≡ f p
  c p = to-Σ-≡ (t , being-prop-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) _ _)
   where
      g : Q → f p holds
      g q = q p

      h : f p holds → Q
      h r p' = transport (λ - → f - holds) (i p p') r

      t : Q ≡ f p holds
      t = pe j (holds-is-prop (f p)) g h

Ω-ainjective : propext (𝓤 ⊔ 𝓥) → ainjective-type (Ω (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Ω-ainjective {𝓤} {𝓥} pe = aflabby-types-are-ainjective (Ω (𝓤 ⊔ 𝓥)) (Ω-aflabby {𝓤 ⊔ 𝓥} {𝓤} pe)

\end{code}

Added 6th Feb 2019.

The injectivity of all types is logically equivalent to excluded middle
(even though excluded middle is a proposition but injectivity is data):

\begin{code}

EM-gives-pointed-types-aflabby : (D : 𝓦 ̇ ) → EM 𝓤 → D → aflabby D 𝓤
EM-gives-pointed-types-aflabby {𝓦} {𝓤} D em d P i f = h (em P i)
 where
  h : P + ¬ P → Σ d ꞉ D , ((p : P) → d ≡ f p)
  h (inl p) = f p , (λ q → ap f (i p q))
  h (inr n) = d , (λ p → 𝟘-elim (n p))

aflabby-EM-lemma : (P : 𝓦 ̇ ) → is-prop P → aflabby ((P + ¬ P) + 𝟙) 𝓦 → P + ¬ P
aflabby-EM-lemma {𝓦} P i φ = γ
 where
  D = (P + ¬ P) + 𝟙 {𝓦}

  f : P + ¬ P → D
  f (inl p) = inl (inl p)
  f (inr n) = inl (inr n)

  d : D
  d = pr₁ (φ (P + ¬ P) (decidability-of-prop-is-prop (fe 𝓦 𝓤₀) i) f)

  κ : (z : P + ¬ P) → d ≡ f z
  κ = pr₂ (φ (P + ¬ P) (decidability-of-prop-is-prop (fe 𝓦 𝓤₀) i) f)

  a : (p : P) → d ≡ inl (inl p)
  a p = κ (inl p)

  b : (n : ¬ P) → d ≡ inl (inr n)
  b n = κ (inr n)

  δ : (d' : D) → d ≡ d' → P + ¬ P
  δ (inl (inl p)) r = inl p
  δ (inl (inr n)) r = inr n
  δ (inr ⋆)       r = 𝟘-elim (m n)
   where
    n : ¬ P
    n p = 𝟘-elim (+disjoint ((a p)⁻¹ ∙ r))

    m : ¬¬ P
    m n = 𝟘-elim (+disjoint ((b n)⁻¹ ∙ r))

  γ : P + ¬ P
  γ = δ d refl

pointed-types-aflabby-gives-EM : ((D : 𝓦 ̇ ) → D → aflabby D 𝓦) → EM 𝓦
pointed-types-aflabby-gives-EM {𝓦} α P i = aflabby-EM-lemma P i (α ((P + ¬ P) + 𝟙) (inr ⋆))

EM-gives-pointed-types-ainjective : EM (𝓤 ⊔ 𝓥) → (D : 𝓦 ̇ ) → D → ainjective-type D 𝓤 𝓥
EM-gives-pointed-types-ainjective em D d = aflabby-types-are-ainjective D
                                            (EM-gives-pointed-types-aflabby D em d)

pointed-types-ainjective-gives-EM : ((D : 𝓦 ̇ ) → D → ainjective-type D 𝓦 𝓤) → EM 𝓦
pointed-types-ainjective-gives-EM α = pointed-types-aflabby-gives-EM
                                       (λ D d → ainjective-types-are-aflabby D (α D d))

\end{code}

End of 6th Feb addition. But this is not the end of the story. What
happens with anonymous injectivity (defined and studied below)?

TODO. Show that the extension induced by aflabbiness is an embedding of
function types.

Without resizing axioms, we have the following resizing construction:

\begin{code}

ainjective-resizing₁ : (D : 𝓦 ̇ ) → ainjective-type D (𝓤 ⊔ 𝓣) 𝓥 → ainjective-type D 𝓤 𝓣
ainjective-resizing₁ D i j e f = aflabby-types-are-ainjective D
                                  (ainjective-types-are-aflabby D i) j e f

\end{code}

In particular:

\begin{code}

ainjective-resizing₂ : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤 𝓤
ainjective-resizing₂ = ainjective-resizing₁

ainjective-resizing₃ : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤₀ 𝓤
ainjective-resizing₃ = ainjective-resizing₁

\end{code}

Added 24th January 2019.

With propositional resizing, as soon as D is aflabby with respect to
some universe, it is aflabby with respect to all universes:

\begin{code}

aflabbiness-resizing : (D : 𝓦 ̇ ) (𝓤 𝓥 : Universe)
                     → propositional-resizing 𝓤 𝓥
                     → aflabby D 𝓥 → aflabby D 𝓤
aflabbiness-resizing D 𝓤 𝓥 R φ P i f = d , h
 where
  Q : 𝓥 ̇
  Q = resize R P i

  j : is-prop Q
  j = resize-is-prop R P i

  α : P → Q
  α = to-resize R P i

  β : Q → P
  β = from-resize R P i

  d : D
  d = pr₁ (φ Q j (f ∘ β))

  k : (q : Q) → d ≡ f (β q)
  k = pr₂ (φ Q j (f ∘ β))

  h : (p : P) → d ≡ f p
  h p = d           ≡⟨ k (α p) ⟩
        f (β (α p)) ≡⟨ ap f (i (β (α p)) p) ⟩
        f p         ∎

\end{code}

And from this it follows that the injectivity of a type with respect
to two given universes implies its injectivity with respect to all
universes:

\begin{code}

ainjective-resizing : ∀ {𝓤 𝓥 𝓤' 𝓥' 𝓦}
                    → propositional-resizing (𝓤' ⊔ 𝓥') 𝓤
                    → (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → ainjective-type D 𝓤' 𝓥'
ainjective-resizing {𝓤} {𝓥} {𝓤'} {𝓥'} {𝓦} R D i j e f =
  aflabby-types-are-ainjective D
   (aflabbiness-resizing D (𝓤' ⊔ 𝓥') 𝓤 R (ainjective-types-are-aflabby D i)) j e f

\end{code}

As an application of this and of injectivity of universes, we have
that any universe is a retract of any larger universe.

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, https://arxiv.org/abs/1507.03634).

\begin{code}

universe-retract : Univalence
                 → Propositional-resizing
                 → (𝓤 𝓥 : Universe)
                 → Σ ρ ꞉ retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ ), is-embedding (section ρ)
universe-retract ua R 𝓤 𝓥 = ρ , (Lift-is-embedding ua)
 where
  a : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
  a = universes-are-ainjective-Π {𝓤} {𝓤} (ua 𝓤)

  b : is-embedding (Lift 𝓥)
    → ainjective-type (𝓤 ̇ ) (𝓤 ⁺) ((𝓤 ⊔ 𝓥 )⁺)
    → retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ )
  b = embedding-retract (𝓤 ̇ ) (𝓤 ⊔ 𝓥 ̇ ) (Lift 𝓥)

  ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ )
  ρ = b (Lift-is-embedding ua) (ainjective-resizing R (𝓤 ̇ ) a)

\end{code}

And unfolding of the above construction is in the module UF-Size.

Added 25th January 2019. From this we get the following
characterization of injective types (as a logical equivalence, not a
type equivalence), which can be read as saying that the injective
types in a universe 𝓤 are precisely the retracts of exponential powers
of 𝓤.

\begin{code}

ainjective-characterization : is-univalent 𝓤
                            → propositional-resizing (𝓤 ⁺) 𝓤 → (D : 𝓤 ̇ )
                            → ainjective-type D 𝓤 𝓤 ⇔ (Σ X ꞉ 𝓤 ̇ , retract D of (X → 𝓤 ̇ ))
ainjective-characterization {𝓤} ua R D = a , b
 where
  a : ainjective-type D 𝓤 𝓤 → Σ X ꞉ 𝓤 ̇ , retract D of (X → 𝓤 ̇ )
  a i = D , d
   where
    c : ainjective-type D 𝓤 (𝓤 ⁺)
    c = ainjective-resizing R D i

    d : retract D of (D → 𝓤 ̇ )
    d = ainjective-is-retract-of-power-of-universe D ua c

  b : (Σ X ꞉ 𝓤 ̇ , retract D of (X → 𝓤 ̇ )) → ainjective-type D 𝓤 𝓤
  b (X , r) = d
   where
    c : ainjective-type (X → 𝓤 ̇ ) 𝓤 𝓤
    c = power-of-ainjective (universes-are-ainjective-Σ ua)

    d : ainjective-type D 𝓤 𝓤
    d = retract-of-ainjective D (X → 𝓤 ̇ ) c r

\end{code}

Added 23rd January 2019:

\begin{code}

module ainjectivity-of-Lifting (𝓤 : Universe) where

 open import Lifting 𝓤 public
 open import LiftingAlgebras 𝓤
 open import LiftingEmbeddingViaSIP 𝓤 public

 open import UF-UA-FunExt

\end{code}

The underlying types of algebras of the Lifting monad are aflabby, and
hence injective, and so in particular the underlying objects of the
free 𝓛-algebras are injective.

\begin{code}

 𝓛-alg-aflabby : propext 𝓤 → funext 𝓤 𝓤 → funext 𝓤 𝓥
               → {A : 𝓥 ̇ } → 𝓛-alg A → aflabby A 𝓤
 𝓛-alg-aflabby pe fe fe' (∐ , κ , ι) P i f = ∐ i f , γ
  where
   γ : (p : P) → ∐ i f ≡ f p
   γ p = 𝓛-alg-Law₀-gives₀' pe fe fe' ∐ κ P i f p

 𝓛-alg-ainjective : propext 𝓤
                  → funext 𝓤 𝓤
                  → funext 𝓤 𝓥
                  → (A : 𝓥 ̇ ) → 𝓛-alg A → ainjective-type A 𝓤 𝓤
 𝓛-alg-ainjective pe fe fe' A α = aflabby-types-are-ainjective A
                                    (𝓛-alg-aflabby pe fe fe' α)

 free-𝓛-algebra-ainjective : is-univalent 𝓤
                           → funext 𝓤 (𝓤 ⁺)
                           → (X : 𝓤 ̇ ) → ainjective-type (𝓛 X) 𝓤 𝓤
 free-𝓛-algebra-ainjective ua fe X = 𝓛-alg-ainjective
                                       (univalence-gives-propext ua)
                                       (univalence-gives-funext ua)
                                       fe
                                       (𝓛 X)
                                       (𝓛-algebra-gives-alg (free-𝓛-algebra ua X))
\end{code}

Because the unit of the Lifting monad is an embedding, it follows that
injective types are retracts of underlying objects of free algebras:

\begin{code}

 ainjective-is-retract-of-free-𝓛-algebra : (D : 𝓤 ̇ )
                                         → is-univalent 𝓤
                                         → ainjective-type D 𝓤 (𝓤 ⁺)
                                         → retract D of (𝓛 D)
 ainjective-is-retract-of-free-𝓛-algebra D ua = embedding-retract D (𝓛 D) η
                                                  (η-is-embedding' 𝓤 D ua
                                                     (univalence-gives-funext ua))
\end{code}

With propositional resizing, the injective types are precisely the
retracts of the underlying objects of free algebras of the Lifting
monad:

\begin{code}

 ainjectives-in-terms-of-free-𝓛-algebras : is-univalent 𝓤
                                         → funext 𝓤 (𝓤 ⁺)
                                         → propositional-resizing (𝓤 ⁺) 𝓤
                                         → (D : 𝓤 ̇ ) → ainjective-type D 𝓤 𝓤
                                                      ⇔ (Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X))
 ainjectives-in-terms-of-free-𝓛-algebras ua fe R D = a , b
  where
   a : ainjective-type D 𝓤 𝓤 → Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X)
   a i = D , ainjective-is-retract-of-free-𝓛-algebra D ua (ainjective-resizing R D i)

   b : (Σ X ꞉ 𝓤 ̇ , retract D of (𝓛 X)) → ainjective-type D 𝓤 𝓤
   b (X , r) = retract-of-ainjective D (𝓛 X) (free-𝓛-algebra-ainjective ua fe X) r

\end{code}

Added 21st January 2019. We now consider injectivity as property
rather than data.

\begin{code}

module injective (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 injective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
 injective-type D 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (j : X → Y) → is-embedding j
                       → (f : X → D) → ∃ g ꞉ (Y → D), g ∘ j ∼ f


 injectivity-is-prop : (D : 𝓦 ̇ ) (𝓤 𝓥 : Universe)
                     → is-prop (injective-type D 𝓤 𝓥)
 injectivity-is-prop {𝓦} D 𝓤 𝓥 = Π-is-prop' (fe (𝓤 ⁺) (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦))
                                        (λ X → Π-is-prop' (fe (𝓥 ⁺) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                          (λ Y → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                            (λ j → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                              (λ e → Π-is-prop (fe (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                                (λ f → ∥∥-is-prop)))))


 ainjective-gives-injective : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → injective-type D 𝓤 𝓥
 ainjective-gives-injective D i j e f = ∣ i j e f ∣

 ∥ainjective∥-gives-injective : (D : 𝓦 ̇ )
                              → ∥ ainjective-type D 𝓤 𝓥 ∥
                              → injective-type D 𝓤 𝓥
 ∥ainjective∥-gives-injective {𝓦} {𝓤} {𝓥} D = ∥∥-rec (injectivity-is-prop D 𝓤 𝓥)
                                                      (ainjective-gives-injective D)

 embedding-∥retract∥ : (D : 𝓦 ̇ ) (Y : 𝓥 ̇ ) (j : D → Y)
                     → is-embedding j
                     → injective-type D 𝓦 𝓥
                     → ∥ retract D of Y ∥
 embedding-∥retract∥ D Y j e i = ∥∥-functor φ a
  where
   a : ∃ r ꞉ (Y → D), r ∘ j ∼ id
   a = i j e id

   φ : (Σ r ꞉ (Y → D), r ∘ j ∼ id) → Σ r ꞉ (Y → D) , Σ s ꞉ (D → Y), r ∘ s ∼ id
   φ (r , p) = r , j , p

 retract-of-injective : (D' : 𝓤 ̇ ) (D : 𝓥 ̇ )
                       → injective-type D 𝓦 𝓣
                       → retract D' of D
                       → injective-type D' 𝓦 𝓣
 retract-of-injective D' D i (r , (s , rs)) {X} {Y} j e f = γ
  where
   i' : ∃ f' ꞉ (Y → D), f' ∘ j ∼ s ∘ f
   i' = i j e (s ∘ f)

   φ : (Σ f' ꞉ (Y → D) , f' ∘ j ∼ s ∘ f) → Σ f'' ꞉ (Y → D'), f'' ∘ j ∼ f
   φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))

   γ : ∃ f'' ꞉ (Y → D') , f'' ∘ j ∼ f
   γ = ∥∥-functor φ i'

\end{code}

The given proof of power-of-injective doesn't adapt to the following,
so we need a new proof, but hence also new universe assumptions.

\begin{code}

 power-of-injective : {A : 𝓣 ̇ } {D : 𝓣 ⊔ 𝓦 ̇ }
                     → injective-type D       (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
                     → injective-type (A → D) (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
 power-of-injective {𝓣} {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = γ
  where
   g : X × A → D
   g = uncurry f

   k : X × A → Y × A
   k (x , a) = j x , a

   c : is-embedding k
   c = pair-fun-is-embedding j (λ x a → a) e (λ x → id-is-embedding)

   ψ : ∃ g' ꞉ (Y × A → D), g' ∘ k ∼ g
   ψ = i k c g

   φ : (Σ g' ꞉ (Y × A → D), g' ∘ k ∼ g) → (Σ f' ꞉ (Y → (A → D)), f' ∘ j ∼ f)
   φ (g' , h) = curry g' , (λ x → dfunext (fe 𝓣 (𝓣 ⊔ 𝓦)) (λ a → h (x , a)))

   γ : ∃ f' ꞉ (Y → (A → D)), f' ∘ j ∼ f
   γ = ∥∥-functor φ ψ

 injective-∥retract∥-of-power-of-universe : (D : 𝓤 ̇ ) → is-univalent 𝓤
                                         → injective-type D 𝓤 (𝓤 ⁺)
                                         → ∥ retract D of (D → 𝓤 ̇ ) ∥
 injective-∥retract∥-of-power-of-universe {𝓤} D ua = embedding-∥retract∥ D (D → 𝓤 ̇ ) Id
                                                      (UA-Id-embedding ua fe)

 injective-gives-∥ainjective∥ : is-univalent 𝓤
                              → (D : 𝓤 ̇ )
                              → injective-type D 𝓤 (𝓤 ⁺)
                              → ∥ ainjective-type D 𝓤 𝓤 ∥
 injective-gives-∥ainjective∥ {𝓤} ua D i = γ
  where
   φ : retract D of (D → 𝓤 ̇ ) → ainjective-type D 𝓤 𝓤
   φ = retract-of-ainjective D (D → 𝓤 ̇ )
         (power-of-ainjective (universes-are-ainjective-Π ua))

   γ : ∥ ainjective-type D 𝓤 𝓤 ∥
   γ = ∥∥-functor φ (injective-∥retract∥-of-power-of-universe D ua i)

\end{code}

So, in summary, regarding the relationship between winjectivity and
truncated injectivity, so far we know that

  ∥ ainjective-type D 𝓤 𝓥 ∥ → injective-type D 𝓤 𝓥

and

  injective-type D 𝓤 (𝓤 ⁺) → ∥ ainjective-type D 𝓤 𝓤 ∥,

and hence, using propositional resizing, we get the following
characterization of a particular case of winjectivity in terms of
injectivity.

\begin{code}

 injectivity-in-terms-of-ainjectivity' : is-univalent 𝓤
                                      → propositional-resizing (𝓤 ⁺) 𝓤
                                      → (D : 𝓤  ̇ ) → injective-type D 𝓤 (𝓤 ⁺)
                                                   ⇔ ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥
 injectivity-in-terms-of-ainjectivity' {𝓤} ua R D = a , b
  where
   a : injective-type D 𝓤 (𝓤 ⁺) → ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥
   a = ∥∥-functor (ainjective-resizing R D) ∘ injective-gives-∥ainjective∥ ua D

   b : ∥ ainjective-type D 𝓤 (𝓤 ⁺) ∥ → injective-type D 𝓤 (𝓤 ⁺)
   b = ∥ainjective∥-gives-injective D

\end{code}

What we really would like to have for D : 𝓤 is

  injective-type D 𝓤 𝓤 ⇔ ∥ ainjective-type D 𝓤 𝓤 ∥,

and, perhaps, more generally, also

  injective-type D 𝓥 𝓦 ⇔ ∥ ainjective-type D 𝓤 𝓦 ∥.

This is now answered 8th Feb (see below).

Added 7th Feb 2019. (Preliminary answer.)

However, with Ω₀-resizing, for a ⋆set⋆ D : 𝓤 we do have

  injective-type D 𝓤 𝓤 ⇔ ∥ ainjective-type D 𝓤 𝓤 ∥,

The reason is that the embedding Id : D → (D → 𝓤) factors through
(D → Ω₀).

\begin{code}

 set-injectivity-in-terms-of-ainjectivity : Ω-resizing₀ 𝓤
                                          → PropExt
                                          → (D  : 𝓤 ̇ ) (i  : is-set D)
                                          → injective-type D 𝓤 𝓤
                                          ⇔ ∥ ainjective-type D 𝓤 𝓤 ∥
 set-injectivity-in-terms-of-ainjectivity {𝓤} (Ω₀ , e₀) pe D i = γ , ∥ainjective∥-gives-injective D
  where
   down-≃ : (D → Ω 𝓤) ≃ (D → Ω₀)
   down-≃ = →cong' (fe 𝓤 𝓤₀) (fe 𝓤 (𝓤 ⁺)) (≃-sym e₀)

   down : (D → Ω 𝓤) → (D → Ω₀)
   down = ⌜ down-≃ ⌝

   down-is-embedding : is-embedding down
   down-is-embedding = equivs-are-embeddings down (⌜⌝-is-equiv down-≃)

   Id-set₀ : D → (D → Ω₀)
   Id-set₀ = down ∘ Id-set i

   Id-set₀-is-embedding : is-embedding Id-set₀
   Id-set₀-is-embedding = ∘-is-embedding
                           (Id-set-is-embedding (fe 𝓤 (𝓤 ⁺)) (pe 𝓤) i)
                           down-is-embedding

   injective-set-retract-of-powerset : injective-type D 𝓤 𝓤 → ∥ retract D of (D → Ω₀) ∥
   injective-set-retract-of-powerset = embedding-∥retract∥ D (D → Ω₀) Id-set₀
                                         Id-set₀-is-embedding

   Ω₀-injective : ainjective-type Ω₀ 𝓤 𝓤
   Ω₀-injective = equiv-to-ainjective Ω₀ (Ω 𝓤) (Ω-ainjective (pe 𝓤)) e₀

   γ : injective-type D 𝓤 𝓤 → ∥ ainjective-type D 𝓤 𝓤 ∥
   γ j = ∥∥-functor φ (injective-set-retract-of-powerset j)
    where
     φ : retract D of (D → Ω₀) → ainjective-type D 𝓤 𝓤
     φ = retract-of-ainjective D (D → Ω₀) (power-of-ainjective Ω₀-injective)

\end{code}

Added 8th Feb. Solves a problem formulated above.

\begin{code}

 injectivity-in-terms-of-ainjectivity : Ω-resizing 𝓤
                                      → is-univalent 𝓤
                                      → (D  : 𝓤 ̇ ) → injective-type D 𝓤 𝓤
                                                   ⇔ ∥ ainjective-type D 𝓤 𝓤 ∥
 injectivity-in-terms-of-ainjectivity {𝓤} ω₀ ua D = γ , ∥ainjective∥-gives-injective D
  where
   open import LiftingSize 𝓤
   open ainjectivity-of-Lifting 𝓤

   L : 𝓤 ̇
   L = pr₁ (𝓛-resizing ω₀ D)

   e : 𝓛 D ≃ L
   e = ≃-sym (pr₂ (𝓛-resizing ω₀ D))

   down : 𝓛 D → L
   down = ⌜ e ⌝

   down-is-embedding : is-embedding down
   down-is-embedding = equivs-are-embeddings down (⌜⌝-is-equiv e)

   ε : D → L
   ε = down ∘ η

   ε-is-embedding : is-embedding ε
   ε-is-embedding = ∘-is-embedding (η-is-embedding' 𝓤 D ua (fe 𝓤 𝓤)) down-is-embedding

   injective-retract-of-L : injective-type D 𝓤 𝓤 → ∥ retract D of L ∥
   injective-retract-of-L = embedding-∥retract∥ D L ε ε-is-embedding

   L-injective : ainjective-type L 𝓤 𝓤
   L-injective = equiv-to-ainjective L (𝓛 D)
                   (free-𝓛-algebra-ainjective ua (fe 𝓤 (𝓤 ⁺)) D) (≃-sym e)

   γ : injective-type D 𝓤 𝓤 → ∥ ainjective-type D 𝓤 𝓤 ∥
   γ j = ∥∥-functor φ (injective-retract-of-L j)
    where
     φ : retract D of L → ainjective-type D 𝓤 𝓤
     φ = retract-of-ainjective D L L-injective

\end{code}

Here are some corollaries:

\begin{code}

 injective-resizing : is-univalent 𝓤 → Ω-resizing 𝓤
                    → (D : 𝓤 ̇ )
                    → injective-type D 𝓤 𝓤
                    → (𝓥 𝓦 : Universe) → propositional-resizing (𝓥 ⊔ 𝓦) 𝓤 → injective-type D 𝓥 𝓦
 injective-resizing {𝓤} ua ω₀ D i 𝓥 𝓦 R = c
  where
   a : ∥ ainjective-type D 𝓤 𝓤 ∥
   a = pr₁ (injectivity-in-terms-of-ainjectivity ω₀ ua D) i

   b : ∥ ainjective-type D 𝓥 𝓦 ∥
   b = ∥∥-functor (ainjective-resizing R D) a

   c : injective-type D 𝓥 𝓦
   c = ∥ainjective∥-gives-injective D b

 EM-gives-pointed-types-injective : EM 𝓤 → (D : 𝓤 ̇ ) → D → injective-type D 𝓤 𝓤
 EM-gives-pointed-types-injective {𝓤} em D d = ainjective-gives-injective D
                                                  (EM-gives-pointed-types-ainjective em D d)

 pointed-types-injective-gives-EM : Ω-resizing 𝓤
                                  → is-univalent 𝓤
                                  → ((D : 𝓤 ̇ ) → D → injective-type D 𝓤 𝓤)
                                  → EM 𝓤
 pointed-types-injective-gives-EM {𝓤} ω ua β P i = e
  where
   a : injective-type ((P + ¬ P) + 𝟙) 𝓤 𝓤
   a = β ((P + ¬ P) + 𝟙) (inr ⋆)

   b : ∥ ainjective-type ((P + ¬ P) + 𝟙) 𝓤 𝓤 ∥
   b = pr₁ (injectivity-in-terms-of-ainjectivity ω ua ((P + ¬ P) + 𝟙)) a

   c : ∥ aflabby ((P + ¬ P) + 𝟙) 𝓤 ∥
   c = ∥∥-functor (ainjective-types-are-aflabby ((P + ¬ P) + 𝟙)) b

   d : ∥ P + ¬ P ∥
   d = ∥∥-functor (aflabby-EM-lemma P i) c

   e : P + ¬ P
   e =  ∥∥-rec (decidability-of-prop-is-prop (fe 𝓤 𝓤₀) i) id d

\end{code}

Fixities:

\begin{code}

infixr 4 _≾_

\end{code}
