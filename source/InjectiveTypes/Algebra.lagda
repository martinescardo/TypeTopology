Martin Escardo, 22nd October 2024 - 22 May 2025

This file is work in progress and aims to eventually subsume the file
gist.InjectivesVersusAlgebras (at which point that file will be deleted).

We give conditions on algebraic injective structure on a type so that
it coincides with the algebraic structure for the partial-map
classifier (aka lifting) monad 𝓛 on types.

We call these conditions "associativity" and "pullback naturality".

Associativity says that an extension (f|j)|k of an extension f|j is
the extension f|(k∘j) along the composition of the embeddings j and k,
as in the following commutative diagram.


                   j         k
              X ──────→ Y ──────→ Z
               ╲        │        ╱
                ╲       │       ╱
             f   ╲      │ f|j  ╱ (f|j)|k = f(k∘j
                  ╲     │     ╱
                   ╲    │    ╱
                    ╲   │   ╱
                     ➘  ↓  ↙
                        D

Pullback naturality is expressed by the following diagram, where the
square is a pullback and j (and hence k) is an embedding.

                   k
              A ──────→ B
              │ ⌟       │
           g  │         │ h
              │         │
              ↓    j    ↓
              X ──────→ Y
               ╲        │
                ╲       │
             f   ╲      │ f|j ∘ h = (f ∘ g) | k
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D

It actually suffices to consider pullbacks of the form


        fiber j y ────→ 𝟙
              │ ⌟       │
              │         │ y
              │         │
              ↓    j    ↓
              X ──────→ Y

This is a sense in which extensions are pointwise.

One may wonder whether it is reasonable to consider naturality with
respect to all commutative squares

                   k
              A ──────→ B
              │         │
           g  │         │ h
              │         │
              ↓    j    ↓
              X ──────→ Y

where j and k are embeddings, but which are not necessarily
pullbacks. However, a counter-example is the commutative square


              𝟘 ──────→ 𝟙
              │         │
              │         │
              │         │
              ↓         ↓
              𝟙 ──────→ 𝟙

Now, an algebra α : 𝓛 D → D of the lifting monad amounts flabbiness
structure plus an associativity law on this structure. Via the
canonical correspondence between algebraic injective structure and
algebraic flabby structure, the above associativity condition
corresponds to the associativity law for 𝓛-algebras (which justifies
our terminology in the case of injectivity). In terms of flabbinnes,
this says that if we have a situation

            P × Q ────→ 𝟙
               ╲        │
                ╲       │
             f   ╲      │
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D

where P and Q propositions, so that also P × Q is a proposition, then
we can

 1. extend f at once, or
 2. extend f in its first variable and then in its second variable,

and these two processes give the same result.

As for pullback naturality, it is given automatically by the canonical
construction of algebraic injectivity data from algebraic flabiness
data.

If we define homomorphisms h : D → E of algebraic injectives in the
obvious way, namely, that for any f : X → D and j : X ↪ Y we have that

    h ∘ f ∣ j = (h ∘ f) ∣ j

as (partially) illustrated by the (incomplete, due to typographical
reasons) diagram

                   j
              X ───────→ Y
               ╲       ╱
                ╲     ╱
               f ╲   ╱ f/j
                  ➘ ↙
                   D
                   │
                   │ h
                   ↓
                   E

then injective homomorphisms correspond to 𝓛-homomorphisms.

When we restrict to types that are sets, we get that the category of
associative, pullback-natural algebraically injective objects is
isomorphic to the category of 𝓛-algebras.

This result holds for the objects of any 1-topos, due to our
constructive reasoning in a restricted type theory.

However, at the moment we don't have a result for ∞-toposes, because,
although the associativity, pullback naturality and the algebra
equations are all property for sets, they are data, and we have proved
only a logical equivalence of associativity + pullback-naturality and
the 𝓛-algebra equations, rather than a full type equivalence (whose
possibility we are currently investigating).

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt

module InjectiveTypes.Algebra
        (fe : FunExt)
       where

fe' : Fun-Ext
fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Blackboard fe hiding (ηΠ ; ηΣ)
open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Pullback
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Univalence
open import Lifting.Algebras

\end{code}

Definition of algebraic injective homomorphisms.

\begin{code}

module algebraic-injective-homomorphisms
        {𝓤 𝓦 𝓣 : Universe}
        (D : 𝓦 ̇ )
        (E : 𝓣 ̇ )
        (D-ainj : ainjective-type D 𝓤 𝓤)
        (E-ainj : ainjective-type E 𝓤 𝓤)
       where

 _∣ᴰ_ : {X Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
 f ∣ᴰ 𝕛 = extension' D-ainj 𝕛 f

 _∣ᴱ_ : {X Y : 𝓤 ̇ } → (X → E) → (X ↪ Y) → (Y → E)
 g ∣ᴱ 𝕛 = extension' E-ainj 𝕛 g

 is-hom : (D → E) → (𝓤 ⁺) ⊔ 𝓦 ⊔ 𝓣 ̇
 is-hom h = {X Y : 𝓤 ̇ } (f : X → D) (𝕛 : X ↪ Y)
          → h ∘ f ∣ᴰ 𝕛 ∼ (h ∘ f) ∣ᴱ 𝕛

\end{code}

Definitions of associativity and pullback naturality.

\begin{code}

module _
        {𝓤 𝓦 : Universe}
        (D : 𝓦 ̇ )
        (D-ainj : ainjective-type D 𝓤 𝓤)
       where

 private
  _∣_ : {X Y : 𝓤 ̇ } → (X → D) → (X ↪ Y) → (Y → D)
  f ∣ 𝕛 = extension' D-ainj 𝕛 f

 associativity : 𝓦 ⊔ 𝓤 ⁺ ̇
 associativity = {X Y Z : 𝓤 ̇ } (f : X → D) (𝕛 : X ↪ Y) (𝕜 : Y ↪ Z)
               → f ∣ (𝕜 ∘↪ 𝕛) ∼ (f ∣ 𝕛) ∣ 𝕜

\end{code}

For the following definition, we consider the standard pullback

                   pb₂
    pullback j h ─────→ B
              │ ⌟       │
          pb₁ │         │ h
              │         │
              ↓     j   ↓
              X ──────→ Y

where pullback j h := Σ (x , y) ꞉ X × B , j x ＝ h y and pb₁ and pb₂
are the projections, rather than an abstract pullback, for simplicity,
so that the above naturality condition becomes

                   pb₂
    pullback j h ─────→ B
              │ ⌟       │
          pb₁ │         │ h
              │         │
              ↓     j   ↓
              X ──────→ Y
               ╲        │
                ╲       │
             f   ╲      │ (f | j) ∘ h = (f ∘ pb₁) | pb₂
                  ╲     │
                   ╲    │
                    ╲   │
                     ➘  ↓
                        D

\begin{code}

 module _
         {X Y B : 𝓤 ̇ }
         (f : X → D)
         (𝕛 : X ↪ Y)
         (h : B → Y)
        where

  open pullback ⌊ 𝕛 ⌋ h

  𝕡𝕓₂ : pullback ↪ B
  𝕡𝕓₂ = pb₂ , pb₂-is-embedding ⌊ 𝕛 ⌋-is-embedding

  pullback-naturality : 𝓤 ⊔ 𝓦 ̇
  pullback-naturality = (f ∣ 𝕛) ∘ h ＝ (f ∘ pb₁) ∣ 𝕡𝕓₂

 Pullback-Naturality : (𝓤 ⁺) ⊔ 𝓦 ̇
 Pullback-Naturality = {X Y B : 𝓤 ̇ }
                       (f : X → D)
                       (𝕛 : X ↪ Y)
                       (h : B → Y)
                     → pullback-naturality f 𝕛 h

\end{code}

\begin{code}

aainjective-structure : (𝓤 : Universe) → 𝓦 ̇ → (𝓤 ⁺) ⊔ 𝓦 ̇
aainjective-structure 𝓤 D =
 Σ D-ainj ꞉ ainjective-type D 𝓤 𝓤 , associativity D D-ainj

module _
        {𝓤 𝓦 : Universe}
        (D : 𝓦 ̇ )
       where

 aainjective-structure₁ : aainjective-structure 𝓤 D → ainjective-type D 𝓤 𝓤
 aainjective-structure₁ = pr₁

 aainjective-structure₂ : (s : aainjective-structure 𝓤 D)
                        → associativity D (aainjective-structure₁ s)
 aainjective-structure₂ = pr₂

{-
 associativity-gives-𝓛-alg-structure : aainjective-structure 𝓤 D → 𝓛-alg 𝓤 D
 associativity-gives-𝓛-alg-structure = {!!}

 𝓛-alg-structure-gives-associativity : 𝓛-alg 𝓤 D → aainjective-structure 𝓤 D
 𝓛-alg-structure-gives-associativity = {!!}

 private
  ϕ = associativity-gives-𝓛-alg-structure
  ψ = 𝓛-alg-structure-gives-associativity

 η : (s@(D-ainj , a) : aainjective-structure 𝓤 D)
   → Pullback-Naturality D D-ainj
   → extension (aainjective-structure₁ (ψ (ϕ s)))＝ extension D-ainj
 η = {!!}

 ε : (t : 𝓛-alg 𝓤 D)
   → ∐ 𝓤 (ϕ (ψ t)) ＝ ∐ 𝓤 t
 ε = {!!}
-}

\end{code}

To be continued, following gist.InjectivesVersusAlgebras.
