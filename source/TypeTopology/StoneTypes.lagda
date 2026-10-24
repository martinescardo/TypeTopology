Martin Escardo, 21st October 2026.

We discuss a notion of Stone type and show as an example that ℕ∞ is a
Stone type, assuming ¬ WLPO. We also discuss that this cannot be
proved without such an assumption. The hypothesis ¬ WLPO can be
regarded as a weak continuity principle. It is equivalent to the
doubly negated continuity of every function of ℕ∞ into a discrete
type, by the module TypeTopology.DecidabilityOfNonContinuity.

Our notion of Stone type is a variant of that of [1], and we compare
the two notions below.

[1] Cherubini, Coquand, Geerligs and Moeneclaey, "A Foundation for
    Synthetic Stone Duality", TYPES 2024, LIPIcs 336, pp. 3:1-3:20,
    2025, https://doi.org/10.4230/LIPIcs.TYPES.2024.3.

The clopens of a type X are the 𝟚-valued functions on X, as in the
module TypeTopology.TotallySeparated, and they form a boolean algebra
with the pointwise operations. An ultrafilter of this algebra amounts
to a boolean algebra homomorphism into 𝟚. Each point of X determines a
principal ultrafilter. We say that X is a pre-Stone type if the map
that takes a point to its principal ultrafilter is an equivalence, and
a Stone type if moreover its boolean algebra of clopens is discrete.

We first observe that being principal is a proposition, and that the
map into the ultrafilters is an embedding precisely when X is totally
separated, and we give criteria for a type to be a pre-Stone type and
a Stone type.

We then show that pre-Stone types and Stone types are closed under
retracts, and hence under equivalence, that Stone types are closed
under binary sums and include the finite types, that a ¬¬-stable
proposition is a pre-Stone type and a proposition is a Stone type
precisely when it is decidable, that a product of pre-Stone types
indexed by a proposition is a pre-Stone type, and a Stone type when
the factors are compact and pointed, and that a sum of Stone types
over a Stone type is a Stone type as soon as every clopen of every
fiber is the preimage of a clopen of the sum, which holds for a
constant family and so gives the closure of the Stone types under
binary products.

We show that ℕ∞ is a Stone type if ¬ WLPO holds. The same facts to
establish this are used in the module Ordinals.BrouwerCodesGiveStoneTypes
to show that the compact totally separated interpretation of the
Brouwer ordinal codes gives Stone types, again assuming ¬ WLPO.

We close with three constructive taboos. That every pre-Stone type is
a Stone type gives WEM. That Stone types are closed under Σ gives ¬¬ WLPO,
and the same for the pre-Stone types, so neither of them is closed
under Σ when ¬ WLPO holds. That every compact totally separated type
is a Stone type refutes the existence of a nonprincipal ultrafilter of
the clopens of ℕ∞, so choice refutes it, although it holds in the
model of Blass [2], where excluded middle holds.

[2] Blass, "A model without ultrafilters", Bull. Acad. Polon. Sci. 25,
    1977, pp. 329-331, which extends a model of Feferman, "Some
    applications of the notions of forcing and generic sets",
    Fundamenta Mathematicae 56, 1964, pp. 325-345,
    https://doi.org/10.4064/fm-56-3-325-345.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module TypeTopology.StoneTypes
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe

open import CoNaturals.Type
open import Fin.Bishop
open import Fin.Type hiding (𝟏)
open import MLTT.Two-Properties
 renaming (max𝟚 to infixl 39 _∨_ ;
           min𝟚 to infixl 40 _∧_ ;
           complement to infix 41 ⇁_)
open import NotionsOfDecidability.Complemented
open import Naturals.Order renaming (max to maxℕ)
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.DecidabilityOfNonContinuity fe
open import TypeTopology.GenericConvergentSequenceCompactness fe
open import TypeTopology.MicroTychonoff
open import TypeTopology.TotallySeparated
open import TypeTopology.WeaklyCompactTypes fe' pt
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Retracts-FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

\end{code}

In what follows, we identify complemented subsets with their boolean
valued characteristic functions, and introduce notation to make this
point of view explicit. We first define the type Clopen X of clopens
of a type X and various operations and relations on it.

\begin{code}

Clopen : 𝓤 ̇ → 𝓤 ̇
Clopen X = X → 𝟚

module _ {X : 𝓤 ̇ } where

 infixl 40 _∩_
 infixl 39 _∪_
 infixr 31 _△_
 infix  45 _ϵ_
 infix  35 _∈_
 infix  35 _∉_
 infix  30 _⊆_

 _ϵ_ : X → Clopen X → 𝟚
 x ϵ A = A x

 _∈_ : X → Clopen X → 𝓤₀ ̇
 x ∈ A = x ϵ A ＝ ₁

 _∉_ : X → Clopen X → 𝓤₀ ̇
 x ∉ A = x ϵ A ＝ ₀

 ∈-is-decidable : (x : X) (A : Clopen X) → is-decidable (x ∈ A)
 ∈-is-decidable x A = 𝟚-is-discrete (x ϵ A) ₁

 ∅ : Clopen X
 ∅ = λ x → ₀

 𝟏 : Clopen X
 𝟏 = λ x → ₁

 _∩_ : Clopen X → Clopen X → Clopen X
 A ∩ B = λ x → x ϵ A ∧ x ϵ B

 _∪_ : Clopen X → Clopen X → Clopen X
 A ∪ B = λ x → x ϵ A ∨ x ϵ B

 complement : Clopen X → Clopen X
 complement A = λ x → ⇁ (x ϵ A)

 _⊆_ : Clopen X → Clopen X → 𝓤 ̇
 A ⊆ B = (x : X) → x ∈ A → x ∈ B

\end{code}

Symmetric difference.

\begin{code}

 _△_ : Clopen X → Clopen X → Clopen X
 A △ B = λ x → x ϵ A ⊕ x ϵ B

\end{code}

The preimage of a clopen along a map.

\begin{code}

infix 50 _⁻¹[_]

_⁻¹[_] : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (Y → X) → Clopen X → Clopen Y
f ⁻¹[ A ] = λ y → f y ϵ A

\end{code}

We now define the subtype of X classified by a clopen, whose inclusion
into X is an embedding, as membership is a proposition, together with
the restriction of a clopen of X to such a subtype, which is its
preimage along the inclusion. A clopen restricted to the subtype that
it classifies is the whole of that subtype.

\begin{code}

clopen-subtype : {X : 𝓤 ̇ } → Clopen X → 𝓤 ̇
clopen-subtype {𝓤} {X} A = Σ x ꞉ X , x ∈ A

clopen-subtype-inclusion : {X : 𝓤 ̇ } (A : Clopen X) → clopen-subtype A → X
clopen-subtype-inclusion A = pr₁

clopen-subtype-membership : {X : 𝓤 ̇ } (A : Clopen X) (c : clopen-subtype A)
                          → clopen-subtype-inclusion A c ∈ A
clopen-subtype-membership A = pr₂

clopen-subtype-inclusion-is-embedding
 : {X : 𝓤 ̇ } (A : Clopen X)
 → is-embedding (clopen-subtype-inclusion A)
clopen-subtype-inclusion-is-embedding A
 = pr₁-is-embedding (λ _ → 𝟚-is-set)

\end{code}

The restriction of a clopen to another clopen.

\begin{code}

infix 50 _↾_

_↾_ : {X : 𝓤 ̇ } (B A : Clopen X) → Clopen (clopen-subtype A)
B ↾ A = clopen-subtype-inclusion A ⁻¹[ B ]

self-restriction-is-𝟏 : {X : 𝓤 ̇ } (A : Clopen X) → A ↾ A ＝ 𝟏
self-restriction-is-𝟏 A = dfunext fe (clopen-subtype-membership A)

\end{code}

An ultrafilter of the boolean algebra of clopens of X is a boolean
algebra homomorphism into 𝟚, and hence in particular a clopen of the
clopens of X, so that the notation above applies to it.

\begin{code}

is-ultrafilter : {X : 𝓤 ̇ } → Clopen (Clopen X) → 𝓤 ̇
is-ultrafilter {𝓤} {X} 𝓕 = (∅ ∉ 𝓕)
                         × (𝟏 ∈ 𝓕)
                         × ((A B : Clopen X) → (A ∩ B) ϵ 𝓕 ＝ A ϵ 𝓕 ∧ B ϵ 𝓕)
                         × ((A B : Clopen X) → (A ∪ B) ϵ 𝓕 ＝ A ϵ 𝓕 ∨ B ϵ 𝓕)

being-ultrafilter-is-prop : {X : 𝓤 ̇ } (𝓕 : Clopen (Clopen X))
                          → is-prop (is-ultrafilter 𝓕)
being-ultrafilter-is-prop {𝓤} {X} 𝓕 =
 ×₄-is-prop
  𝟚-is-set
  𝟚-is-set
  (Π₂-is-prop fe (λ A B → 𝟚-is-set))
  (Π₂-is-prop fe (λ A B → 𝟚-is-set))

\end{code}

A clopen of clopens of X is principal at a point of X when it consists
of the clopen neighbourhoods of that point, and principal when it is
principal at some point. We use the names for arbitrary clopens of
clopens, although we apply them only to ultrafilters, and we name the
point that witnesses principality and its property.

\begin{code}

_is-principal-at_ : {X : 𝓤 ̇ } → Clopen (Clopen X) → X → 𝓤 ̇
_is-principal-at_ {𝓤} {X} 𝓕 x = (A : Clopen X) → A ϵ 𝓕 ＝ x ϵ A

is-principal : {X : 𝓤 ̇ } → Clopen (Clopen X) → 𝓤 ̇
is-principal {𝓤} {X} 𝓕 = Σ x ꞉ X , 𝓕 is-principal-at x

is-nonprincipal : {X : 𝓤 ̇ } → Clopen (Clopen X) → 𝓤 ̇
is-nonprincipal 𝓕 = ¬ is-principal 𝓕

principal-point
 : {X : 𝓤 ̇ } {𝓕 : Clopen (Clopen X)} → is-principal 𝓕 → X
principal-point = pr₁

principality
 : {X : 𝓤 ̇ } {𝓕 : Clopen (Clopen X)} (p : is-principal 𝓕)
 → 𝓕 is-principal-at principal-point p
principality = pr₂

\end{code}

Being principal is a proposition precisely when X is totally separated
in the sense of TypeTopology.TotallySeparated, namely that any two
points that share the same clopen neighbourhoods are the same.

\begin{code}

totally-separated-gives-being-principal-is-prop
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → (𝓕 : Clopen (Clopen X))
 → is-prop (is-principal 𝓕)
totally-separated-gives-being-principal-is-prop {𝓤} {X} τ 𝓕 (x , φ) (y , ψ)
 = IV
 where
  I : (x : X) → is-prop ((A : Clopen X) → A ϵ 𝓕 ＝ x ϵ A)
  I x = Π-is-prop fe (λ A → 𝟚-is-set)

  II : (A : Clopen X) → x ϵ A ＝ y ϵ A
  II A = x ϵ A ＝⟨ (φ A)⁻¹ ⟩
         A ϵ 𝓕 ＝⟨ ψ A ⟩
         y ϵ A ∎

  III : x ＝ y
  III = τ II

  IV : (x , φ) ＝ (y , ψ)
  IV = to-subtype-＝ I III

being-principal-is-prop-gives-totally-separated
 : {X : 𝓤 ̇ }
 → ((𝓕 : Clopen (Clopen X)) → is-prop (is-principal 𝓕))
 → is-totally-separated X
being-principal-is-prop-gives-totally-separated {𝓤} {X} σ {x} {y} e
 = II
 where
  𝓕 : Clopen (Clopen X)
  𝓕 = λ A → x ϵ A

  d : 𝓕 is-principal-at x
  d = λ A → refl

  _ : 𝓕 is-principal-at y
  _ = e

  I : (x , d) ＝ (y , e)
  I = σ 𝓕 (x , d) (y , e)

  II : x ＝ y
  II = ap principal-point I

\end{code}

We name the four conditions in the definition of an ultrafilter, and
we show that ultrafilters are monotone and hence upper closed, and
that they preserve complements.

\begin{code}

module ultrafilter-properties
        {X : 𝓤 ̇ }
        (𝓕 : Clopen (Clopen X))
        (i : is-ultrafilter 𝓕)
       where

 preserves-₀ : ∅ ∉ 𝓕
 preserves-₀ = pr₁ i

 preserves-₁ : 𝟏 ∈ 𝓕
 preserves-₁ = pr₁ (pr₂ i)

 preserves-∧ : (A B : Clopen X) → (A ∩ B) ϵ 𝓕 ＝ A ϵ 𝓕 ∧ B ϵ 𝓕
 preserves-∧ = pr₁ (pr₂ (pr₂ i))

 preserves-∨ : (A B : Clopen X) → (A ∪ B) ϵ 𝓕 ＝ A ϵ 𝓕 ∨ B ϵ 𝓕
 preserves-∨ = pr₂ (pr₂ (pr₂ i))

 monotone : {A B : Clopen X} → A ⊆ B → A ϵ 𝓕 ≤ B ϵ 𝓕
 monotone {A} {B} l = IV
  where
   I : A ∩ B ＝ A
   I = dfunext fe (λ x → Lemma[a≤₂b→min𝟚ab＝a] (≤₂-criterion (l x)))

   II : A ϵ 𝓕 ∧ B ϵ 𝓕 ＝ A ϵ 𝓕
   II = A ϵ 𝓕 ∧ B ϵ 𝓕 ＝⟨ (preserves-∧ A B)⁻¹ ⟩
        (A ∩ B) ϵ 𝓕   ＝⟨ ap 𝓕 I ⟩
        A ϵ 𝓕         ∎

   III : A ϵ 𝓕 ∧ B ϵ 𝓕 ≤ B ϵ 𝓕
   III = Lemma[minab≤₂b]

   IV : A ϵ 𝓕 ≤ B ϵ 𝓕
   IV = transport (λ - → - ≤ B ϵ 𝓕) II III

 upper-closed : {A B : Clopen X} → A ⊆ B → A ∈ 𝓕 → B ∈ 𝓕
 upper-closed l = ≤₂-criterion-converse (monotone l)

 preserves-complement : (A : Clopen X) → complement A ϵ 𝓕 ＝ ⇁ (A ϵ 𝓕)
 preserves-complement A = 𝟚-equality-cases III IV
  where
   I : A ϵ 𝓕 ∧ complement A ϵ 𝓕 ＝ ₀
   I = A ϵ 𝓕 ∧ complement A ϵ 𝓕 ＝⟨ (preserves-∧ A (complement A))⁻¹ ⟩
       (A ∩ complement A) ϵ 𝓕   ＝⟨ ap 𝓕 I₀ ⟩
       ∅ ϵ 𝓕                    ＝⟨ preserves-₀ ⟩
       ₀                        ∎
    where
     I₀ : A ∩ complement A ＝ ∅
     I₀ = dfunext fe (λ x → min𝟚-complement (x ϵ A))

   II : A ϵ 𝓕 ∨ complement A ϵ 𝓕 ＝ ₁
   II = A ϵ 𝓕 ∨ complement A ϵ 𝓕 ＝⟨ (preserves-∨ A (complement A))⁻¹ ⟩
        (A ∪ complement A) ϵ 𝓕   ＝⟨ ap 𝓕 II₀ ⟩
        𝟏 ϵ 𝓕                    ＝⟨ preserves-₁ ⟩
        ₁                        ∎
    where
     II₀ : A ∪ complement A ＝ 𝟏
     II₀ = dfunext fe (λ x → max𝟚-complement (x ϵ A))

   III : A ∉ 𝓕 → complement A ϵ 𝓕 ＝ ⇁ (A ϵ 𝓕)
   III e = complement A ϵ 𝓕         ＝⟨refl⟩
           ₀ ∨ complement A ϵ 𝓕     ＝⟨ ap (λ - → - ∨ complement A ϵ 𝓕) (e ⁻¹) ⟩
           A ϵ 𝓕 ∨ complement A ϵ 𝓕 ＝⟨ II ⟩
           ₁                        ＝⟨refl⟩
           ⇁ ₀                      ＝⟨ ap ⇁_ (e ⁻¹) ⟩
           ⇁ (A ϵ 𝓕)                ∎

   IV : A ∈ 𝓕 → complement A ϵ 𝓕 ＝ ⇁ (A ϵ 𝓕)
   IV e = complement A ϵ 𝓕         ＝⟨refl⟩
          ₁ ∧ complement A ϵ 𝓕     ＝⟨ ap (λ - → - ∧ complement A ϵ 𝓕) (e ⁻¹) ⟩
          A ϵ 𝓕 ∧ complement A ϵ 𝓕 ＝⟨ I ⟩
          ₀                        ＝⟨refl⟩
          ⇁ ₁                      ＝⟨ ap ⇁_ (e ⁻¹) ⟩
          ⇁ (A ϵ 𝓕)                ∎

\end{code}

We now define the type 𝕌 X of the ultrafilters of the clopens of X,
the map 𝕡 that takes a point of X to its principal ultrafilter, and
the notions of a pre-Stone type and a Stone type. The clopens of X
form a discrete type precisely when X is Π-compact in the sense of the
module TypeTopology.WeaklyCompactTypes, so that a Stone type is a
Π-compact pre-Stone type.

\begin{code}

𝕌 : 𝓤 ̇ → 𝓤 ̇
𝕌 X = Σ 𝓕 ꞉ Clopen (Clopen X) , is-ultrafilter 𝓕

clopens-of : {X : 𝓤 ̇ } → 𝕌 X → Clopen (Clopen X)
clopens-of = pr₁

clopens-of-is-embedding : {X : 𝓤 ̇ } → is-embedding (clopens-of {𝓤} {X})
clopens-of-is-embedding = pr₁-is-embedding being-ultrafilter-is-prop

clopens-of-is-ultrafilter : {X : 𝓤 ̇ } (σ : 𝕌 X)
                          → is-ultrafilter (clopens-of σ)
clopens-of-is-ultrafilter = pr₂

𝕡 : (X : 𝓤 ̇ ) → X → 𝕌 X
𝕡 X x = (λ A → x ϵ A) , refl , refl , (λ A B → refl) , (λ A B → refl)

is-pre-stone-type : 𝓤 ̇ → 𝓤 ̇
is-pre-stone-type X = is-equiv (𝕡 X)

being-pre-stone-type-is-prop : (X : 𝓤 ̇ ) → is-prop (is-pre-stone-type X)
being-pre-stone-type-is-prop X = being-equiv-is-prop fe' (𝕡 X)

is-stone-type : 𝓤 ̇ → 𝓤 ̇
is-stone-type X = is-pre-stone-type X × is-discrete (Clopen X)

being-stone-type-is-prop : (X : 𝓤 ̇ ) → is-prop (is-stone-type X)
being-stone-type-is-prop X =
 ×-is-prop (being-pre-stone-type-is-prop X) (being-discrete-is-prop fe')

stone-types-are-pre-stone-types
 : {X : 𝓤 ̇ }
 → is-stone-type X
 → is-pre-stone-type X
stone-types-are-pre-stone-types
 = pr₁

stone-types-have-discrete-clopen-algebras
 : {X : 𝓤 ̇ }
 → is-stone-type X
 → is-discrete (Clopen X)
stone-types-have-discrete-clopen-algebras
 = pr₂

discrete-clopen-algebra-gives-Π-compact
 : {X : 𝓤 ̇ }
 → is-discrete (Clopen X)
 → is-Π-compact X
discrete-clopen-algebra-gives-Π-compact
 = power-of-two-discrete-gives-compact-exponent

Π-compact-gives-discrete-clopen-algebra
 : {X : 𝓤 ̇ }
 → is-Π-compact X
 → is-discrete (Clopen X)
Π-compact-gives-discrete-clopen-algebra c
 = discrete-to-power-Π-compact-is-discrete c 𝟚-is-discrete

stone-types-are-Π-compact
 : {X : 𝓤 ̇ }
 → is-stone-type X
 → is-Π-compact X
stone-types-are-Π-compact
 = discrete-clopen-algebra-gives-Π-compact
 ∘ stone-types-have-discrete-clopen-algebras

\end{code}

The first component of the principal-filter map 𝕡 amounts to the map
`eval X` of the module TypeTopology.TotallySeparated, which makes the
lemmas used in the following proofs applicable.

\begin{code}

totally-separated-gives-𝕡-is-embedding
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → is-embedding (𝕡 X)
totally-separated-gives-𝕡-is-embedding {𝓤} {X} τ
 = factor-is-embedding (𝕡 X) clopens-of
    (totally-separated-gives-totally-separated₂ fe τ)
    clopens-of-is-embedding

𝕡-is-embedding-gives-totally-separated
 : {X : 𝓤 ̇ }
 → is-embedding (𝕡 X)
 → is-totally-separated X
𝕡-is-embedding-gives-totally-separated e
 = totally-separated₂-gives-totally-separated fe
    (∘-is-embedding e clopens-of-is-embedding)

\end{code}

We now show that the ultrafilters of the clopens of a pre-Stone type
are all principal, give criteria for a type to be a pre-Stone type and
a Stone type, and show that pre-Stone types are totally separated.

\begin{code}

ultrafilters-of-pre-stone-types-are-principal
 : {X : 𝓤 ̇ }
 → is-pre-stone-type X
 → (𝓕 : Clopen (Clopen X))
 → is-ultrafilter 𝓕
 → is-principal 𝓕
ultrafilters-of-pre-stone-types-are-principal {𝓤} {X} ζ 𝓕 i
 = x , II
 where
  x : X
  x = inverse (𝕡 X) ζ (𝓕 , i)

  I : 𝕡 X x ＝ (𝓕 , i)
  I = inverses-are-sections (𝕡 X) ζ (𝓕 , i)

  II : (A : Clopen X) → A ϵ 𝓕 ＝ x ϵ A
  II A = (happly (ap clopens-of I) A)⁻¹

pre-stone-criterion
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → ((𝓕 : Clopen (Clopen X)) → is-ultrafilter 𝓕 → is-principal 𝓕)
 → is-pre-stone-type X
pre-stone-criterion {𝓤} {X} τ ψ
 = vv-equivs-are-equivs (𝕡 X) I
 where
  I : (σ : 𝕌 X) → is-singleton (fiber (𝕡 X) σ)
  I (𝓕 , i) = II (ψ 𝓕 i)
   where
    II : is-principal 𝓕 → is-singleton (fiber (𝕡 X) (𝓕 , i))
    II (x , e) =
     pointed-props-are-singletons
      (x , to-subtype-＝
            being-ultrafilter-is-prop
            (dfunext fe (λ A → (e A)⁻¹)))
      (totally-separated-gives-𝕡-is-embedding τ (𝓕 , i))

stone-criterion
 : {X : 𝓤 ̇ }
 → is-discrete (Clopen X)
 → is-totally-separated X
 → ((𝓕 : Clopen (Clopen X)) → is-ultrafilter 𝓕 → is-principal 𝓕)
 → is-stone-type X
stone-criterion d τ ψ = pre-stone-criterion τ ψ , d

pre-stone-types-are-totally-separated
 : {X : 𝓤 ̇ }
 → is-pre-stone-type X
 → is-totally-separated X
pre-stone-types-are-totally-separated {𝓤} {X} ζ
 = 𝕡-is-embedding-gives-totally-separated (equivs-are-embeddings (𝕡 X) ζ)

\end{code}

Pre-Stone types and Stone types are closed under retracts. The
clopens of a retract of X form a retract of the clopens of X, and a
retract of a discrete type is discrete.

\begin{code}

retract-is-pre-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → retract Y of X
 → is-pre-stone-type X
 → is-pre-stone-type Y
retract-is-pre-stone-type {𝓤} {𝓥} {X} {Y} ρ ζ
 = pre-stone-criterion
    (retract-of-totally-separated
      ρ
      (pre-stone-types-are-totally-separated ζ))
    I
 where
  r : X → Y
  r = retraction ρ

  s : Y → X
  s = section ρ

  I : (𝓕 : Clopen (Clopen Y)) → is-ultrafilter 𝓕 → is-principal 𝓕
  I 𝓕 i = III (ultrafilters-of-pre-stone-types-are-principal ζ 𝒢 II)
   where
    open ultrafilter-properties 𝓕 i

    𝒢 : Clopen (Clopen X)
    𝒢 = λ A → s ⁻¹[ A ] ϵ 𝓕

    II : is-ultrafilter 𝒢
    II = preserves-₀ ,
         preserves-₁ ,
         (λ A A' → preserves-∧ (s ⁻¹[ A ]) (s ⁻¹[ A' ])) ,
         (λ A A' → preserves-∨ (s ⁻¹[ A ]) (s ⁻¹[ A' ]))

    III : is-principal 𝒢 → is-principal 𝓕
    III (x , φ) = r x , IV
     where
      IV : (A : Clopen Y) → A ϵ 𝓕 ＝ r x ϵ A
      IV A = A ϵ 𝓕                 ＝⟨ ap 𝓕 V ⟩
             s ⁻¹[ r ⁻¹[ A ] ] ϵ 𝓕 ＝⟨ φ (r ⁻¹[ A ]) ⟩
             r x ϵ A               ∎
       where
        V : A ＝ s ⁻¹[ r ⁻¹[ A ] ]
        V = dfunext fe (λ y → ap A (retract-condition ρ y)⁻¹)

retract-is-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → retract Y of X
 → is-stone-type X
 → is-stone-type Y
retract-is-stone-type ρ ζ
 = retract-is-pre-stone-type ρ (stone-types-are-pre-stone-types ζ) ,
   retract-is-discrete
    (retract-contravariance fe ρ)
    (stone-types-have-discrete-clopen-algebras ζ)

\end{code}

Pre-Stone types and Stone types are closed under equivalence, which is
the special case of the closure under retracts for the retraction that
an equivalence gives.

\begin{code}

equiv-to-pre-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → X ≃ Y
 → is-pre-stone-type Y
 → is-pre-stone-type X
equiv-to-pre-stone-type 𝕗 = retract-is-pre-stone-type (≃-gives-◁ 𝕗)

equiv-to-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → X ≃ Y
 → is-stone-type Y
 → is-stone-type X
equiv-to-stone-type 𝕗 = retract-is-stone-type (≃-gives-◁ 𝕗)

\end{code}

The empty type is a Stone type.

\begin{code}

𝟘-is-pre-stone-type : is-pre-stone-type (𝟘 {𝓤})
𝟘-is-pre-stone-type {𝓤} = vv-equivs-are-equivs (𝕡 𝟘) I
 where
  I : (σ : 𝕌 𝟘) → is-singleton (fiber (𝕡 𝟘) σ)
  I (𝓕 , i) = zero-is-one-elim III
   where
    open ultrafilter-properties 𝓕 i

    II : ∅ ＝ 𝟏
    II = dfunext fe (λ x → 𝟘-elim x)

    III : ₀ ＝ ₁
    III = ₀     ＝⟨ preserves-₀ ⁻¹ ⟩
          ∅ ϵ 𝓕 ＝⟨ ap 𝓕 II ⟩
          𝟏 ϵ 𝓕 ＝⟨ preserves-₁ ⟩
          ₁     ∎

𝟘-is-stone-type : is-stone-type (𝟘 {𝓤})
𝟘-is-stone-type {𝓤}
 = 𝟘-is-pre-stone-type ,
   Π-compact-gives-discrete-clopen-algebra (empty-types-are-Π-compact 𝟘-elim)

\end{code}

The one-point type is a Stone type.

\begin{code}

𝟙-is-pre-stone-type : is-pre-stone-type (𝟙 {𝓤})
𝟙-is-pre-stone-type {𝓤} =
 pre-stone-criterion 𝟙-is-totally-separated I
 where
  I : (𝓕 : Clopen (Clopen 𝟙)) → is-ultrafilter 𝓕 → is-principal 𝓕
  I 𝓕 i = ⋆ , II
   where
    open ultrafilter-properties 𝓕 i

    II : (A : Clopen (𝟙 {𝓤})) → A ϵ 𝓕 ＝ ⋆ ϵ A
    II A = 𝟚-equality-cases III IV
     where
      III : ⋆ ∉ A → A ϵ 𝓕 ＝ ⋆ ϵ A
      III e = A ϵ 𝓕 ＝⟨ ap 𝓕 (dfunext fe (λ _ → e)) ⟩
              ∅ ϵ 𝓕 ＝⟨ preserves-₀ ⟩
              ₀     ＝⟨ e ⁻¹ ⟩
              ⋆ ϵ A ∎

      IV : ⋆ ∈ A → A ϵ 𝓕 ＝ ⋆ ϵ A
      IV e = A ϵ 𝓕 ＝⟨ ap 𝓕 (dfunext fe (λ _ → e)) ⟩
             𝟏 ϵ 𝓕 ＝⟨ preserves-₁ ⟩
             ₁     ＝⟨ e ⁻¹ ⟩
             ⋆ ϵ A ∎

𝟙-is-stone-type : is-stone-type (𝟙 {𝓤})
𝟙-is-stone-type
 = 𝟙-is-pre-stone-type ,
   Π-compact-gives-discrete-clopen-algebra
    (compact-types-are-Π-compact
      (compact∙-types-are-compact 𝟙-is-compact∙))

\end{code}

Given a clopen A of X and a map σ that takes a point of X in A to a
point of Y, we extend a clopen of Y to a clopen of X.

\begin{code}

module clopen-extension
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
        (A : Clopen X)
        (σ : (x : X) → x ∈ A → Y)
       where

 private
  δ : (x : X) → is-decidable (x ∈ A)
  δ x = ∈-is-decidable x A

  ext' : Clopen Y → (x : X) → is-decidable (x ∈ A) → 𝟚
  ext' C x (inl d) = σ x d ϵ C
  ext' C x (inr _) = ₀

 ext : Clopen Y → Clopen X
 ext C = λ x → ext' C x (δ x)

 ext-∅ : ext ∅ ＝ ∅
 ext-∅ = dfunext fe (λ x → I x (δ x))
  where
   I : (x : X) (c : is-decidable (x ∈ A)) → ext' ∅ x c ＝ ₀
   I x (inl d) = refl
   I x (inr _) = refl

 ext-𝟏 : ext 𝟏 ＝ A
 ext-𝟏 = dfunext fe (λ x → I x (δ x))
  where
   I : (x : X) (c : is-decidable (x ∈ A)) → ext' 𝟏 x c ＝ x ϵ A
   I x (inl d) = d ⁻¹
   I x (inr ν) = (different-from-₁-equal-₀ ν)⁻¹

 ext-∩ : (C C' : Clopen Y) → ext (C ∩ C') ＝ ext C ∩ ext C'
 ext-∩ C C' = dfunext fe (λ x → I x (δ x))
  where
   I : (x : X) (c : is-decidable (x ∈ A))
     → ext' (C ∩ C') x c ＝ ext' C x c ∧ ext' C' x c
   I x (inl d) = refl
   I x (inr _) = refl

 ext-∪ : (C C' : Clopen Y) → ext (C ∪ C') ＝ ext C ∪ ext C'
 ext-∪ C C' = dfunext fe (λ x → I x (δ x))
  where
   I : (x : X) (c : is-decidable (x ∈ A))
     → ext' (C ∪ C') x c ＝ ext' C x c ∨ ext' C' x c
   I x (inl d) = refl
   I x (inr _) = refl

 ext-at-section : (C : Clopen Y) (x : X) (d : x ∈ A)
                → x ϵ ext C ＝ σ x d ϵ C
 ext-at-section C x d = I (δ x)
  where
   I : (c : is-decidable (x ∈ A)) → ext' C x c ＝ σ x d ϵ C
   I (inl d') = ap (λ - → σ x - ϵ C) (𝟚-is-set d' d)
   I (inr ν)  = 𝟘-elim (ν d)

 ext-gives-∈ : (C : Clopen Y) (x : X) → x ∈ ext C → x ∈ A
 ext-gives-∈ C x = I (δ x)
  where
   I : (c : is-decidable (x ∈ A)) → ext' C x c ＝ ₁ → x ∈ A
   I (inl d) _ = d
   I (inr _) s = zero-is-one-elim s

 module extension-of-a-preimage
         (j : Y → X)
         (jσ : (x : X) (d : x ∈ A) → j (σ x d) ＝ x)
        where

  ext-preimage-agrees-on-A
   : (B : Clopen X) (x : X)
   → x ∈ A
   → x ϵ ext (j ⁻¹[ B ]) ＝ x ϵ B
  ext-preimage-agrees-on-A B x d =
   x ϵ ext (j ⁻¹[ B ]) ＝⟨ ext-at-section (j ⁻¹[ B ]) x d ⟩
   j (σ x d) ϵ B       ＝⟨ ap B (jσ x d) ⟩
   x ϵ B               ∎

  ext-preimage-⊆ : (B : Clopen X) → ext (j ⁻¹[ B ]) ⊆ B
  ext-preimage-⊆ B x s =
   x ϵ B               ＝⟨ (ext-preimage-agrees-on-A B x d)⁻¹ ⟩
   x ϵ ext (j ⁻¹[ B ]) ＝⟨ s ⟩
   ₁                   ∎
   where
    d : x ∈ A
    d = ext-gives-∈ (j ⁻¹[ B ]) x s

  ext-preimage-covers
   : (B : Clopen X) → B ⊆ ext (j ⁻¹[ B ]) ∪ complement A
  ext-preimage-covers B x = I (∈-is-decidable x A)
   where
    I : is-decidable (x ∈ A)
      → x ∈ B → x ∈ ext (j ⁻¹[ B ]) ∪ complement A
    I (inl d) s = max𝟚-lemma-converse (inl II)
     where
      II : x ∈ ext (j ⁻¹[ B ])
      II = x ϵ ext (j ⁻¹[ B ]) ＝⟨ ext-preimage-agrees-on-A B x d ⟩
           x ϵ B               ＝⟨ s ⟩
           ₁                   ∎
    I (inr ν) s = max𝟚-lemma-converse
                   (inr (ap ⇁_ (different-from-₁-equal-₀ ν)))

\end{code}

Criterion for the the preimage being an ultrafilter.

\begin{code}

preimage-is-ultrafilter
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
   (𝓕 : Clopen (Clopen X))
 → is-ultrafilter 𝓕
 → (E : Clopen Y → Clopen X)
 → E ∅ ＝ ∅
 → E 𝟏 ∈ 𝓕
 → ((C C' : Clopen Y) → E (C ∩ C') ＝ E C ∩ E C')
 → ((C C' : Clopen Y) → E (C ∪ C') ＝ E C ∪ E C')
 → is-ultrafilter (E ⁻¹[ 𝓕 ])
preimage-is-ultrafilter {𝓤} {𝓥} {X} {Y} 𝓕 i E E-∅ E-𝟏 E-∩ E-∪
 = I , E-𝟏 , II , III
 where
  open ultrafilter-properties 𝓕 i

  I : E ∅ ∉ 𝓕
  I = E ∅ ϵ 𝓕 ＝⟨ ap 𝓕 E-∅ ⟩
      ∅ ϵ 𝓕   ＝⟨ preserves-₀ ⟩
      ₀       ∎

  II : (C C' : Clopen Y) → E (C ∩ C') ϵ 𝓕 ＝ E C ϵ 𝓕 ∧ E C' ϵ 𝓕
  II C C' = E (C ∩ C') ϵ 𝓕     ＝⟨ ap 𝓕 (E-∩ C C') ⟩
            (E C ∩ E C') ϵ 𝓕   ＝⟨ preserves-∧ (E C) (E C') ⟩
            E C ϵ 𝓕 ∧ E C' ϵ 𝓕 ∎

  III : (C C' : Clopen Y) → E (C ∪ C') ϵ 𝓕 ＝ E C ϵ 𝓕 ∨ E C' ϵ 𝓕
  III C C' = E (C ∪ C') ϵ 𝓕     ＝⟨ ap 𝓕 (E-∪ C C') ⟩
             (E C ∪ E C') ϵ 𝓕   ＝⟨ preserves-∨ (E C) (E C') ⟩
             E C ϵ 𝓕 ∨ E C' ϵ 𝓕 ∎

\end{code}

We now give a technical criterion for an ultrafilter to be principal,
which we apply a number of times.

\begin{code}

ultrafilter-principality-criterion
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
   (A : Clopen X)
   (j : Y → X)
   (σ : (x : X) → x ∈ A → Y)
 → ((x : X) (d : x ∈ A) → j (σ x d) ＝ x)
 → is-pre-stone-type Y
 → (𝓕 : Clopen (Clopen X))
 → is-ultrafilter 𝓕
 → A ∈ 𝓕
 → Σ y ꞉ Y , 𝓕 is-principal-at j y
ultrafilter-principality-criterion {𝓤} {𝓥} {X} {Y} A j σ jσ ζ 𝓕 i e
 = II (ultrafilters-of-pre-stone-types-are-principal
        ζ (ext ⁻¹[ 𝓕 ]) ext-is-ultrafilter)
 where
  open ultrafilter-properties 𝓕 i
  open clopen-extension A σ
  open extension-of-a-preimage j jσ

  ext-is-ultrafilter : is-ultrafilter (ext ⁻¹[ 𝓕 ])
  ext-is-ultrafilter = preimage-is-ultrafilter 𝓕 i ext ext-∅ I ext-∩ ext-∪
   where
    I : ext 𝟏 ∈ 𝓕
    I = ext 𝟏 ϵ 𝓕 ＝⟨ ap 𝓕 ext-𝟏 ⟩
        A ϵ 𝓕     ＝⟨ e ⟩
        ₁         ∎

  II : is-principal (ext ⁻¹[ 𝓕 ]) → Σ y ꞉ Y , 𝓕 is-principal-at j y
  II (y , φ) = y , III
   where
    III : 𝓕 is-principal-at j y
    III B = 𝟚-equality-cases IV VII
     where
      IV : j y ∉ B → B ϵ 𝓕 ＝ j y ϵ B
      IV d = B ϵ 𝓕   ＝⟨ VI ⟩
             ₀       ＝⟨ d ⁻¹ ⟩
             j y ϵ B ∎
       where
        V : (ext (j ⁻¹[ B ]) ∪ complement A) ∉ 𝓕
        V = (ext (j ⁻¹[ B ]) ∪ complement A) ϵ 𝓕   ＝⟨ V₀ ⟩
            ext (j ⁻¹[ B ]) ϵ 𝓕 ∨ complement A ϵ 𝓕 ＝⟨ ap₂ _∨_ V₁ V₂ ⟩
            ₀ ∨ ₀                                  ＝⟨refl⟩
            ₀                                      ∎
         where
          V₀ = preserves-∨ (ext (j ⁻¹[ B ])) (complement A)

          V₁ : ext (j ⁻¹[ B ]) ∉ 𝓕
          V₁ = ext (j ⁻¹[ B ]) ϵ 𝓕 ＝⟨ φ (j ⁻¹[ B ]) ⟩
               j y ϵ B             ＝⟨ d ⟩
               ₀                   ∎

          V₂ : complement A ∉ 𝓕
          V₂ = complement A ϵ 𝓕 ＝⟨ preserves-complement A ⟩
               ⇁ (A ϵ 𝓕)        ＝⟨ ap ⇁_ e ⟩
               ⇁ ₁              ＝⟨refl⟩
               ₀                ∎

        VI : B ∉ 𝓕
        VI = ₀-smallest (monotone (ext-preimage-covers B)) V

      VII : j y ∈ B → B ϵ 𝓕 ＝ j y ϵ B
      VII d = B ϵ 𝓕   ＝⟨ IX ⟩
              ₁       ＝⟨ d ⁻¹ ⟩
              j y ϵ B ∎
       where
        VIII : ext (j ⁻¹[ B ]) ∈ 𝓕
        VIII = ext (j ⁻¹[ B ]) ϵ 𝓕 ＝⟨ φ (j ⁻¹[ B ]) ⟩
               j y ϵ B             ＝⟨ d ⟩
               ₁                   ∎

        IX : B ∈ 𝓕
        IX = upper-closed (ext-preimage-⊆ B) VIII

\end{code}

Stone types are closed under binary sums.

\begin{code}

+-is-pre-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-pre-stone-type X
 → is-pre-stone-type Y
 → is-pre-stone-type (X + Y)
+-is-pre-stone-type {𝓤} {𝓥} {X} {Y} ζ₀ ζ₁
 = II
 where
  A : Clopen (X + Y)
  A (inl _) = ₁
  A (inr _) = ₀

  σ₀ : (z : X + Y) → z ∈ A → X
  σ₀ (inl x) d = x
  σ₀ (inr y) d = zero-is-one-elim d

  σ₁ : (z : X + Y) → z ∈ complement A → Y
  σ₁ (inl x) d = zero-is-one-elim d
  σ₁ (inr y) d = y

  jσ₀ : (z : X + Y) (d : z ∈ A) → inl (σ₀ z d) ＝ z
  jσ₀ (inl x) d = refl
  jσ₀ (inr y) d = zero-is-one-elim d

  jσ₁ : (z : X + Y) (d : z ∈ complement A) → inr (σ₁ z d) ＝ z
  jσ₁ (inl x) d = zero-is-one-elim d
  jσ₁ (inr y) d = refl

  I : (𝓕 : Clopen (Clopen (X + Y))) → is-ultrafilter 𝓕 → is-principal 𝓕
  I 𝓕 i = 𝟚-equality-cases I₀ I₁
   where
    open ultrafilter-properties 𝓕 i

    I₀ : A ∉ 𝓕 → is-principal 𝓕
    I₀ d = ⦅2⦆ (ultrafilter-principality-criterion
                (complement A) inr σ₁ jσ₁ ζ₁ 𝓕 i ⦅1⦆)
     where
      ⦅1⦆ : complement A ∈ 𝓕
      ⦅1⦆ = complement A ϵ 𝓕 ＝⟨ preserves-complement A ⟩
            ⇁ (A ϵ 𝓕)        ＝⟨ ap ⇁_ d ⟩
            ⇁ ₀              ＝⟨refl⟩
            ₁                ∎

      ⦅2⦆ : (Σ y ꞉ Y , 𝓕 is-principal-at inr y) → is-principal 𝓕
      ⦅2⦆ (y , φ) = inr y , φ

    I₁ : A ∈ 𝓕 → is-principal 𝓕
    I₁ d = ⦅1⦆ (ultrafilter-principality-criterion A inl σ₀ jσ₀ ζ₀ 𝓕 i d)
     where
      ⦅1⦆ : (Σ x ꞉ X , 𝓕 is-principal-at inl x) → is-principal 𝓕
      ⦅1⦆ (x , φ) = inl x , φ

  II : is-pre-stone-type (X + Y)
  II = pre-stone-criterion
        (+-totally-separated X Y
          (pre-stone-types-are-totally-separated ζ₀)
          (pre-stone-types-are-totally-separated ζ₁))
        I

+-is-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-stone-type X
 → is-stone-type Y
 → is-stone-type (X + Y)
+-is-stone-type ζ₀ ζ₁
 = +-is-pre-stone-type
    (stone-types-are-pre-stone-types ζ₀)
    (stone-types-are-pre-stone-types ζ₁) ,
   Π-compact-gives-discrete-clopen-algebra
    (+-is-Π-compact
      (stone-types-are-Π-compact ζ₀)
      (stone-types-are-Π-compact ζ₁))

\end{code}

Finite types are Stone types.

\begin{code}

Fin-is-stone-type : (n : ℕ) → is-stone-type (Fin n)
Fin-is-stone-type 0        = 𝟘-is-stone-type
Fin-is-stone-type (succ n) =
 +-is-stone-type (Fin-is-stone-type n) (𝟙-is-stone-type {𝓤₀})

finite-linear-orders-are-stone-types
 : {X : 𝓤 ̇ }
 → finite-linear-order X
 → is-stone-type X
finite-linear-orders-are-stone-types (n , 𝕗)
 = equiv-to-stone-type 𝕗 (Fin-is-stone-type n)

open PropositionalTruncation pt using (∥∥-rec)
open finiteness pt renaming (is-finite to is-finite-type)

finite-types-are-stone-types
 : {X : 𝓤 ̇ }
 → is-finite-type X
 → is-stone-type X
finite-types-are-stone-types {𝓤} {X} (n , φ)
 = II
 where
  I : X ≃ Fin n → is-stone-type X
  I 𝕗 = finite-linear-orders-are-stone-types (n , 𝕗)

  II : is-stone-type X
  II = ∥∥-rec (being-stone-type-is-prop X) I φ

\end{code}

The two-point type is a Stone type.

\begin{code}

𝟚-is-stone-type : is-stone-type 𝟚
𝟚-is-stone-type =
 equiv-to-stone-type
  (𝟚-≃-𝟙+𝟙 {𝓤₀})
  (+-is-stone-type
    (𝟙-is-stone-type {𝓤₀})
    (𝟙-is-stone-type {𝓤₀}))

\end{code}

A ¬¬-stable proposition is a pre-Stone type.

\begin{code}

¬¬-stable-props-are-pre-stone-types
 : {P : 𝓤 ̇ }
 → is-prop P
 → ¬¬-stable P
 → is-pre-stone-type P
¬¬-stable-props-are-pre-stone-types {𝓤} {P} P-is-prop P-is-¬¬-stable
 = pre-stone-criterion I II
 where
  I : is-totally-separated P
  I {x} {y} _ = P-is-prop x y

  II : (𝓕 : Clopen (Clopen P)) → is-ultrafilter 𝓕 → is-principal 𝓕
  II 𝓕 i = x₀ , VI
   where
    open ultrafilter-properties 𝓕 i

    III : ¬ P → ∅ ＝ 𝟏
    III ν = dfunext fe (λ x → 𝟘-elim (ν x))

    IV : ¬¬ P
    IV ν = zero-is-one-elim
            (₀     ＝⟨ preserves-₀ ⁻¹ ⟩
             ∅ ϵ 𝓕 ＝⟨ ap 𝓕 (III ν) ⟩
             𝟏 ϵ 𝓕 ＝⟨ preserves-₁ ⟩
             ₁     ∎)

    x₀ : P
    x₀ = P-is-¬¬-stable IV

    V : (A : Clopen P) (b : 𝟚) → x₀ ϵ A ＝ b → A ＝ (λ _ → b)
    V A b e = dfunext fe V₀
     where
      V₀ : (x : P) → x ϵ A ＝ b
      V₀ x = x ϵ A  ＝⟨ ap A (P-is-prop x x₀) ⟩
             x₀ ϵ A ＝⟨ e ⟩
             b      ∎

    VI : (A : Clopen P) → A ϵ 𝓕 ＝ x₀ ϵ A
    VI A = 𝟚-equality-cases VI₀ VI₁
     where
      VI₀ : x₀ ∉ A → A ϵ 𝓕 ＝ x₀ ϵ A
      VI₀ e = A ϵ 𝓕  ＝⟨ ap 𝓕 (V A ₀ e) ⟩
              ∅ ϵ 𝓕  ＝⟨ preserves-₀ ⟩
              ₀      ＝⟨ e ⁻¹ ⟩
              x₀ ϵ A ∎

      VI₁ : x₀ ∈ A → A ϵ 𝓕 ＝ x₀ ϵ A
      VI₁ e = A ϵ 𝓕  ＝⟨ ap 𝓕 (V A ₁ e) ⟩
              𝟏 ϵ 𝓕  ＝⟨ preserves-₁ ⟩
              ₁      ＝⟨ e ⁻¹ ⟩
              x₀ ϵ A ∎

\end{code}

A proposition is a Stone type precisely when it is decidable.

\begin{code}

decidable-props-are-stone-types
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-decidable P
 → is-stone-type P
decidable-props-are-stone-types {𝓤} {P} P-is-prop (inl x)
 = equiv-to-stone-type
    (singleton-≃-𝟙 (pointed-props-are-singletons x P-is-prop))
    (𝟙-is-stone-type {𝓤})
decidable-props-are-stone-types {𝓤} {P} P-is-prop (inr ν)
 = equiv-to-stone-type (empty-≃-𝟘 ν) (𝟘-is-stone-type {𝓤})

\end{code}

A decidable property of the points of X is classified by a clopen of X,
its characteristic clopen, and we name the four implications relating
membership in it and the property.

\begin{code}

characteristic-clopen
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
 → ((x : X) → is-decidable (A x))
 → Clopen X
characteristic-clopen d = pr₁ (co-characteristic-function d)

characteristic-clopen-property
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
   (d : (x : X) → is-decidable (A x))
   (x : X)
 → (x ∉ characteristic-clopen d → ¬ A x)
 × (x ∈ characteristic-clopen d → A x)
characteristic-clopen-property d = pr₂ (co-characteristic-function d)

characteristic-clopen-property₀
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
   (d : (x : X) → is-decidable (A x))
   (x : X)
 → x ∉ characteristic-clopen d
 → ¬ A x
characteristic-clopen-property₀ d x = pr₁ (characteristic-clopen-property d x)

characteristic-clopen-property₁
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
   (d : (x : X) → is-decidable (A x))
   (x : X)
 → x ∈ characteristic-clopen d
 → A x
characteristic-clopen-property₁ d x = pr₂ (characteristic-clopen-property d x)

characteristic-clopen-property₂
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
   (d : (x : X) → is-decidable (A x))
   (x : X)
 → A x
 → x ∈ characteristic-clopen d
characteristic-clopen-property₂ d x a
 = different-from-₀-equal-₁
    (λ e → characteristic-clopen-property₀ d x e a)

characteristic-clopen-property₃
 : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
   (d : (x : X) → is-decidable (A x))
   (x : X)
 → ¬ A x
 → x ∉ characteristic-clopen d
characteristic-clopen-property₃ d x ν
 = different-from-₁-equal-₀
    (λ e → ν (characteristic-clopen-property₁ d x e))

\end{code}

For the converse we need the following. For a Π-compact proposition P,
it is decidable whether a clopen of P contains every point of P, and
so this condition is classified by a clopen of the clopens of P. The
whole space 𝟏 is the only clopen satisfying it, and this singleton is
an ultrafilter as soon as P is nonempty.

\begin{code}

module singleton-𝟏-ultrafilter
        {P : 𝓤 ̇ }
        (P-is-prop : is-prop P)
        (c : is-Π-compact P)
       where

 singleton-𝟏 : Clopen (Clopen P)
 singleton-𝟏 = characteristic-clopen c

 singleton-𝟏-property₀ : (A : Clopen P)
                       → A ∉ singleton-𝟏
                       → ¬ ((x : P) → x ∈ A)
 singleton-𝟏-property₀ = characteristic-clopen-property₀ c

 singleton-𝟏-property₁ : (A : Clopen P)
                       → A ∈ singleton-𝟏
                       → (x : P) → x ∈ A
 singleton-𝟏-property₁ = characteristic-clopen-property₁ c

 singleton-𝟏-property₂ : (A : Clopen P)
                       → ((x : P) → x ∈ A)
                       → A ∈ singleton-𝟏
 singleton-𝟏-property₂ = characteristic-clopen-property₂ c

 singleton-𝟏-property₃ : (A : Clopen P)
                       → ¬ ((x : P) → x ∈ A)
                       → A ∉ singleton-𝟏
 singleton-𝟏-property₃ = characteristic-clopen-property₃ c

 private
  not-all-gives-¬¬-some-outside
   : (A : Clopen P)
   → ¬ ((x : P) → x ∈ A)
   → ¬¬ (Σ x ꞉ P , x ∉ A)
  not-all-gives-¬¬-some-outside A ν φ =
   ν (λ x → different-from-₀-equal-₁ (λ e → φ (x , e)))

  not-whole-space-∪
   : (A B : Clopen P)
   → ¬ ((x : P) → x ∈ A)
   → ¬ ((x : P) → x ∈ B)
   → ¬ ((x : P) → x ∈ A ∪ B)
  not-whole-space-∪ A B νA νB σ = IV
   where
    I : (x₀ x₁ : P) → x₀ ∉ A → x₁ ∉ B → ₀ ＝ ₁
    I x₀ x₁ r₀ r₁ =
     ₀            ＝⟨ (ap₂ _∨_ r₀ I₀)⁻¹ ⟩
     x₀ ϵ (A ∪ B) ＝⟨ σ x₀ ⟩
     ₁            ∎
     where
      I₀ : x₀ ∉ B
      I₀ = x₀ ϵ B ＝⟨ ap B (P-is-prop x₀ x₁) ⟩
           x₁ ϵ B ＝⟨ r₁ ⟩
           ₀      ∎

    II : (x₀ : P) → x₀ ∉ A → ¬ (Σ x ꞉ P , x ∉ B)
    II x₀ r₀ (x₁ , r₁) = zero-is-one-elim (I x₀ x₁ r₀ r₁)

    III : ¬ (Σ x ꞉ P , x ∉ A)
    III (x₀ , r₀) = not-all-gives-¬¬-some-outside B νB (II x₀ r₀)

    IV : 𝟘
    IV = not-all-gives-¬¬-some-outside A νA III

 singleton-𝟏-preserves-∧
  : (A B : Clopen P)
  → (A ∩ B) ϵ singleton-𝟏 ＝ A ϵ singleton-𝟏 ∧ B ϵ singleton-𝟏
 singleton-𝟏-preserves-∧ A B = ＝₂-criterion I II
  where
   I : (A ∩ B) ∈ singleton-𝟏
     → A ϵ singleton-𝟏 ∧ B ϵ singleton-𝟏 ＝ ₁
   I e = Lemma[a＝₁→b＝₁→min𝟚ab＝₁] III IV
    where
     σ : (x : P) → x ∈ A ∩ B
     σ = singleton-𝟏-property₁ (A ∩ B) e

     III : A ∈ singleton-𝟏
     III = singleton-𝟏-property₂ A (λ x → Lemma[min𝟚ab＝₁→a＝₁] (σ x))

     IV : B ∈ singleton-𝟏
     IV = singleton-𝟏-property₂ B (λ x → Lemma[min𝟚ab＝₁→b＝₁] (σ x))

   II : A ϵ singleton-𝟏 ∧ B ϵ singleton-𝟏 ＝ ₁
      → (A ∩ B) ∈ singleton-𝟏
   II e = singleton-𝟏-property₂ (A ∩ B) V
    where
     V : (x : P) → x ∈ A ∩ B
     V x = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
            (singleton-𝟏-property₁ A (Lemma[min𝟚ab＝₁→a＝₁] e) x)
            (singleton-𝟏-property₁ B (Lemma[min𝟚ab＝₁→b＝₁] e) x)

 singleton-𝟏-preserves-∨
  : (A B : Clopen P)
  → (A ∪ B) ϵ singleton-𝟏 ＝ A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏
 singleton-𝟏-preserves-∨ A B = ＝₂-criterion I II
  where
   I : (A ∪ B) ∈ singleton-𝟏
     → A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏 ＝ ₁
   I e = 𝟚-equality-cases III IV
    where
     σ : (x : P) → x ∈ A ∪ B
     σ = singleton-𝟏-property₁ (A ∪ B) e

     III : A ∉ singleton-𝟏
         → A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏 ＝ ₁
     III e₀ = 𝟚-equality-cases V VI
      where
       V : B ∉ singleton-𝟏
         → A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏 ＝ ₁
       V e₁ = 𝟘-elim
               (not-whole-space-∪ A B
                 (singleton-𝟏-property₀ A e₀)
                 (singleton-𝟏-property₀ B e₁)
                 σ)

       VI : B ∈ singleton-𝟏
          → A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏 ＝ ₁
       VI e₁ = max𝟚-lemma-converse (inr e₁)

     IV : A ∈ singleton-𝟏
        → A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏 ＝ ₁
     IV e₀ = max𝟚-lemma-converse (inl e₀)

   II : A ϵ singleton-𝟏 ∨ B ϵ singleton-𝟏 ＝ ₁
      → (A ∪ B) ∈ singleton-𝟏
   II e = singleton-𝟏-property₂ (A ∪ B) (cases VII VIII (max𝟚-lemma e))
    where
     VII : A ∈ singleton-𝟏 → (x : P) → x ∈ A ∪ B
     VII e₀ x = max𝟚-lemma-converse (inl (singleton-𝟏-property₁ A e₀ x))

     VIII : B ∈ singleton-𝟏 → (x : P) → x ∈ A ∪ B
     VIII e₁ x = max𝟚-lemma-converse (inr (singleton-𝟏-property₁ B e₁ x))

 singleton-𝟏-is-ultrafilter : ¬¬ P → is-ultrafilter singleton-𝟏
 singleton-𝟏-is-ultrafilter ν
  = I ,
    II ,
    singleton-𝟏-preserves-∧ ,
    singleton-𝟏-preserves-∨
  where
   I : ∅ ∉ singleton-𝟏
   I = singleton-𝟏-property₃ ∅ (λ σ → ν (λ x → zero-is-one-elim (σ x)))

   II : 𝟏 ∈ singleton-𝟏
   II = singleton-𝟏-property₂ 𝟏 (λ _ → refl)

stone-props-are-decidable
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-stone-type P
 → is-decidable P
stone-props-are-decidable {𝓤} {P} P-is-prop ζ
 = II
 where
  c : is-Π-compact P
  c = stone-types-are-Π-compact ζ

  open singleton-𝟏-ultrafilter P-is-prop c

  I : is-decidable (¬ P) → is-decidable P
  I (inl ν) = inr ν
  I (inr ν) = inl (principal-point
                    (ultrafilters-of-pre-stone-types-are-principal
                      (stone-types-are-pre-stone-types ζ)
                      singleton-𝟏
                      (singleton-𝟏-is-ultrafilter ν)))

  II : is-decidable P
  II = I (negations-of-Π-compact-types-are-decidable P c)

\end{code}

A map from X to Z takes the clopens of Z to the clopens of X by taking
preimages, and this preserves the boolean operations on the nose. So
an ultrafilter of the clopens of X gives an ultrafilter of the clopens
of Z, which we call its image.

\begin{code}

module _ {X : 𝓤 ̇ } {Z : 𝓦 ̇ } (f : X → Z) where

 ultrafilter-image : Clopen (Clopen X) → Clopen (Clopen Z)
 ultrafilter-image 𝓕 = λ C → f ⁻¹[ C ] ϵ 𝓕

 preimage-∅ : f ⁻¹[ ∅ ] ＝ ∅
 preimage-∅ = refl

 preimage-𝟏 : f ⁻¹[ 𝟏 ] ＝ 𝟏
 preimage-𝟏 = refl

 preimage-∩ : (C C' : Clopen Z)
            → f ⁻¹[ C ∩ C' ] ＝ f ⁻¹[ C ] ∩ f ⁻¹[ C' ]
 preimage-∩ C C' = refl

 preimage-∪ : (C C' : Clopen Z)
            → f ⁻¹[ C ∪ C' ] ＝ f ⁻¹[ C ] ∪ f ⁻¹[ C' ]
 preimage-∪ C C' = refl

 ultrafilter-image-is-ultrafilter
  : (𝓕 : Clopen (Clopen X))
  → is-ultrafilter 𝓕
  → is-ultrafilter (ultrafilter-image 𝓕)
 ultrafilter-image-is-ultrafilter 𝓕 i
  = preimage-is-ultrafilter 𝓕 i (f ⁻¹[_])
     preimage-∅
     I
     preimage-∩
     preimage-∪
  where
   open ultrafilter-properties 𝓕 i

   I : f ⁻¹[ 𝟏 ] ∈ 𝓕
   I = f ⁻¹[ 𝟏 ] ϵ 𝓕 ＝⟨ ap 𝓕 preimage-𝟏 ⟩
       𝟏 ϵ 𝓕         ＝⟨ preserves-₁ ⟩
       ₁             ∎

\end{code}

A product of pre-Stone types indexed by a proposition is a pre-Stone
type, which is the analogue of the micro Tychonoff theorem of the
module TypeTopology.MicroTychonoff. The point at which 𝓕 is principal
has to be given uniformly in the witnesses of P.

\begin{code}

prop-indexed-products-are-pre-stone-types
 : {P : 𝓤 ̇ } {Y : P → 𝓥 ̇ }
 → is-prop P
 → ((p : P) → is-pre-stone-type (Y p))
 → is-pre-stone-type (Π Y)
prop-indexed-products-are-pre-stone-types {𝓤} {𝓥} {P} {Y} P-is-prop ζ
 = pre-stone-criterion
    (Π-is-totally-separated fe
      (λ p → pre-stone-types-are-totally-separated (ζ p)))
    I
 where
  𝕖 : (p : P) → Π Y ≃ Y p
  𝕖 p = prop-indexed-product p fe P-is-prop

  I : (𝓕 : Clopen (Clopen (Π Y))) → is-ultrafilter 𝓕 → is-principal 𝓕
  I 𝓕 i = f , IV
   where
    open ultrafilter-properties 𝓕 i

    𝓖 : (p : P) → Clopen (Clopen (Y p))
    𝓖 p = ultrafilter-image ⌜ 𝕖 p ⌝ 𝓕

    𝓖-is-ultrafilter : (p : P) → is-ultrafilter (𝓖 p)
    𝓖-is-ultrafilter p = ultrafilter-image-is-ultrafilter ⌜ 𝕖 p ⌝ 𝓕 i

    II : (p : P) → is-principal (𝓖 p)
    II p = ultrafilters-of-pre-stone-types-are-principal
            (ζ p) (𝓖 p) (𝓖-is-ultrafilter p)

    f : Π Y
    f p = principal-point (II p)

    f-property : (p : P) → 𝓖 p is-principal-at f p
    f-property p = principality (II p)

    III : is-principal 𝓕 → 𝓕 is-principal-at f
    III (g , φ) A = A ϵ 𝓕 ＝⟨ φ A ⟩
                    g ϵ A ＝⟨ ap A (V ⁻¹) ⟩
                    f ϵ A ∎
     where
      V : f ＝ g
      V = dfunext fe VI
       where
        VI : (p : P) → f p ＝ g p
        VI p = pre-stone-types-are-totally-separated (ζ p) VI₀
         where
          VI₀ : (A : Clopen (Y p)) → f p ϵ A ＝ g p ϵ A
          VI₀ A = f p ϵ A  ＝⟨ (f-property p A)⁻¹ ⟩
                  A ϵ 𝓖 p ＝⟨ φ (⌜ 𝕖 p ⌝ ⁻¹[ A ]) ⟩
                  g p ϵ A  ∎

    IV : (A : Clopen (Π Y)) → A ϵ 𝓕 ＝ f ϵ A
    IV A = 𝟚-is-¬¬-separated (A ϵ 𝓕) (f ϵ A) V
     where
      V : ¬¬ (A ϵ 𝓕 ＝ f ϵ A)
      V ν = VI VIII
       where
        VI : ¬¬ (P + ¬ P)
        VI ν' = ν' (inr (λ p → ν' (inl p)))

        VII : P + ¬ P → is-pre-stone-type (Π Y)
        VII (inl p)  = equiv-to-pre-stone-type (𝕖 p) (ζ p)
        VII (inr ν') = equiv-to-pre-stone-type
                        (empty-indexed-product-is-𝟙 fe ν')
                        (𝟙-is-pre-stone-type {𝓤₀})

        VIII : ¬ (P + ¬ P)
        VIII d = ν (III (ultrafilters-of-pre-stone-types-are-principal
                          (VII d) 𝓕 i) A)

\end{code}

If moreover the factors are compact and pointed then the product is a
Stone type, because the micro Tychonoff theorem gives that the product
is itself compact and pointed, and hence Π-compact.

\begin{code}

prop-indexed-products-are-stone-types
 : {P : 𝓤 ̇ } {Y : P → 𝓥 ̇ }
 → is-prop P
 → ((p : P) → is-compact∙ (Y p))
 → ((p : P) → is-pre-stone-type (Y p))
 → is-stone-type (Π Y)
prop-indexed-products-are-stone-types P-is-prop κ ζ
 = prop-indexed-products-are-pre-stone-types P-is-prop ζ ,
   Π-compact-gives-discrete-clopen-algebra
    (compact-types-are-Π-compact
      (compact∙-types-are-compact (micro-tychonoff fe P-is-prop κ)))

\end{code}

In particular, if P is a proposition then the type P → 𝟚 is a
pre-Stone type, and in fact a Stone type, whether or not P is
decidable. The type P → 𝟚 itself is not discrete in general, as the
discreteness of P → 𝟚 for all propositions P amounts to weak excluded
middle, by P→𝟚-discreteness-iff-WEM of the module Taboos.P2. But the
Stone condition concerns the clopens of P → 𝟚 rather than P → 𝟚
itself, and their discreteness amounts to the Π-compactness of P → 𝟚,
which the micro Tychonoff theorem gives.

\begin{code}

P→𝟚-is-pre-stone-type
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-pre-stone-type (P → 𝟚)
P→𝟚-is-pre-stone-type P-is-prop
 = prop-indexed-products-are-pre-stone-types P-is-prop
    (λ _ → stone-types-are-pre-stone-types 𝟚-is-stone-type)

P→𝟚-is-stone-type
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-stone-type (P → 𝟚)
P→𝟚-is-stone-type P-is-prop
 = prop-indexed-products-are-stone-types P-is-prop
    (λ _ → 𝟚-is-compact∙)
    (λ _ → stone-types-are-pre-stone-types 𝟚-is-stone-type)

\end{code}

An ultrafilter of clopens of a sum is determined by the clopens of the
fiber over the point of the base, because two clopens of the sum that
agree on the fiber agree on a clopen of the base that belongs to the
ultrafilter. So the sum is a Stone type as soon as every clopen of
every fiber is the preimage of a clopen of the sum, which we call
having extendable clopens.

\begin{code}

clopens-are-extendable-at : {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) → X → 𝓤 ⊔ 𝓥 ̇
clopens-are-extendable-at {𝓤} {𝓥} {X} Y x =
   (A : Clopen (Y x))
 → Σ B ꞉ Clopen (Σ Y) , ((y : Y x) → (x , y) ϵ B ＝ y ϵ A)

module _ {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } where

 extension-of-clopen : {x : X}
                     → clopens-are-extendable-at Y x
                     → Clopen (Y x)
                     → Clopen (Σ Y)
 extension-of-clopen e A = pr₁ (e A)

 extension-of-clopen-at-fiber
  : {x : X}
    (e : clopens-are-extendable-at Y x)
    (A : Clopen (Y x))
    (y : Y x)
  → (x , y) ϵ extension-of-clopen e A ＝ y ϵ A
 extension-of-clopen-at-fiber e A = pr₂ (e A)

has-extendable-clopens : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
has-extendable-clopens {𝓤} {𝓥} {X} Y =
 (x : X) → clopens-are-extendable-at Y x

\end{code}

The extension of a clopen of a fiber agrees with it on the fiber,
which shows that a sum of totally separated types with extendable
clopens over a totally separated base is totally separated. Without
extendable clopens such a sum is not totally separated in general, as
the general statement gives ¬¬ WLPO by Σ-totally-separated-taboo of
the module TypeTopology.SigmaTotallySeparated.

\begin{code}

Σ-is-totally-separated-if-family-has-extendable-clopens
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-totally-separated X
 → ((x : X) → is-totally-separated (Y x))
 → has-extendable-clopens Y
 → is-totally-separated (Σ Y)
Σ-is-totally-separated-if-family-has-extendable-clopens
 {𝓤} {𝓥} {X} {Y} τ τ' ext {x , y} {x' , y'} φ
 = to-Σ-＝ (I , II)
 where
  I : x ＝ x'
  I = τ (λ C → φ (pr₁ ⁻¹[ C ]))

  II : transport Y I y ＝ y'
  II = τ' x' III
   where
    III : (A : Clopen (Y x')) → transport Y I y ϵ A ＝ y' ϵ A
    III A = transport Y I y ϵ A        ＝⟨ (IV (transport Y I y))⁻¹ ⟩
            (x' , transport Y I y) ϵ B ＝⟨ (ap B (to-Σ-＝ (I , refl)))⁻¹ ⟩
            (x , y) ϵ B                ＝⟨ φ B ⟩
            (x' , y') ϵ B              ＝⟨ IV y' ⟩
            y' ϵ A                     ∎
     where
      B : Clopen (Σ Y)
      B = extension-of-clopen (ext x') A

      IV : (y'' : Y x') → (x' , y'') ϵ B ＝ y'' ϵ A
      IV = extension-of-clopen-at-fiber (ext x') A

\end{code}

If the clopens of each fiber form a discrete type, then the points of
the base at which two clopens of the sum agree on the whole fiber form
a clopen of the base, which we call the agreement of the two clopens.

\begin{code}

module fiberwise-agreement
        {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
        (d : (x : X) → is-discrete (Clopen (Y x)))
       where

 private
  δ : (A B : Clopen (Σ Y)) (x : X)
    → is-decidable ((λ y → (x , y) ϵ A) ＝ (λ y → (x , y) ϵ B))
  δ A B x = d x (λ y → (x , y) ϵ A) (λ y → (x , y) ϵ B)

 agreement : Clopen (Σ Y) → Clopen (Σ Y) → Clopen X
 agreement A B = characteristic-clopen (δ A B)

 agreement-property₀
  : (A B : Clopen (Σ Y)) (x : X)
  → x ∈ agreement A B
  → (y : Y x) → (x , y) ϵ A ＝ (x , y) ϵ B
 agreement-property₀ A B x e
  = happly (characteristic-clopen-property₁ (δ A B) x e)

 agreement-property₁
  : (A B : Clopen (Σ Y)) (x : X)
  → ((y : Y x) → (x , y) ϵ A ＝ (x , y) ϵ B)
  → x ∈ agreement A B
 agreement-property₁ A B x ψ
  = characteristic-clopen-property₂  (δ A B) x (dfunext fe ψ)

\end{code}

We now fix an ultrafilter 𝓕 of clopens of a sum whose image on the
base is the principal ultrafilter at a point x₀. Whether a clopen of
the sum belongs to 𝓕 depends only on its restriction to the fiber
over x₀, because two clopens that agree on this fiber agree on a
clopen of the base that belongs to 𝓕. If moreover the clopens of this
fiber are extendable, then the clopens of the fiber whose extensions
belong to 𝓕 form an ultrafilter, and a clopen of the sum belongs to 𝓕
precisely when its restriction to the fiber belongs to this
ultrafilter.

\begin{code}

module ultrafilter-over-base-point
        {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
        (d : (x : X) → is-discrete (Clopen (Y x)))
        (𝓕 : Clopen (Clopen (Σ Y)))
        (i : is-ultrafilter 𝓕)
        (x₀ : X)
        (φ : (C : Clopen X) → C ϵ ultrafilter-image pr₁ 𝓕 ＝ x₀ ϵ C)
       where

 open ultrafilter-properties 𝓕 i
 open fiberwise-agreement d

 𝓕-depends-only-on-the-fiber
  : (A B : Clopen (Σ Y))
  → ((y : Y x₀) → (x₀ , y) ϵ A ＝ (x₀ , y) ϵ B)
  → A ϵ 𝓕 ＝ B ϵ 𝓕
 𝓕-depends-only-on-the-fiber A B ψ
  = A ϵ 𝓕         ＝⟨ II ⟩
    (D ∩ A) ϵ 𝓕   ＝⟨ ap 𝓕 III ⟩
    (D ∩ B) ϵ 𝓕   ＝⟨ preserves-∧ D B ⟩
    D ϵ 𝓕 ∧ B ϵ 𝓕 ＝⟨ ap (λ - → - ∧ B ϵ 𝓕) I ⟩
    B ϵ 𝓕         ∎
  where
   D : Clopen (Σ Y)
   D = pr₁ ⁻¹[ agreement A B ]

   I : D ∈ 𝓕
   I = D ϵ 𝓕              ＝⟨ φ (agreement A B) ⟩
       x₀ ϵ agreement A B ＝⟨ agreement-property₁ A B x₀ ψ ⟩
       ₁                  ∎

   II : A ϵ 𝓕 ＝ (D ∩ A) ϵ 𝓕
   II = A ϵ 𝓕         ＝⟨ (ap (λ - → - ∧ A ϵ 𝓕) I)⁻¹ ⟩
        D ϵ 𝓕 ∧ A ϵ 𝓕 ＝⟨ (preserves-∧ D A)⁻¹ ⟩
        (D ∩ A) ϵ 𝓕   ∎

   III : D ∩ A ＝ D ∩ B
   III = dfunext fe IV
    where
     IV : (z : Σ Y) → z ϵ (D ∩ A) ＝ z ϵ (D ∩ B)
     IV (x , y) = 𝟚-equality-cases V VI
      where
       V : x ∉ agreement A B
         → (x , y) ϵ (D ∩ A) ＝ (x , y) ϵ (D ∩ B)
       V e = (x , y) ϵ (D ∩ A) ＝⟨ ap (λ - → - ∧ (x , y) ϵ A) e ⟩
             ₀                 ＝⟨ (ap (λ - → - ∧ (x , y) ϵ B) e)⁻¹ ⟩
             (x , y) ϵ (D ∩ B) ∎

       VI : x ∈ agreement A B
          → (x , y) ϵ (D ∩ A) ＝ (x , y) ϵ (D ∩ B)
       VI e = ap (λ - → x ϵ agreement A B ∧ -)
                 (agreement-property₀ A B x e y)

 module ultrafilter-on-the-fiber (e : clopens-are-extendable-at Y x₀) where

  extension : Clopen (Y x₀) → Clopen (Σ Y)
  extension = extension-of-clopen e

  extension-at-fiber : (A : Clopen (Y x₀)) (y : Y x₀)
                     → (x₀ , y) ϵ extension A ＝ y ϵ A
  extension-at-fiber = extension-of-clopen-at-fiber e

  fiber-ultrafilter : Clopen (Clopen (Y x₀))
  fiber-ultrafilter = extension ⁻¹[ 𝓕 ]

  fiber-ultrafilter-value
   : (A : Clopen (Σ Y))
   → A ϵ 𝓕 ＝ (λ y → (x₀ , y) ϵ A) ϵ fiber-ultrafilter
  fiber-ultrafilter-value A
   = 𝓕-depends-only-on-the-fiber
      A
      (extension (λ y → (x₀ , y) ϵ A))
      (λ y → (extension-at-fiber (λ y' → (x₀ , y') ϵ A) y)⁻¹)

  fiber-ultrafilter-is-ultrafilter : is-ultrafilter fiber-ultrafilter
  fiber-ultrafilter-is-ultrafilter
   = I ,
     II ,
     III _∧_ preserves-∧ ,
     III _∨_ preserves-∨
   where
    I : ∅ ∉ fiber-ultrafilter
    I = ∅ ϵ fiber-ultrafilter ＝⟨ (fiber-ultrafilter-value ∅)⁻¹ ⟩
        ∅ ϵ 𝓕                 ＝⟨ preserves-₀ ⟩
        ₀                     ∎

    II : 𝟏 ∈ fiber-ultrafilter
    II = 𝟏 ϵ fiber-ultrafilter ＝⟨ (fiber-ultrafilter-value 𝟏)⁻¹ ⟩
         𝟏 ϵ 𝓕                 ＝⟨ preserves-₁ ⟩
         ₁                     ∎

    III : (_⊛_ : 𝟚 → 𝟚 → 𝟚)
        → ((C D : Clopen (Σ Y)) → (λ z → z ϵ C ⊛ z ϵ D) ϵ 𝓕 ＝ C ϵ 𝓕 ⊛ D ϵ 𝓕)
        → (A B : Clopen (Y x₀))
        → (λ y → y ϵ A ⊛ y ϵ B) ϵ fiber-ultrafilter
        ＝ A ϵ fiber-ultrafilter ⊛ B ϵ fiber-ultrafilter
    III _⊛_ p A B
     = E ϵ fiber-ultrafilter                       ＝⟨ V ⟩
       E' ϵ 𝓕                                      ＝⟨ VI ⟩
       A ϵ fiber-ultrafilter ⊛ B ϵ fiber-ultrafilter ∎
     where
      E : Clopen (Y x₀)
      E y = y ϵ A ⊛ y ϵ B

      E' : Clopen (Σ Y)
      E' z = z ϵ extension A ⊛ z ϵ extension B

      IV : (y : Y x₀) → (x₀ , y) ϵ extension E ＝ (x₀ , y) ϵ E'
      IV y = (x₀ , y) ϵ extension E ＝⟨ IV₀ ⟩
             y ϵ E                  ＝⟨ IV₁ ⟩
             (x₀ , y) ϵ E'          ∎
       where
        IV₀ : (x₀ , y) ϵ extension E ＝ y ϵ E
        IV₀ = extension-at-fiber E y

        IV₁ : y ϵ E ＝ (x₀ , y) ϵ E'
        IV₁ = ap₂ _⊛_ ((extension-at-fiber A y)⁻¹)
                      ((extension-at-fiber B y)⁻¹)

      V : E ϵ fiber-ultrafilter ＝ E' ϵ 𝓕
      V = 𝓕-depends-only-on-the-fiber (extension E) E' IV

      VI : E' ϵ 𝓕 ＝ A ϵ fiber-ultrafilter ⊛ B ϵ fiber-ultrafilter
      VI = p (extension A) (extension B)

\end{code}

So an ultrafilter of clopens of a sum with extendable clopens is
principal, with the point of the base given by the image ultrafilter
and the point of the fiber over it by the ultrafilter of the fiber.

\begin{code}

ultrafilters-of-Σ-are-principal
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-pre-stone-type X
 → ((x : X) → is-stone-type (Y x))
 → has-extendable-clopens Y
 → (𝓕 : Clopen (Clopen (Σ Y)))
 → is-ultrafilter 𝓕
 → is-principal 𝓕
ultrafilters-of-Σ-are-principal {𝓤} {𝓥} {X} {Y} ζ δ ext 𝓕 i
 = (x₀ , y₀) , IV
 where
  I : is-principal (ultrafilter-image pr₁ 𝓕)
  I = ultrafilters-of-pre-stone-types-are-principal
       ζ
       (ultrafilter-image pr₁ 𝓕)
       (ultrafilter-image-is-ultrafilter pr₁ 𝓕 i)

  x₀ : X
  x₀ = principal-point I

  open ultrafilter-over-base-point
        (λ x → stone-types-have-discrete-clopen-algebras (δ x))
        𝓕
        i
        x₀
        (principality I)
  open ultrafilter-on-the-fiber (ext x₀)

  II : is-principal fiber-ultrafilter
  II = ultrafilters-of-pre-stone-types-are-principal
        (stone-types-are-pre-stone-types (δ x₀))
        fiber-ultrafilter
        fiber-ultrafilter-is-ultrafilter

  y₀ : Y x₀
  y₀ = principal-point II

  III : (A : Clopen (Y x₀)) → A ϵ fiber-ultrafilter ＝ y₀ ϵ A
  III = principality II

  IV : (A : Clopen (Σ Y)) → A ϵ 𝓕 ＝ (x₀ , y₀) ϵ A
  IV A = A ϵ 𝓕                  ＝⟨ fiber-ultrafilter-value A ⟩
         A₀ ϵ fiber-ultrafilter ＝⟨ III A₀ ⟩
         (x₀ , y₀) ϵ A          ∎
   where
    A₀ : Clopen (Y x₀)
    A₀ y = (x₀ , y) ϵ A

\end{code}

The clopens of the sum form a discrete type, because the sum of
Π-compact types over a Π-compact base is Π-compact, and with this the
three conditions of the Stone criterion are available.

\begin{code}

Σ-of-stone-types-has-discrete-clopen-algebra
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-stone-type X
 → ((x : X) → is-stone-type (Y x))
 → is-discrete (Clopen (Σ Y))
Σ-of-stone-types-has-discrete-clopen-algebra ζ δ
 = Π-compact-gives-discrete-clopen-algebra
    (Π-compact-closed-under-Σ
      (stone-types-are-Π-compact ζ)
      (λ x → stone-types-are-Π-compact (δ x)))

Σ-is-stone-type-if-family-has-extendable-clopens
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-stone-type X
 → ((x : X) → is-stone-type (Y x))
 → has-extendable-clopens Y
 → is-stone-type (Σ Y)
Σ-is-stone-type-if-family-has-extendable-clopens {𝓤} {𝓥} {X} {Y} ζ δ ext
 = stone-criterion
    (Σ-of-stone-types-has-discrete-clopen-algebra ζ δ)
    (Σ-is-totally-separated-if-family-has-extendable-clopens I II ext)
    (ultrafilters-of-Σ-are-principal (stone-types-are-pre-stone-types ζ) δ ext)
 where
  I : is-totally-separated X
  I = pre-stone-types-are-totally-separated (stone-types-are-pre-stone-types ζ)

  II : (x : X) → is-totally-separated (Y x)
  II x = pre-stone-types-are-totally-separated
          (stone-types-are-pre-stone-types (δ x))

\end{code}

Clopens are extendable at isolated points.

\begin{code}

clopens-are-extendable-at-isolated-points
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
   (x : X)
 → is-isolated x
 → clopens-are-extendable-at Y x
clopens-are-extendable-at-isolated-points {𝓤} {𝓥} {X} {Y} x j A
 = B , III
 where
  I : (x' : X) → is-decidable (x ＝ x') → Clopen (Y x')
  I x' (inl e) y = transport Y (e ⁻¹) y ϵ A
  I x' (inr _) y = ₀

  B : Clopen (Σ Y)
  B (x' , y) = I x' (j x') y

  II : (d : is-decidable (x ＝ x)) (y : Y x) → I x d y ＝ y ϵ A
  II (inl e) y = ap (λ - → transport Y - y ϵ A)
                    (isolated-points-are-h-isolated x j (e ⁻¹) refl)
  II (inr ν) y = 𝟘-elim (ν refl)

  III : (y : Y x) → (x , y) ϵ B ＝ y ϵ A
  III = II (j x)

discrete-bases-extend-clopens
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-discrete X
 → has-extendable-clopens Y
discrete-bases-extend-clopens d x
 = clopens-are-extendable-at-isolated-points x (d x)

\end{code}

A constant family has extendable clopens, so Stone types are closed
under binary products.

\begin{code}

constant-families-have-extendable-clopens
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → has-extendable-clopens (λ (_ : X) → Y)
constant-families-have-extendable-clopens {𝓤} {𝓥} {X} {Y} x A
 = B , (λ y → refl)
 where
  B : Clopen (X × Y)
  B (_ , y) = y ϵ A

×-is-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-stone-type X
 → is-stone-type Y
 → is-stone-type (X × Y)
×-is-stone-type ζ ζ'
 = Σ-is-stone-type-if-family-has-extendable-clopens
    ζ
    (λ _ → ζ')
    constant-families-have-extendable-clopens

\end{code}

A family of propositions that are Stone types has extendable clopens.
Hence the sum of a family of Stone propositions indexed by a Stone
type is a Stone type, and in particular so is a clopen subtype.

\begin{code}

stone-propositions-have-extendable-clopens
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → ((x : X) → is-prop (Y x))
 → ((x : X) → is-stone-type (Y x))
 → has-extendable-clopens Y
stone-propositions-have-extendable-clopens {𝓤} {𝓥} {X} {Y} i δ x A
 = I (stone-props-are-decidable (i x) (δ x))
 where
  I : is-decidable (Y x)
    → Σ B ꞉ Clopen (Σ Y) , ((y : Y x) → (x , y) ϵ B ＝ y ϵ A)
  I (inl y₁) = (λ _ → y₁ ϵ A) , (λ y → ap A (i x y₁ y))
  I (inr ν)  = ∅ , (λ y → 𝟘-elim (ν y))

Σ-of-stone-propositions-is-stone-type
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-stone-type X
 → ((x : X) → is-prop (Y x))
 → ((x : X) → is-stone-type (Y x))
 → is-stone-type (Σ Y)
Σ-of-stone-propositions-is-stone-type ζ i δ
 = Σ-is-stone-type-if-family-has-extendable-clopens
    ζ
    δ
    (stone-propositions-have-extendable-clopens i δ)

clopen-subtypes-of-stone-types-are-stone-types
 : {X : 𝓤 ̇ }
 → is-stone-type X
 → (A : Clopen X)
 → is-stone-type (clopen-subtype A)
clopen-subtypes-of-stone-types-are-stone-types ζ A
 = Σ-of-stone-propositions-is-stone-type
    ζ
    (λ _ → 𝟚-is-set)
    (λ x → decidable-props-are-stone-types
            𝟚-is-set
            (∈-is-decidable x A))

\end{code}

A clopen subtype inherits the pre-Stone property.

\begin{code}

clopen-subtypes-of-pre-stone-types-are-pre-stone-types
 : {X : 𝓤 ̇ }
 → is-pre-stone-type X
 → (A : Clopen X)
 → is-pre-stone-type (clopen-subtype A)
clopen-subtypes-of-pre-stone-types-are-pre-stone-types {𝓤} {X} ζ A
 = pre-stone-criterion I II
 where
  σ : (x : X) → x ∈ A → clopen-subtype A
  σ x d = (x , d)

  open clopen-extension A σ

  I : is-totally-separated (clopen-subtype A)
  I = embedding-into-totally-separated-gives-totally-separated
       (clopen-subtype-inclusion A)
       (clopen-subtype-inclusion-is-embedding A)
       (pre-stone-types-are-totally-separated ζ)

  II : (𝓕 : Clopen (Clopen (clopen-subtype A)))
     → is-ultrafilter 𝓕
     → is-principal 𝓕
  II 𝓕 i = IV (ultrafilters-of-pre-stone-types-are-principal ζ 𝓖 III)
   where
    open ultrafilter-properties 𝓕 i

    𝓖 : Clopen (Clopen X)
    𝓖 = ultrafilter-image (clopen-subtype-inclusion A) 𝓕

    III : is-ultrafilter 𝓖
    III = ultrafilter-image-is-ultrafilter (clopen-subtype-inclusion A) 𝓕 i

    IV : is-principal 𝓖 → is-principal 𝓕
    IV (x₀ , V) = (x₀ , VI) , VIII
     where
      VI : x₀ ∈ A
      VI = x₀ ϵ A ＝⟨ (V A)⁻¹ ⟩
           A ϵ 𝓖  ＝⟨ ap 𝓕 (self-restriction-is-𝟏 A) ⟩
           𝟏 ϵ 𝓕  ＝⟨ preserves-₁ ⟩
           ₁      ∎

      VII : (C : Clopen (clopen-subtype A)) → ext C ↾ A ＝ C
      VII C = dfunext fe (λ (x , d) → ext-at-section C x d)

      VIII : (C : Clopen (clopen-subtype A)) → C ϵ 𝓕 ＝ (x₀ , VI) ϵ C
      VIII C = C ϵ 𝓕         ＝⟨ ap 𝓕 (VII C)⁻¹ ⟩
               ext C ϵ 𝓖     ＝⟨ V (ext C) ⟩
               x₀ ϵ ext C    ＝⟨ ext-at-section C x₀ VI ⟩
               (x₀ , VI) ϵ C ∎

\end{code}

We now turn to ℕ∞. For a natural number n, the clopen ↑ n is the upper
set of n in ℕ∞.

\begin{code}

infix 50 ↑_

↑_ : ℕ → Clopen ℕ∞
↑ n = λ x → ι x n

\end{code}

For a natural number k, the clopen `singleton k` is the characteristic
function of the singleton subset containing the point ι k.

\begin{code}

singleton : ℕ → Clopen ℕ∞
singleton 0        = complement (↑ 0)
singleton (succ j) = ↑ j ∩ complement (↑ (succ j))

singleton-property₀ : (k : ℕ) (x : ℕ∞) → x ∈ singleton k → x ＝ ι k
singleton-property₀ 0 x e = is-Zero-equal-Zero fe (complement-lc (ι x 0) ₀ e)
singleton-property₀ (succ j) x e =
 Succ-criterion fe
  (Lemma[min𝟚ab＝₁→a＝₁] e)
  (complement-lc (ι x (succ j)) ₀ (Lemma[min𝟚ab＝₁→b＝₁] e))

singleton-property₁ : (k : ℕ) → ι k ∈ singleton k
singleton-property₁ 0        = ap ⇁_ (ℕ-to-ℕ∞-diagonal₀ 0)
singleton-property₁ (succ j) =
 Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
  (ℕ-to-ℕ∞-diagonal₁ j)
  (ap ⇁_ (ℕ-to-ℕ∞-diagonal₀ (succ j)))

\end{code}

A modulus of a clopen A of ℕ∞ is an m : ℕ such that for all n ≥ m we
have that ι n ϵ A if and only if ∞ ϵ A. This is the notion of
continuity of the module TypeTopology.DecidabilityOfNonContinuity,
formulated with the order of ℕ rather than with maximum, and for
𝟚-valued rather than ℕ-valued functions. If ¬ WLPO holds then no
clopen of ℕ∞ fails to have a modulus, and this is how we use the
hypothesis.

\begin{code}

_is-modulus-of_ : ℕ → Clopen ℕ∞ → 𝓤₀ ̇
m is-modulus-of A = (n : ℕ) → m ≤ n → ι n ϵ A ＝ ∞ ϵ A

has-modulus : Clopen ℕ∞ → 𝓤₀ ̇
has-modulus A = Σ m ꞉ ℕ , m is-modulus-of A

¬WLPO-gives-¬¬-has-modulus : ¬ WLPO → (A : Clopen ℕ∞) → ¬¬ has-modulus A
¬WLPO-gives-¬¬-has-modulus nwlpo A = ¬¬-functor II I
 where
  g : 𝟚 → ℕ
  g ₀ = 0
  g ₁ = 1

  g-lc : {b c : 𝟚} → g b ＝ g c → b ＝ c
  g-lc {₀} {₀} r = refl
  g-lc {₀} {₁} r = 𝟘-elim (zero-not-positive 0 r)
  g-lc {₁} {₀} r = 𝟘-elim (zero-not-positive 0 (r ⁻¹))
  g-lc {₁} {₁} r = refl

  f : ℕ∞ → ℕ
  f = g ∘ A

  I : ¬¬ continuous f
  I = ¬WLPO-gives-all-functions-are-not-not-continuous nwlpo f

  II : continuous f → has-modulus A
  II (m , ψ) = m , III
   where
    III : (n : ℕ) → m ≤ n → ι n ϵ A ＝ ∞ ϵ A
    III n l = g-lc (f (ι n)             ＝⟨ ap f (IV ⁻¹) ⟩
                    f (max (ι m) (ι n)) ＝⟨ ψ n ⟩
                    f ∞                 ∎)
     where
      IV : max (ι m) (ι n) ＝ ι n
      IV = max (ι m) (ι n) ＝⟨ (max-fin fe m n)⁻¹ ⟩
           ι (maxℕ m n)    ＝⟨ ap ℕ-to-ℕ∞ (max-ord→ m n l) ⟩
           ι n             ∎

\end{code}

Given an ultrafilter 𝓕 of the clopens of ℕ∞, the sequence of values of
𝓕 at the upper sets is decreasing, and so it is an element u of ℕ∞,
with which 𝓕 agrees on the upper sets by construction.

\begin{code}

module ultrafilter-on-ℕ∞
        (𝓕 : Clopen (Clopen ℕ∞))
        (i : is-ultrafilter 𝓕)
       where

 open ultrafilter-properties 𝓕 i

 private
  α : ℕ → 𝟚
  α n = ↑ n ϵ 𝓕

  α-is-decreasing : is-decreasing α
  α-is-decreasing n = monotone I
   where
    I : ↑ (succ n) ⊆ ↑ n
    I (β , d) = ≤₂-criterion-converse (d n)

 u : ℕ∞
 u = (α , α-is-decreasing)

 _ : (n : ℕ) → ↑ n ϵ 𝓕 ＝ u ϵ ↑ n
 _ = λ n → refl

\end{code}

If u is finite, say u ＝ ι k, then `singleton k` belongs to 𝓕, and the
only point belonging to `singleton k` is ι k. So the criterion above
applies with the one-point type, and 𝓕 is principal at u.

\begin{code}

 private
  𝓕-at-singleton : (k : ℕ) → u ＝ ι k → singleton k ∈ 𝓕
  𝓕-at-singleton 0 e =
   singleton 0 ϵ 𝓕 ＝⟨ preserves-complement (↑ 0) ⟩
   ⇁ (α 0)         ＝⟨ ap ⇁_ I ⟩
   ⇁ ₀             ＝⟨refl⟩
   ₁               ∎
    where
     I : α 0 ＝ ₀
     I = α 0       ＝⟨ ap (λ - → ι - 0) e ⟩
         ι (ι 0) 0 ＝⟨ ℕ-to-ℕ∞-diagonal₀ 0 ⟩
         ₀         ∎
  𝓕-at-singleton (succ j) e =
   singleton (succ j) ϵ 𝓕            ＝⟨ I ⟩
   α j ∧ complement (↑ (succ j)) ϵ 𝓕 ＝⟨ II ⟩
   α j ∧ ⇁ (α (succ j))              ＝⟨ V ⟩
   ₁ ∧ ⇁ ₀                           ＝⟨refl⟩
   ₁                                 ∎
    where
     I = preserves-∧ (↑ j) (complement (↑ (succ j)))
     II = ap (λ - → α j ∧ -) (preserves-complement (↑ (succ j)))

     III : α j ＝ ₁
     III = α j              ＝⟨ ap (λ - → ι - j) e ⟩
           ι (ι (succ j)) j ＝⟨ ℕ-to-ℕ∞-diagonal₁ j ⟩
           ₁                ∎

     IV : α (succ j) ＝ ₀
     IV = α (succ j)              ＝⟨ ap (λ - → ι - (succ j)) e ⟩
          ι (ι (succ j)) (succ j) ＝⟨ ℕ-to-ℕ∞-diagonal₀ (succ j) ⟩
          ₀                       ∎

     V = ap₂ (λ - -' → - ∧ ⇁ -') III IV

 𝓕-at-finite : (k : ℕ) → u ＝ ι k → 𝓕 is-principal-at u
 𝓕-at-finite k e A = III
  where
   j : 𝟙 {𝓤₀} → ℕ∞
   j _ = ι k

   σ : (x : ℕ∞) → x ∈ singleton k → 𝟙 {𝓤₀}
   σ _ _ = ⋆

   jσ : (x : ℕ∞) (d : x ∈ singleton k) → j (σ x d) ＝ x
   jσ x d = (singleton-property₀ k x d)⁻¹

   I : Σ y ꞉ 𝟙 {𝓤₀} , 𝓕 is-principal-at ι k
   I = ultrafilter-principality-criterion
        (singleton k) j σ jσ (𝟙-is-pre-stone-type {𝓤₀}) 𝓕 i
        (𝓕-at-singleton k e)

   II : 𝓕 is-principal-at ι k
   II = pr₂ I

   III : A ϵ 𝓕 ＝ u ϵ A
   III = A ϵ 𝓕   ＝⟨ II A ⟩
         ι k ϵ A ＝⟨ (ap A e)⁻¹ ⟩
         u ϵ A   ∎

 not-principal-at-u-gives-u-is-∞ : (A : Clopen ℕ∞) → A ϵ 𝓕 ≠ u ϵ A → u ＝ ∞
 not-principal-at-u-gives-u-is-∞ A ν =
  not-finite-is-∞ fe (λ k e → ν (𝓕-at-finite k e A))

\end{code}

If u is the point at infinity, then every upper set belongs to 𝓕, and
the same holds for an ultrafilter that is not principal.

\begin{code}

 𝓕-at-upper-sets : u ＝ ∞ → (n : ℕ) → ↑ n ∈ 𝓕
 𝓕-at-upper-sets e n = ap (λ - → ι - n) e

 _ : (A : Clopen ℕ∞) → A ϵ 𝓕 ≠ u ϵ A → (n : ℕ) → ↑ n ∈ 𝓕
 _ = λ A ν → 𝓕-at-upper-sets (not-principal-at-u-gives-u-is-∞ A ν)

 private
  clopens-containing-∞-are-in-𝓕
   : u ＝ ∞
   → (A : Clopen ℕ∞) (m : ℕ)
   → m is-modulus-of A
   → ∞ ∈ A
   → A ∈ 𝓕
  clopens-containing-∞-are-in-𝓕 e A m φ r =
   upper-closed II (𝓕-at-upper-sets e m)
   where
    I : (x : ℕ∞) → x ∈ complement (↑ m) ∪ A
    I = ℕ∞-𝟚-density fe III (max𝟚-lemma-converse (inr r))
     where
      III : (n : ℕ) → ι n ∈ complement (↑ m) ∪ A
      III n = 𝟚-equality-cases
               (λ (s : ι (ι n) m ＝ ₀)
                   → max𝟚-lemma-converse (inl (ap ⇁_ s)))
               (λ (s : ι (ι n) m ＝ ₁)
                   → max𝟚-lemma-converse (inr (IV s)))
       where
        IV : ι (ι n) m ＝ ₁ → ι n ∈ A
        IV s = ι n ϵ A ＝⟨ φ n (<-coarser-than-≤ m n (⊏-gives-< m n s)) ⟩
               ∞ ϵ A   ＝⟨ r ⟩
               ₁       ∎

    II : ↑ m ⊆ A
    II x s = x ϵ A               ＝⟨refl⟩
             ₀ ∨ x ϵ A           ＝⟨ III ⟩
             ⇁ (x ϵ ↑ m) ∨ x ϵ A ＝⟨ I x ⟩
             ₁                   ∎
     where
      III = ap (λ - → ⇁ - ∨ x ϵ A) (s ⁻¹)

 𝓕-at-∞ : u ＝ ∞
        → (A : Clopen ℕ∞) (m : ℕ)
        → m is-modulus-of A
        → A ϵ 𝓕 ＝ u ϵ A
 𝓕-at-∞ e A m φ = 𝟚-equality-cases II III
  where
   I : u ϵ A ＝ ∞ ϵ A
   I = ap A e

   II : ∞ ∉ A → A ϵ 𝓕 ＝ u ϵ A
   II r = A ϵ 𝓕 ＝⟨ V ⟩
          ₀     ＝⟨ r ⁻¹ ⟩
          ∞ ϵ A ＝⟨ I ⁻¹ ⟩
          u ϵ A ∎
    where
     IV : complement A ∈ 𝓕
     IV = clopens-containing-∞-are-in-𝓕 e (complement A) m
           (λ n l → ap ⇁_ (φ n l))
           (ap ⇁_ r)

     V : A ∉ 𝓕
     V = complement-lc (A ϵ 𝓕) ₀
          (⇁ (A ϵ 𝓕)        ＝⟨ (preserves-complement A)⁻¹ ⟩
           complement A ϵ 𝓕 ＝⟨ IV ⟩
           ₁                ＝⟨refl⟩
           ⇁ ₀              ∎)

   III : ∞ ∈ A → A ϵ 𝓕 ＝ u ϵ A
   III r = A ϵ 𝓕 ＝⟨ clopens-containing-∞-are-in-𝓕 e A m φ r ⟩
           ₁     ＝⟨ r ⁻¹ ⟩
           ∞ ϵ A ＝⟨ I ⁻¹ ⟩
           u ϵ A ∎

\end{code}

Putting the two cases together, 𝓕 is principal at u as soon as it is
principal at ∞ when u is ∞, which is the following criterion, and if
¬ WLPO holds then the criterion applies.

\begin{code}

 𝓕-is-principal-at-u-criterion
  : (u ＝ ∞ → 𝓕 is-principal-at ∞)
  → 𝓕 is-principal-at u
 𝓕-is-principal-at-u-criterion ψ A
  = 𝟚-is-¬¬-separated (A ϵ 𝓕) (u ϵ A) I
  where
   I : ¬¬ (A ϵ 𝓕 ＝ u ϵ A)
   I ν = ν (A ϵ 𝓕 ＝⟨ ψ II A ⟩
            ∞ ϵ A ＝⟨ (ap A II)⁻¹ ⟩
            u ϵ A ∎)
    where
     II : u ＝ ∞
     II = not-principal-at-u-gives-u-is-∞ A ν

 𝓕-is-principal-at-u : ¬ WLPO → 𝓕 is-principal-at u
 𝓕-is-principal-at-u nwlpo = 𝓕-is-principal-at-u-criterion I
  where
   I : u ＝ ∞ → 𝓕 is-principal-at ∞
   I e A = 𝟚-is-¬¬-separated (A ϵ 𝓕) (∞ ϵ A) II
    where
     II : ¬¬ (A ϵ 𝓕 ＝ ∞ ϵ A)
     II ν = ¬WLPO-gives-¬¬-has-modulus nwlpo A III
      where
       III : ¬ has-modulus A
       III (m , φ) = ν (A ϵ 𝓕 ＝⟨ 𝓕-at-∞ e A m φ ⟩
                        u ϵ A ＝⟨ ap A e ⟩
                        ∞ ϵ A ∎)

\end{code}

The clopens of ℕ∞ form a discrete type, as ℕ∞ is compact, so that ℕ∞
is a Stone type precisely when it is a pre-Stone type. The criterion
above, applied to the discreteness of the clopens and to the total
separatedness of ℕ∞, now gives that ℕ∞ is a Stone type if ¬ WLPO
holds.

\begin{code}

ℕ∞-has-a-discrete-clopen-algebra : is-discrete (Clopen ℕ∞)
ℕ∞-has-a-discrete-clopen-algebra
 = Π-compact-gives-discrete-clopen-algebra
    (compact-types-are-Π-compact ℕ∞-compact)

ℕ∞-is-stone-type : ¬ WLPO → is-stone-type ℕ∞
ℕ∞-is-stone-type nwlpo =
 stone-criterion
  ℕ∞-has-a-discrete-clopen-algebra
  (ℕ∞-is-totally-separated fe)
  I
 where
  I : (𝓕 : Clopen (Clopen ℕ∞)) (i : is-ultrafilter 𝓕)
    → is-principal 𝓕
  I 𝓕 i = u , 𝓕-is-principal-at-u nwlpo
   where
    open ultrafilter-on-ℕ∞ 𝓕 i

\end{code}

The module Ordinals.BrouwerCodesGiveStoneTypes generalizes the above
result for ℕ∞, again assuming that ¬ WLPO holds, to the compact
totally separated interpretation of the Brouwer ordinal codes, of
which ℕ∞ is the interpretation of the code for the first infinite
ordinal.

We now discuss the assumption ¬ WLPO for the above result. With no
assumptions, we have that ℕ∞ is a Stone type precisely when every
ultrafilter that contains all the upper sets is principal at ∞.

\begin{code}

Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞ : 𝓤₀ ̇
Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞ =
   (𝓕 : Clopen (Clopen ℕ∞))
 → is-ultrafilter 𝓕
 → ((n : ℕ) → ↑ n ∈ 𝓕)
 → 𝓕 is-principal-at ∞

stone-gives-principal-at-∞
 : is-stone-type ℕ∞
 → Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞
stone-gives-principal-at-∞ ζ 𝓕 i ψ
 = I (ultrafilters-of-pre-stone-types-are-principal
       (stone-types-are-pre-stone-types ζ) 𝓕 i)
 where
  I : is-principal 𝓕 → 𝓕 is-principal-at ∞
  I (u , φ) A = A ϵ 𝓕 ＝⟨ φ A ⟩
                u ϵ A ＝⟨ ap A II ⟩
                ∞ ϵ A ∎
   where
    II : u ＝ ∞
    II = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe III)
     where
      III : (n : ℕ) → ι u n ＝ ι ∞ n
      III n = ι u n   ＝⟨ (φ (↑ n))⁻¹ ⟩
              ↑ n ϵ 𝓕 ＝⟨ ψ n ⟩
              ₁       ＝⟨refl⟩
              ι ∞ n   ∎

principal-at-∞-gives-stone
 : Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞
 → is-stone-type ℕ∞
principal-at-∞-gives-stone φ
 = stone-criterion
    ℕ∞-has-a-discrete-clopen-algebra
    (ℕ∞-is-totally-separated fe)
    I
 where
  I : (𝓕 : Clopen (Clopen ℕ∞)) (i : is-ultrafilter 𝓕)
    → is-principal 𝓕
  I 𝓕 i = u , 𝓕-is-principal-at-u-criterion (λ e → φ 𝓕 i (𝓕-at-upper-sets e))
   where
    open ultrafilter-on-ℕ∞ 𝓕 i

ℕ∞-is-stone-type-iff-principal-at-∞
 : is-stone-type ℕ∞
 ↔ Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞
ℕ∞-is-stone-type-iff-principal-at-∞
 = stone-gives-principal-at-∞ ,
   principal-at-∞-gives-stone

\end{code}

That ℕ∞ is a Stone type is not provable without a further hypothesis
such as ¬ WLPO. With choice there is a nonprincipal ultrafilter on ℕ,
which is an ultrafilter of the clopens of ℕ∞ that is not principal at
any point, so that ℕ∞ is not a Stone type in such a model. That ¬ WLPO
holds is sufficient for ℕ∞ to be a Stone type, but it is not
necessary. It is consistent with ZF that every ultrafilter on every
set is principal, by a model of Blass [2] where the ultrafilters on ℕ
are all principal. In the model of Blass excluded middle holds, and
hence so does WLPO, and ℕ∞ is the set ℕ + 𝟙. Every subset of ℕ + 𝟙 is
decidable, so the clopens of ℕ∞ are the characteristic functions of
all the subsets of ℕ + 𝟙, and the ultrafilters of the clopens are the
ultrafilters of the powerset of ℕ + 𝟙, which are all principal. So ℕ∞
is a Stone type in that model.

We now show that if every pre-Stone type is a Stone type then WEM
holds. The first step is that the emptiness of a Π-compact type is
decidable, which is negations-of-Π-compact-types-are-decidable of
TypeTopology.WeaklyCompactTypes.

\begin{code}

Pre-Stone-Types-Are-Stone-Types : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pre-Stone-Types-Are-Stone-Types 𝓤 =
   (X : 𝓤 ̇ )
 → is-pre-stone-type X
 → is-stone-type X

pre-stone-types-are-stone-types-gives-WEM
 : Pre-Stone-Types-Are-Stone-Types 𝓤
 → WEM 𝓤
pre-stone-types-are-stone-types-gives-WEM c Q Q-is-prop
 = I (negations-of-Π-compact-types-are-decidable (¬ Q)
      (stone-types-are-Π-compact
       (c (¬ Q)
          (¬¬-stable-props-are-pre-stone-types
            (negations-are-props fe)
            three-negations-imply-one))))
 where
  I : is-decidable (¬ (¬ Q)) → ¬ Q + ¬¬ Q
  I (inl nnq) = inr nnq
  I (inr f)   = inl (three-negations-imply-one f)

\end{code}

We now show that if ¬ WLPO holds then Stone types are **not** closed
under Σ. A counterexample is the type ℕ∞₂ of the module
TypeTopology.FailureOfTotalSeparatedness, whose total separatedness
gives ¬¬ WLPO. Its base ℕ∞ is a Stone type when ¬ WLPO holds, and its
fibers are of the form P → 𝟚 for a proposition P and hence are Stone
types, so that the closure would make ℕ∞₂ a pre-Stone type and hence
totally separated.

\begin{code}

open import TypeTopology.FailureOfTotalSeparatedness fe

Stone-Types-Are-Closed-Under-Σ : 𝓤₁ ̇
Stone-Types-Are-Closed-Under-Σ =
   (X : 𝓤₀ ̇ ) (Y : X → 𝓤₀ ̇ )
 → is-stone-type X
 → ((x : X) → is-stone-type (Y x))
 → is-stone-type (Σ Y)

closure-under-Σ-gives-¬¬-WLPO
 : Stone-Types-Are-Closed-Under-Σ
 → ¬¬ WLPO
closure-under-Σ-gives-¬¬-WLPO c nwlpo
 = ℕ∞₂-is-not-totally-separated-in-general I nwlpo
 where
  I : is-totally-separated ℕ∞₂
  I = pre-stone-types-are-totally-separated
       (stone-types-are-pre-stone-types
         (c ℕ∞
            (λ u → u ＝ ∞ → 𝟚)
            (ℕ∞-is-stone-type nwlpo)
            (λ u → P→𝟚-is-stone-type (ℕ∞-is-set fe))))

¬WLPO-gives-failure-of-closure-under-Σ
 : ¬ WLPO
 → ¬ Stone-Types-Are-Closed-Under-Σ
¬WLPO-gives-failure-of-closure-under-Σ nwlpo c
 = closure-under-Σ-gives-¬¬-WLPO c nwlpo

\end{code}

The Stone types of [1] **are** closed under Σ, by their Theorem 4.18,
but the notion of a Stone type considered there is not the same as
ours. The Stone spaces there are the spectra of countably presented
boolean algebras, and the boolean algebra of clopens of such a space
is overtly discrete, by their Corollary 2.14, so that the equality of
two clopens is open rather than decidable, and becomes decidable only
when it is closed as well, by their Corollary 1.22. So their Stone
spaces are not Π-compact in general, whereas our definition includes
Π-compactness via the discreteness of the type of clopens. Their proof
of the closure under Σ appeals to their Axiom 3, local choice, in
their Lemma 4.11, to replace data that varies pointwise over the base
by data uniform in the base. Our definition lacks precisely that, as
we saw above, where a sum of Stone types over a Stone type is a Stone
type when the clopens of the fibers are preimages of clopens of the
sum, and the condition fails in general when ¬ WLPO holds.

Coming back to our setting, the pre-Stone types are not closed under Σ
either, when ¬ WLPO holds, because their closure under Σ gives that of
the Stone types, the discreteness of the clopens of a sum coming from
the Π-compactness of the base and of the fibers.

\begin{code}

Pre-Stone-Types-Are-Closed-Under-Σ : 𝓤₁ ̇
Pre-Stone-Types-Are-Closed-Under-Σ =
   (X : 𝓤₀ ̇ ) (Y : X → 𝓤₀ ̇ )
 → is-pre-stone-type X
 → ((x : X) → is-pre-stone-type (Y x))
 → is-pre-stone-type (Σ Y)

pre-stone-closure-under-Σ-gives-stone-closure-under-Σ
 : Pre-Stone-Types-Are-Closed-Under-Σ
 → Stone-Types-Are-Closed-Under-Σ
pre-stone-closure-under-Σ-gives-stone-closure-under-Σ c X Y ζ δ
 = c X Y
    (stone-types-are-pre-stone-types ζ)
    (λ x → stone-types-are-pre-stone-types (δ x)) ,
   Π-compact-gives-discrete-clopen-algebra
    (Π-compact-closed-under-Σ
      (stone-types-are-Π-compact ζ)
      (λ x → stone-types-are-Π-compact (δ x)))

¬WLPO-gives-failure-of-closure-under-Σ-for-pre-stone-types
 : ¬ WLPO
 → ¬ Pre-Stone-Types-Are-Closed-Under-Σ
¬WLPO-gives-failure-of-closure-under-Σ-for-pre-stone-types nwlpo c
 = ¬WLPO-gives-failure-of-closure-under-Σ nwlpo
    (pre-stone-closure-under-Σ-gives-stone-closure-under-Σ c)

\end{code}

We can't drop the extendability of the clopens from the closure under
Σ proved above when ¬ WLPO holds, because the above counterexample ℕ∞₂
is a sum of Stone types over a Stone type.

\begin{code}

¬WLPO-gives-clopens-are-not-always-extendable
 : ¬ WLPO
 → ¬ has-extendable-clopens (λ (u : ℕ∞) → u ＝ ∞ → 𝟚)
¬WLPO-gives-clopens-are-not-always-extendable nwlpo ext
 = ℕ∞₂-is-not-totally-separated-in-general I nwlpo
 where
  I : is-totally-separated ℕ∞₂
  I = pre-stone-types-are-totally-separated
       (stone-types-are-pre-stone-types
         (Σ-is-stone-type-if-family-has-extendable-clopens
           (ℕ∞-is-stone-type nwlpo)
           (λ u → P→𝟚-is-stone-type (ℕ∞-is-set fe))
           ext))

\end{code}

A compact type is Π-compact, so a compact totally separated type is a
Stone type as soon as it is a pre-Stone type, which says that every
ultrafilter is principal. So the statement that every compact totally
separated type is a Stone type contradicts choice. It gives that no
ultrafilter of clopens of such a type is nonprincipal, and ℕ∞ is
compact and totally separated, whereas with choice there is a
nonprincipal ultrafilter of the clopens of ℕ∞, as discussed above.
Hence that every compact totally separated type is a Stone type fails
in every model of choice, and so is not provable under our
assumptions.

\begin{code}

Compact-Totally-Separated-Types-Are-Stone-Types : (𝓤 : Universe) → 𝓤 ⁺ ̇
Compact-Totally-Separated-Types-Are-Stone-Types 𝓤 =
   (X : 𝓤 ̇ )
 → is-compact X
 → is-totally-separated X
 → is-stone-type X

ultrafilters-on-compact-totally-separated-types-are-principal
 : Compact-Totally-Separated-Types-Are-Stone-Types 𝓤
 → (X : 𝓤 ̇ )
 → is-compact X
 → is-totally-separated X
 → (𝓕 : Clopen (Clopen X))
 → is-ultrafilter 𝓕
 → is-principal 𝓕
ultrafilters-on-compact-totally-separated-types-are-principal c X κ τ 𝓕 i
 = ultrafilters-of-pre-stone-types-are-principal
    (stone-types-are-pre-stone-types (c X κ τ)) 𝓕 i

ultrafilters-on-ℕ∞-are-principal
 : Compact-Totally-Separated-Types-Are-Stone-Types 𝓤₀
 → (𝓕 : Clopen (Clopen ℕ∞))
 → is-ultrafilter 𝓕
 → is-principal 𝓕
ultrafilters-on-ℕ∞-are-principal c
 = ultrafilters-on-compact-totally-separated-types-are-principal
    c
    ℕ∞
    ℕ∞-compact
    (ℕ∞-is-totally-separated fe)

nonprincipal-ultrafilter-on-ℕ∞-gives-failure
 : (𝓕 : Clopen (Clopen ℕ∞))
 → is-ultrafilter 𝓕
 → is-nonprincipal 𝓕
 → ¬ Compact-Totally-Separated-Types-Are-Stone-Types 𝓤₀
nonprincipal-ultrafilter-on-ℕ∞-gives-failure 𝓕 i ν c
 = ν (ultrafilters-on-ℕ∞-are-principal c 𝓕 i)

\end{code}
