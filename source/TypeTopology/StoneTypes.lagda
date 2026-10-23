Martin Escardo, 21st October 2026.

We discuss a notion of Stone type and show as an example that ℕ∞ is a
Stone type, assuming ¬ WLPO. We also discuss that this cannot be
proved without such an assumption. The hypothesis ¬ WLPO can be
regarded as a weak continuity principle. It is equivalent to the
doubly negated continuity of every function of ℕ∞ into a discrete
type, by the module TypeTopology.DecidabilityOfNonContinuity.

Our notion of Stone type is a variant of that of [1], and we compare
them below.

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
fiber is the restriction of a clopen of the sum, which holds at the
isolated points of the base, for a constant family, giving the closure
under binary products, and for a family of propositions.

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
 renaming (_≤̇_ to infix 30 _⊆_)
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
 infix  45 _ϵ_
 infix  35 _∈_
 infix  35 _∉_

 _ϵ_ : X → Clopen X → 𝟚
 x ϵ A = A x

 _∈_ : X → Clopen X → 𝓤₀ ̇
 x ∈ A = x ϵ A ＝ ₁

 _∉_ : X → Clopen X → 𝓤₀ ̇
 x ∉ A = x ϵ A ＝ ₀

 ∈-is-decidable : (x : X) (A : Clopen X) → is-decidable (x ∈ A)
 ∈-is-decidable x A = 𝟚-is-discrete (x ϵ A) ₁

 ∅ : Clopen X
 ∅ _ = ₀

 𝟏 : Clopen X
 𝟏 _ = ₁

 _∩_ : Clopen X → Clopen X → Clopen X
 (A ∩ B) x = x ϵ A ∧ x ϵ B

 _∪_ : Clopen X → Clopen X → Clopen X
 (A ∪ B) x = x ϵ A ∨ x ϵ B

 complement : Clopen X → Clopen X
 complement A x = ⇁ (x ϵ A)

\end{code}

We now define the subtype of X classified by a clopen, whose inclusion
into X is an embedding, as membership is a proposition.

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

restriction-to-clopen-subtype-is-𝟏
 : {X : 𝓤 ̇ } (A : Clopen X)
 → A ∘ clopen-subtype-inclusion A ＝ 𝟏
restriction-to-clopen-subtype-is-𝟏 A
 = dfunext fe (clopen-subtype-membership A)

\end{code}

An ultrafilter of the boolean algebra of clopens of X is a boolean
algebra homomorphism into 𝟚, and hence in particular a clopen of the
clopens of X, so that the notation above applies to it.

\begin{code}

is-ultrafilter : {X : 𝓤 ̇ } → Clopen (Clopen X) → 𝓤 ̇
is-ultrafilter {𝓤} {X} ℱ = (∅ ∉ ℱ)
                         × (𝟏 ∈ ℱ)
                         × ((A B : Clopen X) → (A ∩ B) ϵ ℱ ＝ A ϵ ℱ ∧ B ϵ ℱ)
                         × ((A B : Clopen X) → (A ∪ B) ϵ ℱ ＝ A ϵ ℱ ∨ B ϵ ℱ)

being-ultrafilter-is-prop : {X : 𝓤 ̇ } (ℱ : Clopen (Clopen X))
                          → is-prop (is-ultrafilter ℱ)
being-ultrafilter-is-prop {𝓤} {X} ℱ =
 ×₄-is-prop
  𝟚-is-set
  𝟚-is-set
  (Π₂-is-prop fe (λ A B → 𝟚-is-set))
  (Π₂-is-prop fe (λ A B → 𝟚-is-set))

\end{code}

A clopen of clopens of X is principal when it consists of the clopen
neighbourhoods of a point. We use the name for arbitrary clopens of
clopens, although we apply it only to ultrafilters.

\begin{code}

is-principal : {X : 𝓤 ̇ } → Clopen (Clopen X) → 𝓤 ̇
is-principal {𝓤} {X} ℱ = Σ x ꞉ X , ((A : Clopen X) → A ϵ ℱ ＝ x ϵ A)

is-nonprincipal : {X : 𝓤 ̇ } → Clopen (Clopen X) → 𝓤 ̇
is-nonprincipal ℱ = ¬ is-principal ℱ

\end{code}

Being principal is a proposition precisely when X is totally separated
in the sense of TypeTopology.TotallySeparated. A point witnessing that
a clopen of clopens is principal is unique when the clopens separate
the points of X, and conversely two points with the same clopens both
witness that the clopen neighbourhoods of the first of them are
principal.

\begin{code}

totally-separated-gives-being-principal-is-prop
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → (ℱ : Clopen (Clopen X))
 → is-prop (is-principal ℱ)
totally-separated-gives-being-principal-is-prop {𝓤} {X} τ ℱ (x , φ) (y , ψ)
 = to-subtype-＝ I II
 where
  I : (x : X) → is-prop ((A : Clopen X) → A ϵ ℱ ＝ x ϵ A)
  I x = Π-is-prop fe (λ A → 𝟚-is-set)

  II : x ＝ y
  II = τ III
   where
    III : (A : Clopen X) → x ϵ A ＝ y ϵ A
    III A = x ϵ A ＝⟨ (φ A)⁻¹ ⟩
            A ϵ ℱ ＝⟨ ψ A ⟩
            y ϵ A ∎

being-principal-is-prop-gives-totally-separated
 : {X : 𝓤 ̇ }
 → ((ℱ : Clopen (Clopen X)) → is-prop (is-principal ℱ))
 → is-totally-separated X
being-principal-is-prop-gives-totally-separated {𝓤} {X} σ {x} {y} e
 = ap pr₁ (σ (λ A → x ϵ A) (x , (λ A → refl)) (y , e))

\end{code}

We name the four conditions in the definition of an ultrafilter, and
we show that ultrafilters are monotone and preserve complements.

\begin{code}

module ultrafilter-properties
        {X : 𝓤 ̇ }
        (ℱ : Clopen (Clopen X))
        (i : is-ultrafilter ℱ)
       where

 preserves-₀ : ∅ ∉ ℱ
 preserves-₀ = pr₁ i

 preserves-₁ : 𝟏 ∈ ℱ
 preserves-₁ = pr₁ (pr₂ i)

 preserves-∧ : (A B : Clopen X) → (A ∩ B) ϵ ℱ ＝ A ϵ ℱ ∧ B ϵ ℱ
 preserves-∧ = pr₁ (pr₂ (pr₂ i))

 preserves-∨ : (A B : Clopen X) → (A ∪ B) ϵ ℱ ＝ A ϵ ℱ ∨ B ϵ ℱ
 preserves-∨ = pr₂ (pr₂ (pr₂ i))

 monotone : {A B : Clopen X} → A ⊆ B → A ϵ ℱ ≤ B ϵ ℱ
 monotone {A} {B} l = transport (λ - → - ≤ B ϵ ℱ) II Lemma[minab≤₂b]
  where
   I : A ∩ B ＝ A
   I = dfunext fe (λ x → Lemma[a≤₂b→min𝟚ab＝a] (l x))

   II : A ϵ ℱ ∧ B ϵ ℱ ＝ A ϵ ℱ
   II = A ϵ ℱ ∧ B ϵ ℱ ＝⟨ (preserves-∧ A B)⁻¹ ⟩
        (A ∩ B) ϵ ℱ   ＝⟨ ap ℱ I ⟩
        A ϵ ℱ         ∎

 preserves-complement : (A : Clopen X) → complement A ϵ ℱ ＝ ⇁ (A ϵ ℱ)
 preserves-complement A = 𝟚-equality-cases III IV
  where
   I : A ϵ ℱ ∧ complement A ϵ ℱ ＝ ₀
   I = A ϵ ℱ ∧ complement A ϵ ℱ ＝⟨ (preserves-∧ A (complement A))⁻¹ ⟩
       (A ∩ complement A) ϵ ℱ   ＝⟨ ap ℱ I₀ ⟩
       ∅ ϵ ℱ                    ＝⟨ preserves-₀ ⟩
       ₀                        ∎
    where
     I₀ : A ∩ complement A ＝ ∅
     I₀ = dfunext fe (λ x → min𝟚-complement (x ϵ A))

   II : A ϵ ℱ ∨ complement A ϵ ℱ ＝ ₁
   II = A ϵ ℱ ∨ complement A ϵ ℱ ＝⟨ (preserves-∨ A (complement A))⁻¹ ⟩
        (A ∪ complement A) ϵ ℱ   ＝⟨ ap ℱ II₀ ⟩
        𝟏 ϵ ℱ                    ＝⟨ preserves-₁ ⟩
        ₁                        ∎
    where
     II₀ : A ∪ complement A ＝ 𝟏
     II₀ = dfunext fe (λ x → max𝟚-complement (x ϵ A))

   III : A ∉ ℱ → complement A ϵ ℱ ＝ ⇁ (A ϵ ℱ)
   III e = complement A ϵ ℱ         ＝⟨refl⟩
           ₀ ∨ complement A ϵ ℱ     ＝⟨ ap (λ - → - ∨ complement A ϵ ℱ) (e ⁻¹) ⟩
           A ϵ ℱ ∨ complement A ϵ ℱ ＝⟨ II ⟩
           ₁                        ＝⟨refl⟩
           ⇁ ₀                      ＝⟨ ap ⇁_ (e ⁻¹) ⟩
           ⇁ (A ϵ ℱ)                ∎

   IV : A ∈ ℱ → complement A ϵ ℱ ＝ ⇁ (A ϵ ℱ)
   IV e = complement A ϵ ℱ         ＝⟨refl⟩
          ₁ ∧ complement A ϵ ℱ     ＝⟨ ap (λ - → - ∧ complement A ϵ ℱ) (e ⁻¹) ⟩
          A ϵ ℱ ∧ complement A ϵ ℱ ＝⟨ I ⟩
          ₀                        ＝⟨refl⟩
          ⇁ ₁                      ＝⟨ ap ⇁_ (e ⁻¹) ⟩
          ⇁ (A ϵ ℱ)                ∎

\end{code}

We now define the type 𝕌 X of the ultrafilters of the clopens of X,
the map 𝕡 that takes a point of X to its principal ultrafilter, and
the notions of a pre-Stone type and a Stone type. The clopens of X
form a discrete type precisely when X is Π-compact in the sense of the
module TypeTopology.WeaklyCompactTypes, so that a Stone type is a
Π-compact pre-Stone type.

\begin{code}

𝕌 : 𝓤 ̇ → 𝓤 ̇
𝕌 X = Σ ℱ ꞉ Clopen (Clopen X) , is-ultrafilter ℱ

clopens-of : {X : 𝓤 ̇ } → 𝕌 X → Clopen (Clopen X)
clopens-of = pr₁

clopens-of-is-ultrafilter : {X : 𝓤 ̇ } (σ : 𝕌 X)
                          → is-ultrafilter (clopens-of σ)
clopens-of-is-ultrafilter = pr₂

𝕡 : (X : 𝓤 ̇ ) → X → 𝕌 X
𝕡 X x = eval X x , refl , refl , (λ A B → refl) , (λ A B → refl)

_ : (X : 𝓤 ̇ ) (x : X) (A : Clopen X) → A ϵ clopens-of (𝕡 X x) ＝ x ϵ A
_ = λ X x A → refl

is-pre-stone-type : 𝓤 ̇ → 𝓤 ̇
is-pre-stone-type X = is-equiv (𝕡 X)

being-pre-stone-type-is-prop : (X : 𝓤 ̇ ) → is-prop (is-pre-stone-type X)
being-pre-stone-type-is-prop X = being-equiv-is-prop'' fe (𝕡 X)

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

The first component of 𝕡 is the map eval X of the module
TypeTopology.TotallySeparated, which takes a point to the evaluation
at it and is the unit of the 𝟚-valued double dualization, as the
clopens of the clopens of X are the 𝟚-valued double dual of X. So 𝕡 is
the unit with its codomain cut down to the ultrafilters. The map
eval X is an embedding precisely when X is totally separated, and so
the same holds for 𝕡, as the inclusion of the ultrafilters into the
maps on the clopens is an embedding.

\begin{code}

clopens-of-is-embedding : {X : 𝓤 ̇ } → is-embedding (clopens-of {𝓤} {X})
clopens-of-is-embedding = pr₁-is-embedding being-ultrafilter-is-prop

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
are principal, give criteria for a type to be a pre-Stone type and a
Stone type, and show that pre-Stone types are totally separated.

\begin{code}

ultrafilters-of-pre-stone-types-are-principal
 : {X : 𝓤 ̇ }
 → is-pre-stone-type X
 → (ℱ : Clopen (Clopen X))
 → is-ultrafilter ℱ
 → is-principal ℱ
ultrafilters-of-pre-stone-types-are-principal {𝓤} {X} ζ ℱ i
 = x , II
 where
  x : X
  x = inverse (𝕡 X) ζ (ℱ , i)

  I : 𝕡 X x ＝ (ℱ , i)
  I = inverses-are-sections (𝕡 X) ζ (ℱ , i)

  II : (A : Clopen X) → A ϵ ℱ ＝ x ϵ A
  II A = (happly (ap clopens-of I) A)⁻¹

pre-stone-criterion
 : {X : 𝓤 ̇ }
 → is-totally-separated X
 → ((ℱ : Clopen (Clopen X)) → is-ultrafilter ℱ → is-principal ℱ)
 → is-pre-stone-type X
pre-stone-criterion {𝓤} {X} τ ψ
 = vv-equivs-are-equivs (𝕡 X) I
 where
  I : (σ : 𝕌 X) → is-singleton (fiber (𝕡 X) σ)
  I (ℱ , i) = II (ψ ℱ i)
   where
    II : is-principal ℱ
       → is-singleton (fiber (𝕡 X) (ℱ , i))
    II (x , e) =
     pointed-props-are-singletons
      (x , to-subtype-＝ being-ultrafilter-is-prop
            (dfunext fe (λ A → (e A)⁻¹)))
      (totally-separated-gives-𝕡-is-embedding τ (ℱ , i))

stone-criterion
 : {X : 𝓤 ̇ }
 → is-discrete (Clopen X)
 → is-totally-separated X
 → ((ℱ : Clopen (Clopen X)) → is-ultrafilter ℱ → is-principal ℱ)
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

  I : (ℱ : Clopen (Clopen Y)) → is-ultrafilter ℱ → is-principal ℱ
  I ℱ i = III (ultrafilters-of-pre-stone-types-are-principal ζ 𝒢 II)
   where
    open ultrafilter-properties ℱ i

    𝒢 : Clopen (Clopen X)
    𝒢 A = (A ∘ s) ϵ ℱ

    II : is-ultrafilter 𝒢
    II = preserves-₀ ,
         preserves-₁ ,
         (λ A A' → preserves-∧ (A ∘ s) (A' ∘ s)) ,
         (λ A A' → preserves-∨ (A ∘ s) (A' ∘ s))

    III : is-principal 𝒢 → is-principal ℱ
    III (x , φ) = r x , IV
     where
      IV : (A : Clopen Y) → A ϵ ℱ ＝ r x ϵ A
      IV A = A ϵ ℱ           ＝⟨ ap ℱ V ⟩
             (A ∘ r ∘ s) ϵ ℱ ＝⟨ φ (A ∘ r) ⟩
             r x ϵ A         ∎
       where
        V : A ＝ A ∘ r ∘ s
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
  I : (σ : 𝕌 (𝟘 {𝓤})) → is-singleton (fiber (𝕡 𝟘) σ)
  I (ℱ , i) = zero-is-one-elim III
   where
    open ultrafilter-properties ℱ i

    II : ∅ ＝ 𝟏
    II = dfunext fe (λ x → 𝟘-elim x)

    III : ₀ ＝ ₁
    III = ₀     ＝⟨ preserves-₀ ⁻¹ ⟩
          ∅ ϵ ℱ ＝⟨ ap ℱ II ⟩
          𝟏 ϵ ℱ ＝⟨ preserves-₁ ⟩
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
  I : (ℱ : Clopen (Clopen (𝟙 {𝓤}))) → is-ultrafilter ℱ → is-principal ℱ
  I ℱ i = ⋆ , II
   where
    open ultrafilter-properties ℱ i

    II : (A : Clopen (𝟙 {𝓤})) → A ϵ ℱ ＝ ⋆ ϵ A
    II A = 𝟚-equality-cases III IV
     where
      III : ⋆ ∉ A → A ϵ ℱ ＝ ⋆ ϵ A
      III e = A ϵ ℱ ＝⟨ ap ℱ (dfunext fe (λ _ → e)) ⟩
              ∅ ϵ ℱ ＝⟨ preserves-₀ ⟩
              ₀     ＝⟨ e ⁻¹ ⟩
              ⋆ ϵ A ∎

      IV : ⋆ ∈ A → A ϵ ℱ ＝ ⋆ ϵ A
      IV e = A ϵ ℱ ＝⟨ ap ℱ (dfunext fe (λ _ → e)) ⟩
             𝟏 ϵ ℱ ＝⟨ preserves-₁ ⟩
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
point of Y, we extend a clopen of Y to a clopen of X. The extension
takes ∅ to ∅ and 𝟏 to A, it preserves the two binary operations, it
agrees with the given clopen along σ, and the points which belong to
it are in A. We use it for the criterion that follows and again for
the clopen subtype below.

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
 ext C x = ext' C x (δ x)

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
 → (ℱ : Clopen (Clopen X))
 → is-ultrafilter ℱ
 → A ∈ ℱ
 → Σ y ꞉ Y , ((B : Clopen X) → B ϵ ℱ ＝ j y ϵ B)
ultrafilter-principality-criterion {𝓤} {𝓥} {X} {Y} A j σ jσ ζ ℱ i e
 = VI (ultrafilters-of-pre-stone-types-are-principal
        ζ (ℱ ∘ ext) ext-is-ultrafilter)
 where
  open ultrafilter-properties ℱ i
  open clopen-extension A σ

  ext-is-ultrafilter : is-ultrafilter (ℱ ∘ ext)
  ext-is-ultrafilter = I , II , III , IV
   where
    I : ext ∅ ∉ ℱ
    I = ext ∅ ϵ ℱ ＝⟨ ap ℱ ext-∅ ⟩
        ∅ ϵ ℱ     ＝⟨ preserves-₀ ⟩
        ₀         ∎

    II : ext 𝟏 ∈ ℱ
    II = ext 𝟏 ϵ ℱ ＝⟨ ap ℱ ext-𝟏 ⟩
         A ϵ ℱ     ＝⟨ e ⟩
         ₁         ∎

    III : (C C' : Clopen Y) → ext (C ∩ C') ϵ ℱ ＝ ext C ϵ ℱ ∧ ext C' ϵ ℱ
    III C C' = ext (C ∩ C') ϵ ℱ       ＝⟨ ap ℱ (ext-∩ C C') ⟩
               (ext C ∩ ext C') ϵ ℱ   ＝⟨ preserves-∧ (ext C) (ext C') ⟩
               ext C ϵ ℱ ∧ ext C' ϵ ℱ ∎

    IV : (C C' : Clopen Y) → ext (C ∪ C') ϵ ℱ ＝ ext C ϵ ℱ ∨ ext C' ϵ ℱ
    IV C C' = ext (C ∪ C') ϵ ℱ       ＝⟨ ap ℱ (ext-∪ C C') ⟩
              (ext C ∪ ext C') ϵ ℱ   ＝⟨ preserves-∨ (ext C) (ext C') ⟩
              ext C ϵ ℱ ∨ ext C' ϵ ℱ ∎

  VI : is-principal (ℱ ∘ ext)
     → Σ y ꞉ Y , ((B : Clopen X) → B ϵ ℱ ＝ j y ϵ B)
  VI (y , φ) = y , VII
   where
    VII : (B : Clopen X) → B ϵ ℱ ＝ j y ϵ B
    VII B = 𝟚-equality-cases I II
     where
      I : j y ∉ B → B ϵ ℱ ＝ j y ϵ B
      I d = B ϵ ℱ   ＝⟨ V ⟩
            ₀       ＝⟨ d ⁻¹ ⟩
            j y ϵ B ∎
       where
        III : B ⊆ ext (B ∘ j) ∪ complement A
        III x = ≤₂-criterion (v (∈-is-decidable x A))
         where
          v : (c : is-decidable (x ∈ A))
            → x ∈ B → x ∈ ext (B ∘ j) ∪ complement A
          v (inl d) s = max𝟚-lemma-converse (inl vi)
           where
            vi : x ∈ ext (B ∘ j)
            vi = x ϵ ext (B ∘ j) ＝⟨ ext-at-section (B ∘ j) x d ⟩
                 j (σ x d) ϵ B   ＝⟨ ap B (jσ x d) ⟩
                 x ϵ B           ＝⟨ s ⟩
                 ₁               ∎
          v (inr ν) s = max𝟚-lemma-converse
                         (inr (ap ⇁_ (different-from-₁-equal-₀ ν)))

        IV : (ext (B ∘ j) ∪ complement A) ∉ ℱ
        IV = (ext (B ∘ j) ∪ complement A) ϵ ℱ   ＝⟨ IV₀ ⟩
             ext (B ∘ j) ϵ ℱ ∨ complement A ϵ ℱ ＝⟨ ap₂ _∨_ IV₁ IV₂ ⟩
             ₀ ∨ ₀                              ＝⟨refl⟩
             ₀                                  ∎
         where
          IV₀ = preserves-∨ (ext (B ∘ j)) (complement A)

          IV₁ : ext (B ∘ j) ∉ ℱ
          IV₁ = ext (B ∘ j) ϵ ℱ ＝⟨ φ (B ∘ j) ⟩
                j y ϵ B         ＝⟨ d ⟩
                ₀               ∎

          IV₂ : complement A ∉ ℱ
          IV₂ = complement A ϵ ℱ ＝⟨ preserves-complement A ⟩
                ⇁ (A ϵ ℱ)        ＝⟨ ap ⇁_ e ⟩
                ⇁ ₁              ＝⟨refl⟩
                ₀                ∎

        V : B ∉ ℱ
        V = ₀-minimal (transport (λ - → B ϵ ℱ ≤ -) IV (monotone III))

      II : j y ∈ B → B ϵ ℱ ＝ j y ϵ B
      II d = B ϵ ℱ   ＝⟨ ₁-maximal IV ⟩
             ₁       ＝⟨ d ⁻¹ ⟩
             j y ϵ B ∎
       where
        III : ext (B ∘ j) ⊆ B
        III x = ≤₂-criterion III₀
         where
          III₀ : x ∈ ext (B ∘ j) → x ∈ B
          III₀ s = x ϵ B           ＝⟨ (ap B (jσ x d'))⁻¹ ⟩
                   j (σ x d') ϵ B  ＝⟨ (ext-at-section (B ∘ j) x d')⁻¹ ⟩
                   x ϵ ext (B ∘ j) ＝⟨ s ⟩
                   ₁               ∎
           where
            d' : x ∈ A
            d' = ext-gives-∈ (B ∘ j) x s

        IV : ₁ ≤ B ϵ ℱ
        IV = transport (λ - → - ≤ B ϵ ℱ) v (monotone III)
         where
          v : ext (B ∘ j) ∈ ℱ
          v = ext (B ∘ j) ϵ ℱ ＝⟨ φ (B ∘ j) ⟩
              j y ϵ B         ＝⟨ d ⟩
              ₁               ∎

\end{code}

Stone types are closed under binary sums.

\begin{code}

+-is-pre-stone-type
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → is-pre-stone-type X
 → is-pre-stone-type Y
 → is-pre-stone-type (X + Y)
+-is-pre-stone-type {𝓤} {𝓥} {X} {Y} ζ₀ ζ₁
 = pre-stone-criterion
    (+-totally-separated X Y
      (pre-stone-types-are-totally-separated ζ₀)
      (pre-stone-types-are-totally-separated ζ₁))
    I
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

  I : (ℱ : Clopen (Clopen (X + Y))) → is-ultrafilter ℱ → is-principal ℱ
  I ℱ i = 𝟚-equality-cases II III
   where
    open ultrafilter-properties ℱ i

    II : A ∉ ℱ → is-principal ℱ
    II d = V (ultrafilter-principality-criterion
                (complement A) inr σ₁ jσ₁ ζ₁ ℱ i IV)
     where
      IV : complement A ∈ ℱ
      IV = complement A ϵ ℱ ＝⟨ preserves-complement A ⟩
           ⇁ (A ϵ ℱ)        ＝⟨ ap ⇁_ d ⟩
           ⇁ ₀              ＝⟨refl⟩
           ₁                ∎

      V : (Σ y ꞉ Y , ((B : Clopen (X + Y)) → B ϵ ℱ ＝ inr y ϵ B))
        → is-principal ℱ
      V (y , φ) = inr y , φ

    III : A ∈ ℱ → is-principal ℱ
    III d = IV (ultrafilter-principality-criterion A inl σ₀ jσ₀ ζ₀ ℱ i d)
     where
      IV : (Σ x ꞉ X , ((B : Clopen (X + Y)) → B ϵ ℱ ＝ inl x ϵ B))
         → is-principal ℱ
      IV (x , φ) = inl x , φ

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

The standard finite types are Stone types.

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

  II : (ℱ : Clopen (Clopen P)) → is-ultrafilter ℱ → is-principal ℱ
  II ℱ i = x₀ , VI
   where
    open ultrafilter-properties ℱ i

    III : ¬ P → ∅ ＝ 𝟏
    III ν = dfunext fe (λ x → 𝟘-elim (ν x))

    IV : ¬¬ P
    IV ν = zero-is-one-elim
            (₀     ＝⟨ preserves-₀ ⁻¹ ⟩
             ∅ ϵ ℱ ＝⟨ ap ℱ (III ν) ⟩
             𝟏 ϵ ℱ ＝⟨ preserves-₁ ⟩
             ₁     ∎)

    x₀ : P
    x₀ = P-is-¬¬-stable IV

    V : (A : Clopen P) (b : 𝟚) → x₀ ϵ A ＝ b → A ＝ (λ _ → b)
    V A b e = dfunext fe v
     where
      v : (x : P) → x ϵ A ＝ b
      v x = x ϵ A  ＝⟨ ap A (P-is-prop x x₀) ⟩
            x₀ ϵ A ＝⟨ e ⟩
            b      ∎

    VI : (A : Clopen P) → A ϵ ℱ ＝ x₀ ϵ A
    VI A = 𝟚-equality-cases v vi
     where
      v : x₀ ∉ A → A ϵ ℱ ＝ x₀ ϵ A
      v e = A ϵ ℱ  ＝⟨ ap ℱ (V A ₀ e) ⟩
            ∅ ϵ ℱ  ＝⟨ preserves-₀ ⟩
            ₀      ＝⟨ e ⁻¹ ⟩
            x₀ ϵ A ∎

      vi : x₀ ∈ A → A ϵ ℱ ＝ x₀ ϵ A
      vi e = A ϵ ℱ  ＝⟨ ap ℱ (V A ₁ e) ⟩
             𝟏 ϵ ℱ  ＝⟨ preserves-₁ ⟩
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

stone-props-are-decidable
 : {P : 𝓤 ̇ }
 → is-prop P
 → is-stone-type P
 → is-decidable P
stone-props-are-decidable {𝓤} {P} P-is-prop ζ
 = I (negations-of-Π-compact-types-are-decidable P c)
 where
  c : is-Π-compact P
  c = stone-types-are-Π-compact ζ

  ℱ : Clopen (Clopen P)
  ℱ = pr₁ (co-characteristic-function c)

  ℱ-property : (A : Clopen P)
             → (A ∉ ℱ → ¬ ((x : P) → x ∈ A)) × (A ∈ ℱ → (x : P) → x ∈ A)
  ℱ-property = pr₂ (co-characteristic-function c)

  ℱ-property₀ : (A : Clopen P) → A ∉ ℱ → ¬ ((x : P) → x ∈ A)
  ℱ-property₀ A = pr₁ (ℱ-property A)

  ℱ-property₁ : (A : Clopen P) → A ∈ ℱ → (x : P) → x ∈ A
  ℱ-property₁ A = pr₂ (ℱ-property A)

  ℱ-property₂ : (A : Clopen P) → ((x : P) → x ∈ A) → A ∈ ℱ
  ℱ-property₂ A σ = different-from-₀-equal-₁
                       (λ e → ℱ-property₀ A e σ)

  ℱ-property₃ : (A : Clopen P) → ¬ ((x : P) → x ∈ A) → A ∉ ℱ
  ℱ-property₃ A ν = different-from-₁-equal-₀
                           (λ e → ν (ℱ-property₁ A e))

  not-all-gives-¬¬-some-outside
   : (A : Clopen P)
   → ¬ ((x : P) → x ∈ A)
   → ¬¬ (Σ x ꞉ P , x ∉ A)
  not-all-gives-¬¬-some-outside A ν φ =
   ν (λ x → different-from-₀-equal-₁ (λ e → φ (x , e)))

  I : is-decidable (¬ P) → is-decidable P
  I (inl ν) = inr ν
  I (inr ν) = inl (pr₁ (ultrafilters-of-pre-stone-types-are-principal
                         (stone-types-are-pre-stone-types ζ)
                         ℱ
                         III))
   where
    III : is-ultrafilter ℱ
    III = iv , v , vi , vii
     where
      iv : ∅ ∉ ℱ
      iv = ℱ-property₃ ∅ (λ σ → ν (λ x → zero-is-one-elim (σ x)))

      v : 𝟏 ∈ ℱ
      v = ℱ-property₂ 𝟏 (λ _ → refl)

      vi : (A B : Clopen P) → (A ∩ B) ϵ ℱ ＝ A ϵ ℱ ∧ B ϵ ℱ
      vi A B = ＝₂-criterion a b
       where
        a : (A ∩ B) ∈ ℱ → A ϵ ℱ ∧ B ϵ ℱ ＝ ₁
        a e = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
               (ℱ-property₂ A (λ x → Lemma[min𝟚ab＝₁→a＝₁]
                              (ℱ-property₁ (A ∩ B) e x)))
               (ℱ-property₂ B (λ x → Lemma[min𝟚ab＝₁→b＝₁]
                              (ℱ-property₁ (A ∩ B) e x)))

        b : A ϵ ℱ ∧ B ϵ ℱ ＝ ₁ → (A ∩ B) ∈ ℱ
        b e = ℱ-property₂ (A ∩ B)
               (λ x → Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
                       (ℱ-property₁ A (Lemma[min𝟚ab＝₁→a＝₁] e) x)
                       (ℱ-property₁ B (Lemma[min𝟚ab＝₁→b＝₁] e) x))

      vii : (A B : Clopen P) → (A ∪ B) ϵ ℱ ＝ A ϵ ℱ ∨ B ϵ ℱ
      vii A B = ＝₂-criterion a b
       where
        a : (A ∪ B) ∈ ℱ → A ϵ ℱ ∨ B ϵ ℱ ＝ ₁
        a e = 𝟚-equality-cases viii ix
         where
          σ : (x : P) → x ∈ A ∪ B
          σ = ℱ-property₁ (A ∪ B) e

          viii : A ∉ ℱ → A ϵ ℱ ∨ B ϵ ℱ ＝ ₁
          viii e₀ = 𝟚-equality-cases viii₀ viii₁
           where
            viii₀ : B ∉ ℱ → A ϵ ℱ ∨ B ϵ ℱ ＝ ₁
            viii₀ e₁ = 𝟘-elim
                    (not-all-gives-¬¬-some-outside A (ℱ-property₀ A e₀)
                      (λ (x₀ , r₀) →
                         not-all-gives-¬¬-some-outside B (ℱ-property₀ B e₁)
                          (λ (x₁ , r₁) → zero-is-one-elim
                                          (xii x₀ x₁ r₀ r₁))))
             where
              xii : (x₀ x₁ : P) → x₀ ∉ A → x₁ ∉ B → ₀ ＝ ₁
              xii x₀ x₁ r₀ r₁ =
               ₀            ＝⟨ (ap₂ _∨_ r₀ xiii)⁻¹ ⟩
               x₀ ϵ (A ∪ B) ＝⟨ σ x₀ ⟩
               ₁            ∎
               where
                xiii : x₀ ∉ B
                xiii = x₀ ϵ B ＝⟨ ap B (P-is-prop x₀ x₁) ⟩
                       x₁ ϵ B ＝⟨ r₁ ⟩
                       ₀      ∎

            viii₁ : B ∈ ℱ → A ϵ ℱ ∨ B ϵ ℱ ＝ ₁
            viii₁ e₁ = max𝟚-lemma-converse (inr e₁)

          ix : A ∈ ℱ → A ϵ ℱ ∨ B ϵ ℱ ＝ ₁
          ix e₀ = max𝟚-lemma-converse (inl e₀)

        b : A ϵ ℱ ∨ B ϵ ℱ ＝ ₁ → (A ∪ B) ∈ ℱ
        b e = ℱ-property₂ (A ∪ B) (cases viii ix (max𝟚-lemma e))
         where
          viii : A ∈ ℱ → (x : P) → x ∈ A ∪ B
          viii e₀ x = max𝟚-lemma-converse
                       (inl (ℱ-property₁ A e₀ x))

          ix : B ∈ ℱ → (x : P) → x ∈ A ∪ B
          ix e₁ x = max𝟚-lemma-converse
                     (inr (ℱ-property₁ B e₁ x))

\end{code}

A product of pre-Stone types indexed by a proposition is a pre-Stone
type, which is the analogue of the micro Tychonoff theorem of the
module TypeTopology.MicroTychonoff. The point at which ℱ is principal
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

  I : (ℱ : Clopen (Clopen (Π Y)))
    → is-ultrafilter ℱ
    → is-principal ℱ
  I ℱ i = f , IV
   where
    open ultrafilter-properties ℱ i

    ℱₚ : (p : P) → Clopen (Clopen (Y p))
    ℱₚ p A = (A ∘ ⌜ 𝕖 p ⌝) ϵ ℱ

    ℱₚ-is-ultrafilter : (p : P) → is-ultrafilter (ℱₚ p)
    ℱₚ-is-ultrafilter p = preserves-₀ ,
                          preserves-₁ ,
                          (λ A B → preserves-∧ (A ∘ ⌜ 𝕖 p ⌝) (B ∘ ⌜ 𝕖 p ⌝)) ,
                          (λ A B → preserves-∨ (A ∘ ⌜ 𝕖 p ⌝) (B ∘ ⌜ 𝕖 p ⌝))

    II : (p : P) → Σ x ꞉ Y p , ((A : Clopen (Y p)) → A ϵ ℱₚ p ＝ x ϵ A)
    II p = ultrafilters-of-pre-stone-types-are-principal
            (ζ p) (ℱₚ p) (ℱₚ-is-ultrafilter p)

    f : Π Y
    f p = pr₁ (II p)

    f-property : (p : P) (A : Clopen (Y p)) → A ϵ ℱₚ p ＝ f p ϵ A
    f-property p = pr₂ (II p)

    III : (Σ g ꞉ Π Y , ((A : Clopen (Π Y)) → A ϵ ℱ ＝ g ϵ A))
        → (A : Clopen (Π Y)) → A ϵ ℱ ＝ f ϵ A
    III (g , φ) A = A ϵ ℱ ＝⟨ φ A ⟩
                    g ϵ A ＝⟨ ap A (V ⁻¹) ⟩
                    f ϵ A ∎
     where
      V : f ＝ g
      V = dfunext fe VI
       where
        VI : (p : P) → f p ＝ g p
        VI p = pre-stone-types-are-totally-separated (ζ p) vi
         where
          vi : (A : Clopen (Y p)) → f p ϵ A ＝ g p ϵ A
          vi A = f p ϵ A  ＝⟨ (f-property p A)⁻¹ ⟩
                 A ϵ ℱₚ p ＝⟨ φ (A ∘ ⌜ 𝕖 p ⌝) ⟩
                 g p ϵ A  ∎

    IV : (A : Clopen (Π Y)) → A ϵ ℱ ＝ f ϵ A
    IV A = 𝟚-is-¬¬-separated (A ϵ ℱ) (f ϵ A) V
     where
      V : ¬¬ (A ϵ ℱ ＝ f ϵ A)
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
                          (VII d) ℱ i) A)

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
agree on that fiber agree on a clopen of the base that belongs to the
ultrafilter. So the sum is a Stone type as soon as every clopen of
every fiber is the restriction of a clopen of the sum, which we call
having extendable clopens. We define this pointwise, and we name the
extension of a clopen of a fiber and the equation it satisfies on that
fiber.

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

Σ-is-stone-type-if-family-has-extendable-clopens
 : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
 → is-stone-type X
 → ((x : X) → is-stone-type (Y x))
 → has-extendable-clopens Y
 → is-stone-type (Σ Y)
Σ-is-stone-type-if-family-has-extendable-clopens {𝓤} {𝓥} {X} {Y} ζ δ ext
 = stone-criterion I II III
 where
  agreement-is-decidable
   : (A B : Clopen (Σ Y)) (x : X)
   → is-decidable ((λ y → (x , y) ϵ A) ＝ (λ y → (x , y) ϵ B))
  agreement-is-decidable A B x
   = stone-types-have-discrete-clopen-algebras (δ x)
      (λ y → (x , y) ϵ A)
      (λ y → (x , y) ϵ B)

  agreement : Clopen (Σ Y) → Clopen (Σ Y) → Clopen X
  agreement A B = pr₁ (co-characteristic-function (agreement-is-decidable A B))

  agreement-property
   : (A B : Clopen (Σ Y)) (x : X)
   → (x ∉ agreement A B → (λ y → (x , y) ϵ A) ≠ (λ y → (x , y) ϵ B))
   × (x ∈ agreement A B → (λ y → (x , y) ϵ A) ＝ (λ y → (x , y) ϵ B))
  agreement-property A B = pr₂ (co-characteristic-function
                                 (agreement-is-decidable A B))

  agreement-property₀
   : (A B : Clopen (Σ Y)) (x : X)
   → x ∉ agreement A B
   → (λ y → (x , y) ϵ A) ≠ (λ y → (x , y) ϵ B)
  agreement-property₀ A B x = pr₁ (agreement-property A B x)

  agreement-property₁
   : (A B : Clopen (Σ Y)) (x : X)
   → x ∈ agreement A B
   → (λ y → (x , y) ϵ A) ＝ (λ y → (x , y) ϵ B)
  agreement-property₁ A B x = pr₂ (agreement-property A B x)

  agreement-property₂
   : (A B : Clopen (Σ Y)) (x : X)
   → ((y : Y x) → (x , y) ϵ A ＝ (x , y) ϵ B)
   → x ∈ agreement A B
  agreement-property₂ A B x ψ =
   different-from-₀-equal-₁
    (λ e → agreement-property₀ A B x e (dfunext fe ψ))

  I : is-discrete (Clopen (Σ Y))
  I = Π-compact-gives-discrete-clopen-algebra
       (Π-compact-closed-under-Σ
         (stone-types-are-Π-compact ζ)
         (λ x → stone-types-are-Π-compact (δ x)))

  II : is-totally-separated (Σ Y)
  II {x , y} {x' , y'} φ = to-Σ-＝ (IV , V)
   where
    IV : x ＝ x'
    IV = pre-stone-types-are-totally-separated
          (stone-types-are-pre-stone-types ζ)
          (λ C → φ (C ∘ pr₁))

    V : transport Y IV y ＝ y'
    V = pre-stone-types-are-totally-separated
         (stone-types-are-pre-stone-types (δ x'))
         VI
     where
      VI : (A : Clopen (Y x')) → transport Y IV y ϵ A ＝ y' ϵ A
      VI A = transport Y IV y ϵ A        ＝⟨ (vii (transport Y IV y))⁻¹ ⟩
             (x' , transport Y IV y) ϵ B ＝⟨ (ap B (to-Σ-＝ (IV , refl)))⁻¹ ⟩
             (x , y) ϵ B                 ＝⟨ φ B ⟩
             (x' , y') ϵ B               ＝⟨ vii y' ⟩
             y' ϵ A                      ∎
       where
        B : Clopen (Σ Y)
        B = extension-of-clopen (ext x') A

        vii : (y'' : Y x') → (x' , y'') ϵ B ＝ y'' ϵ A
        vii = extension-of-clopen-at-fiber (ext x') A

  III : (ℱ : Clopen (Clopen (Σ Y))) → is-ultrafilter ℱ → is-principal ℱ
  III ℱ i = (x₀ , y₀) , XIII
   where
    open ultrafilter-properties ℱ i

    ℱ₁ : Clopen (Clopen X)
    ℱ₁ C = (C ∘ pr₁) ϵ ℱ

    IV : is-ultrafilter ℱ₁
    IV = preserves-₀ ,
         preserves-₁ ,
         (λ C C' → preserves-∧ (C ∘ pr₁) (C' ∘ pr₁)) ,
         (λ C C' → preserves-∨ (C ∘ pr₁) (C' ∘ pr₁))

    V : is-principal ℱ₁
    V = ultrafilters-of-pre-stone-types-are-principal
         (stone-types-are-pre-stone-types ζ) ℱ₁ IV

    x₀ : X
    x₀ = pr₁ V

    φ₁ : (C : Clopen X) → C ϵ ℱ₁ ＝ x₀ ϵ C
    φ₁ = pr₂ V

    VI : (A B : Clopen (Σ Y))
       → ((y : Y x₀) → (x₀ , y) ϵ A ＝ (x₀ , y) ϵ B)
       → A ϵ ℱ ＝ B ϵ ℱ
    VI A B ψ = A ϵ ℱ         ＝⟨ VIII ⟩
               (D ∩ A) ϵ ℱ   ＝⟨ ap ℱ IX ⟩
               (D ∩ B) ϵ ℱ   ＝⟨ preserves-∧ D B ⟩
               D ϵ ℱ ∧ B ϵ ℱ ＝⟨ ap (λ - → - ∧ B ϵ ℱ) VII ⟩
               B ϵ ℱ         ∎
     where
      D : Clopen (Σ Y)
      D = agreement A B ∘ pr₁

      VII : D ∈ ℱ
      VII = D ϵ ℱ              ＝⟨ φ₁ (agreement A B) ⟩
            x₀ ϵ agreement A B ＝⟨ agreement-property₂ A B x₀ ψ ⟩
            ₁                  ∎

      VIII : A ϵ ℱ ＝ (D ∩ A) ϵ ℱ
      VIII = A ϵ ℱ         ＝⟨ (ap (λ - → - ∧ A ϵ ℱ) VII)⁻¹ ⟩
             D ϵ ℱ ∧ A ϵ ℱ ＝⟨ (preserves-∧ D A)⁻¹ ⟩
             (D ∩ A) ϵ ℱ   ∎

      IX : D ∩ A ＝ D ∩ B
      IX = dfunext fe IX₀
       where
        IX₀ : (z : Σ Y) → z ϵ (D ∩ A) ＝ z ϵ (D ∩ B)
        IX₀ (x' , y) = 𝟚-equality-cases xi xii
         where
          xi : x' ∉ agreement A B
             → (x' , y) ϵ (D ∩ A) ＝ (x' , y) ϵ (D ∩ B)
          xi e = (x' , y) ϵ (D ∩ A) ＝⟨ ap (λ - → - ∧ (x' , y) ϵ A) e ⟩
                 ₀                  ＝⟨ (ap (λ - → - ∧ (x' , y) ϵ B) e)⁻¹ ⟩
                 (x' , y) ϵ (D ∩ B) ∎

          xii : x' ∈ agreement A B
              → (x' , y) ϵ (D ∩ A) ＝ (x' , y) ϵ (D ∩ B)
          xii e = ap (λ - → x' ϵ agreement A B ∧ -)
                   (happly (agreement-property₁ A B x' e) y)

    extension : Clopen (Y x₀) → Clopen (Σ Y)
    extension A = extension-of-clopen (ext x₀) A

    𝒢 : Clopen (Clopen (Y x₀))
    𝒢 = ℱ ∘ extension

    𝒢-slice : (A : Clopen (Y x₀)) (y : Y x₀) → (x₀ , y) ϵ extension A ＝ y ϵ A
    𝒢-slice A = extension-of-clopen-at-fiber (ext x₀) A

    𝒢-preserves-operation
     : (_⊛_ : 𝟚 → 𝟚 → 𝟚)
     → ((C D : Clopen (Σ Y)) → (λ z → z ϵ C ⊛ z ϵ D) ϵ ℱ ＝ C ϵ ℱ ⊛ D ϵ ℱ)
     → (A B : Clopen (Y x₀))
     → (λ y → y ϵ A ⊛ y ϵ B) ϵ 𝒢 ＝ A ϵ 𝒢 ⊛ B ϵ 𝒢
    𝒢-preserves-operation _⊛_ p A B =
     (λ y → y ϵ A ⊛ y ϵ B) ϵ 𝒢                     ＝⟨ i₀ ⟩
     (λ z → z ϵ extension A ⊛ z ϵ extension B) ϵ ℱ ＝⟨ i₁ ⟩
     A ϵ 𝒢 ⊛ B ϵ 𝒢                                 ∎
     where
      fiberwise : (y : Y x₀)
                → (x₀ , y) ϵ extension (λ y' → y' ϵ A ⊛ y' ϵ B)
                ＝ (x₀ , y) ϵ extension A ⊛ (x₀ , y) ϵ extension B
      fiberwise y =
       (x₀ , y) ϵ extension (λ y' → y' ϵ A ⊛ y' ϵ B)   ＝⟨ fiberwise₀ ⟩
       y ϵ A ⊛ y ϵ B                                   ＝⟨ fiberwise₁ ⟩
       (x₀ , y) ϵ extension A ⊛ (x₀ , y) ϵ extension B ∎
       where
        fiberwise₀ = 𝒢-slice (λ y' → y' ϵ A ⊛ y' ϵ B) y
        fiberwise₁ = ap₂ _⊛_ ((𝒢-slice A y)⁻¹) ((𝒢-slice B y)⁻¹)

      i₀ = VI (extension (λ y → y ϵ A ⊛ y ϵ B))
              (λ z → z ϵ extension A ⊛ z ϵ extension B)
              fiberwise
      i₁ = p (extension A) (extension B)

    XI : is-ultrafilter 𝒢
    XI = xiii , xiv , xv , xvi
     where
      xiii : ∅ ∉ 𝒢
      xiii = ∅ ϵ 𝒢 ＝⟨ VI (extension ∅) ∅ (𝒢-slice ∅) ⟩
             ∅ ϵ ℱ ＝⟨ preserves-₀ ⟩
             ₀     ∎

      xiv : 𝟏 ∈ 𝒢
      xiv = 𝟏 ϵ 𝒢 ＝⟨ VI (extension 𝟏) 𝟏 (𝒢-slice 𝟏) ⟩
            𝟏 ϵ ℱ ＝⟨ preserves-₁ ⟩
            ₁     ∎

      xv : (A B : Clopen (Y x₀)) → (A ∩ B) ϵ 𝒢 ＝ A ϵ 𝒢 ∧ B ϵ 𝒢
      xv = 𝒢-preserves-operation _∧_ preserves-∧

      xvi : (A B : Clopen (Y x₀)) → (A ∪ B) ϵ 𝒢 ＝ A ϵ 𝒢 ∨ B ϵ 𝒢
      xvi = 𝒢-preserves-operation _∨_ preserves-∨

    XII : is-principal 𝒢
    XII = ultrafilters-of-pre-stone-types-are-principal
           (stone-types-are-pre-stone-types (δ x₀))
           𝒢
           XI

    y₀ : Y x₀
    y₀ = pr₁ XII

    φ₂ : (A : Clopen (Y x₀)) → A ϵ 𝒢 ＝ y₀ ϵ A
    φ₂ = pr₂ XII

    XIII : (A : Clopen (Σ Y)) → A ϵ ℱ ＝ (x₀ , y₀) ϵ A
    XIII A = A ϵ ℱ                    ＝⟨ xviii ⟩
             (λ y → (x₀ , y) ϵ A) ϵ 𝒢 ＝⟨ φ₂ (λ y → (x₀ , y) ϵ A) ⟩
             (x₀ , y₀) ϵ A            ∎
     where
      xviii : A ϵ ℱ ＝ (λ y → (x₀ , y) ϵ A) ϵ 𝒢
      xviii = VI
               A
               (extension (λ y → (x₀ , y) ϵ A))
               (λ y → (𝒢-slice (λ y' → (x₀ , y') ϵ A) y)⁻¹)

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
constant-families-have-extendable-clopens x A = A ∘ pr₂ , (λ y → refl)

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

The clopen subtype inherits the pre-Stone property.

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

  II : (ℱ : Clopen (Clopen (clopen-subtype A)))
     → is-ultrafilter ℱ
     → is-principal ℱ
  II ℱ i = IV (ultrafilters-of-pre-stone-types-are-principal ζ 𝒢 III)
   where
    open ultrafilter-properties ℱ i

    𝒢 : Clopen (Clopen X)
    𝒢 B = (B ∘ clopen-subtype-inclusion A) ϵ ℱ

    III : is-ultrafilter 𝒢
    III = preserves-₀ ,
          preserves-₁ ,
          (λ B B' → preserves-∧ (B ∘ clopen-subtype-inclusion A)
                                (B' ∘ clopen-subtype-inclusion A)) ,
          (λ B B' → preserves-∨ (B ∘ clopen-subtype-inclusion A)
                                (B' ∘ clopen-subtype-inclusion A))

    IV : is-principal 𝒢 → is-principal ℱ
    IV (x₀ , V) = (x₀ , VI) , VIII
     where
      VI : x₀ ∈ A
      VI = x₀ ϵ A ＝⟨ (V A)⁻¹ ⟩
           A ϵ 𝒢  ＝⟨ ap ℱ (restriction-to-clopen-subtype-is-𝟏 A) ⟩
           𝟏 ϵ ℱ  ＝⟨ preserves-₁ ⟩
           ₁      ∎

      VII : (C : Clopen (clopen-subtype A))
          → ext C ∘ clopen-subtype-inclusion A ＝ C
      VII C = dfunext fe (λ (x , d) → ext-at-section C x d)

      VIII : (C : Clopen (clopen-subtype A)) → C ϵ ℱ ＝ (x₀ , VI) ϵ C
      VIII C = C ϵ ℱ         ＝⟨ ap ℱ (VII C)⁻¹ ⟩
               ext C ϵ 𝒢     ＝⟨ V (ext C) ⟩
               x₀ ϵ ext C    ＝⟨ ext-at-section C x₀ VI ⟩
               (x₀ , VI) ϵ C ∎

\end{code}

We now turn to ℕ∞. For a natural number n, the clopen ↑ n is the upper
set of n in ℕ∞.

\begin{code}

infix 50 ↑_

↑_ : ℕ → Clopen ℕ∞
(↑ n) x = ι x n

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

Given an ultrafilter ℱ of the clopens of ℕ∞, the sequence of values of
ℱ at the upper sets is decreasing, and so it is an element u of ℕ∞,
with which ℱ agrees on the upper sets by construction.

\begin{code}

module ultrafilter-on-ℕ∞
        (ℱ : Clopen (Clopen ℕ∞))
        (i : is-ultrafilter ℱ)
       where

 open ultrafilter-properties ℱ i

 private
  α : ℕ → 𝟚
  α n = ↑ n ϵ ℱ

  α-is-decreasing : is-decreasing α
  α-is-decreasing n = monotone I
   where
    I : ↑ (succ n) ⊆ ↑ n
    I (β , d) = d n

 u : ℕ∞
 u = (α , α-is-decreasing)

 _ : (n : ℕ) → ↑ n ϵ ℱ ＝ u ϵ ↑ n
 _ = λ n → refl

\end{code}

If u is finite, say u ＝ ι k, then singleton k belongs to ℱ, and the
only point belonging to singleton k is ι k. So the criterion above
applies with the one-point type, and ℱ is principal at u.

\begin{code}

 private
  ℱ-at-singleton : (k : ℕ) → u ＝ ι k → singleton k ∈ ℱ
  ℱ-at-singleton 0 e =
   singleton 0 ϵ ℱ ＝⟨ preserves-complement (↑ 0) ⟩
   ⇁ (α 0)         ＝⟨ ap ⇁_ I ⟩
   ⇁ ₀             ＝⟨refl⟩
   ₁               ∎
    where
     I : α 0 ＝ ₀
     I = α 0       ＝⟨ ap (λ - → ι - 0) e ⟩
         ι (ι 0) 0 ＝⟨ ℕ-to-ℕ∞-diagonal₀ 0 ⟩
         ₀         ∎
  ℱ-at-singleton (succ j) e =
   singleton (succ j) ϵ ℱ            ＝⟨ i₀ ⟩
   α j ∧ complement (↑ (succ j)) ϵ ℱ ＝⟨ i₁ ⟩
   α j ∧ ⇁ (α (succ j))              ＝⟨ i₂ ⟩
   ₁ ∧ ⇁ ₀                           ＝⟨refl⟩
   ₁                                 ∎
    where
     i₀ = preserves-∧ (↑ j) (complement (↑ (succ j)))
     i₁ = ap (λ - → α j ∧ -) (preserves-complement (↑ (succ j)))

     I : α j ＝ ₁
     I = α j              ＝⟨ ap (λ - → ι - j) e ⟩
         ι (ι (succ j)) j ＝⟨ ℕ-to-ℕ∞-diagonal₁ j ⟩
         ₁                ∎

     II : α (succ j) ＝ ₀
     II = α (succ j)              ＝⟨ ap (λ - → ι - (succ j)) e ⟩
          ι (ι (succ j)) (succ j) ＝⟨ ℕ-to-ℕ∞-diagonal₀ (succ j) ⟩
          ₀                       ∎

     i₂ = ap₂ (λ - -' → - ∧ ⇁ -') I II

 ℱ-at-finite : (k : ℕ) → u ＝ ι k → (A : Clopen ℕ∞) → A ϵ ℱ ＝ u ϵ A
 ℱ-at-finite k e A = I (ultrafilter-principality-criterion
                         (singleton k)
                         (λ _ → ι k)
                         (λ _ _ → ⋆)
                         (λ x d → (singleton-property₀ k x d)⁻¹)
                         (𝟙-is-pre-stone-type {𝓤₀})
                         ℱ i
                         (ℱ-at-singleton k e))
  where
   I : (Σ y ꞉ 𝟙 {𝓤₀} , ((B : Clopen ℕ∞) → B ϵ ℱ ＝ ι k ϵ B))
     → A ϵ ℱ ＝ u ϵ A
   I (y , φ) = A ϵ ℱ   ＝⟨ φ A ⟩
               ι k ϵ A ＝⟨ (ap A e)⁻¹ ⟩
               u ϵ A   ∎

 not-principal-at-u-gives-u-is-∞ : (A : Clopen ℕ∞) → A ϵ ℱ ≠ u ϵ A → u ＝ ∞
 not-principal-at-u-gives-u-is-∞ A ν =
  not-finite-is-∞ fe (λ k e → ν (ℱ-at-finite k e A))

\end{code}

If u is the point at infinity, then every upper set belongs to ℱ, and
the same holds for an ultrafilter that is not principal.

\begin{code}

 ℱ-at-upper-sets : u ＝ ∞ → (n : ℕ) → ↑ n ∈ ℱ
 ℱ-at-upper-sets e n = ap (λ - → ι - n) e

 _ : (A : Clopen ℕ∞) → A ϵ ℱ ≠ u ϵ A → (n : ℕ) → ↑ n ∈ ℱ
 _ = λ A ν → ℱ-at-upper-sets (not-principal-at-u-gives-u-is-∞ A ν)

 private
  clopens-containing-∞-are-in-ℱ
   : u ＝ ∞
   → (A : Clopen ℕ∞) (m : ℕ)
   → m is-modulus-of A
   → ∞ ∈ A
   → A ∈ ℱ
  clopens-containing-∞-are-in-ℱ e A m φ r =
   ≤₂-criterion-converse (monotone II) (ℱ-at-upper-sets e m)
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
    II x = ≤₂-criterion III
     where
      III : x ∈ ↑ m → x ∈ A
      III s = x ϵ A               ＝⟨refl⟩
              ₀ ∨ x ϵ A           ＝⟨ IV ⟩
              ⇁ (x ϵ ↑ m) ∨ x ϵ A ＝⟨ I x ⟩
              ₁                   ∎
       where
        IV = ap (λ - → ⇁ - ∨ x ϵ A) (s ⁻¹)

 ℱ-at-∞ : u ＝ ∞
        → (A : Clopen ℕ∞) (m : ℕ)
        → m is-modulus-of A
        → A ϵ ℱ ＝ u ϵ A
 ℱ-at-∞ e A m φ = 𝟚-equality-cases II III
  where
   I : u ϵ A ＝ ∞ ϵ A
   I = ap A e

   II : ∞ ∉ A → A ϵ ℱ ＝ u ϵ A
   II r = A ϵ ℱ ＝⟨ V ⟩
          ₀     ＝⟨ r ⁻¹ ⟩
          ∞ ϵ A ＝⟨ I ⁻¹ ⟩
          u ϵ A ∎
    where
     IV : complement A ∈ ℱ
     IV = clopens-containing-∞-are-in-ℱ e (complement A) m
           (λ n l → ap ⇁_ (φ n l))
           (ap ⇁_ r)

     V : A ∉ ℱ
     V = complement-lc (A ϵ ℱ) ₀ VI
      where
       VI : ⇁ (A ϵ ℱ) ＝ ⇁ ₀
       VI = ⇁ (A ϵ ℱ)        ＝⟨ (preserves-complement A)⁻¹ ⟩
            complement A ϵ ℱ ＝⟨ IV ⟩
            ₁                ＝⟨refl⟩
            ⇁ ₀              ∎

   III : ∞ ∈ A → A ϵ ℱ ＝ u ϵ A
   III r = A ϵ ℱ ＝⟨ clopens-containing-∞-are-in-ℱ e A m φ r ⟩
           ₁     ＝⟨ r ⁻¹ ⟩
           ∞ ϵ A ＝⟨ I ⁻¹ ⟩
           u ϵ A ∎

\end{code}

Putting the two cases together, ℱ is principal at u as soon as it is
principal at ∞ when u is ∞, which is the following criterion. If
¬ WLPO holds then the criterion applies.

\begin{code}

 ℱ-is-principal-at-u-criterion
  : (u ＝ ∞ → (A : Clopen ℕ∞) → A ϵ ℱ ＝ ∞ ϵ A)
  → (A : Clopen ℕ∞) → A ϵ ℱ ＝ u ϵ A
 ℱ-is-principal-at-u-criterion ψ A
  = 𝟚-is-¬¬-separated (A ϵ ℱ) (u ϵ A) I
  where
   I : ¬¬ (A ϵ ℱ ＝ u ϵ A)
   I ν = ν (A ϵ ℱ ＝⟨ ψ II A ⟩
            ∞ ϵ A ＝⟨ (ap A II)⁻¹ ⟩
            u ϵ A ∎)
    where
     II : u ＝ ∞
     II = not-principal-at-u-gives-u-is-∞ A ν

 ℱ-is-principal-at-u : ¬ WLPO → (A : Clopen ℕ∞) → A ϵ ℱ ＝ u ϵ A
 ℱ-is-principal-at-u nwlpo = ℱ-is-principal-at-u-criterion I
  where
   I : u ＝ ∞ → (A : Clopen ℕ∞) → A ϵ ℱ ＝ ∞ ϵ A
   I e A = 𝟚-is-¬¬-separated (A ϵ ℱ) (∞ ϵ A) II
    where
     II : ¬¬ (A ϵ ℱ ＝ ∞ ϵ A)
     II ν = ¬WLPO-gives-¬¬-has-modulus nwlpo A III
      where
       III : ¬ has-modulus A
       III (m , φ) = ν (A ϵ ℱ ＝⟨ ℱ-at-∞ e A m φ ⟩
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
  I : (ℱ : Clopen (Clopen ℕ∞)) (i : is-ultrafilter ℱ)
    → is-principal ℱ
  I ℱ i = u , ℱ-is-principal-at-u nwlpo
   where
    open ultrafilter-on-ℕ∞ ℱ i

\end{code}

As an example, Stone types are closed under binary products, as shown
above, and so ℕ∞ × ℕ∞ is a Stone type when ¬ WLPO holds.

\begin{code}

ℕ∞×ℕ∞-is-stone-type : ¬ WLPO → is-stone-type (ℕ∞ × ℕ∞)
ℕ∞×ℕ∞-is-stone-type nwlpo
 = ×-is-stone-type
    (ℕ∞-is-stone-type nwlpo)
    (ℕ∞-is-stone-type nwlpo)

\end{code}

ℕ∞ is a Stone type precisely when every ultrafilter that contains all
the upper sets is principal at ∞.

\begin{code}

Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞ : 𝓤₀ ̇
Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞ =
   (ℱ : Clopen (Clopen ℕ∞))
 → is-ultrafilter ℱ
 → ((n : ℕ) → ↑ n ∈ ℱ)
 → (A : Clopen ℕ∞) → A ϵ ℱ ＝ ∞ ϵ A

stone-gives-principal-at-∞
 : is-stone-type ℕ∞
 → Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞
stone-gives-principal-at-∞ ζ ℱ i ψ
 = I (ultrafilters-of-pre-stone-types-are-principal
       (stone-types-are-pre-stone-types ζ) ℱ i)
 where
  I : is-principal ℱ
    → (A : Clopen ℕ∞) → A ϵ ℱ ＝ ∞ ϵ A
  I (u , φ) A = A ϵ ℱ ＝⟨ φ A ⟩
                u ϵ A ＝⟨ ap A II ⟩
                ∞ ϵ A ∎
   where
    II : u ＝ ∞
    II = ℕ∞-to-ℕ→𝟚-lc fe (dfunext fe III)
     where
      III : (n : ℕ) → ι u n ＝ ι ∞ n
      III n = ι u n   ＝⟨ (φ (↑ n))⁻¹ ⟩
              ↑ n ϵ ℱ ＝⟨ ψ n ⟩
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
  I : (ℱ : Clopen (Clopen ℕ∞)) (i : is-ultrafilter ℱ)
    → is-principal ℱ
  I ℱ i = u , ℱ-is-principal-at-u-criterion (λ e → φ ℱ i (ℱ-at-upper-sets e))
   where
    open ultrafilter-on-ℕ∞ ℱ i

ℕ∞-is-stone-type-iff-principal-at-∞
 : is-stone-type ℕ∞
 ↔ Ultrafilters-Containing-All-Upper-Sets-Are-Principal-At-∞
ℕ∞-is-stone-type-iff-principal-at-∞
 = stone-gives-principal-at-∞ ,
   principal-at-∞-gives-stone

\end{code}

That ℕ∞ is a Stone type is not provable without a hypothesis such as ¬
WLPO. With choice there is a nonprincipal ultrafilter on ℕ, which is
an ultrafilter of the clopens of ℕ∞ that is not principal at any
point, so that ℕ∞ is not a Stone type in such a model.  That ¬ WLPO
holds is sufficient for ℕ∞ to be a Stone type, but it is not
necessary. It is consistent with ZF that every ultrafilter on every
set is principal, by a model of Blass [2] where the ultrafilters on ℕ
are all principal. In the model of Blass excluded middle holds, and
hence so does WLPO, and ℕ∞ is the set ℕ + 𝟙. Every subset of ℕ + 𝟙 is
decidable, so the clopens of ℕ∞ are the characteristic functions of
all the subsets of ℕ + 𝟙, and the ultrafilters of the clopens are the
ultrafilters of the powerset of ℕ + 𝟙, which are all principal. So ℕ∞
is a Stone type in that model.

The module Ordinals.BrouwerCodesGiveStoneTypes generalizes the above
result for ℕ∞, again assuming that ¬ WLPO holds, to the compact
totally separated interpretation of the Brouwer ordinal codes, of
which ℕ∞ is the interpretation of the code for the first infinite
ordinal.

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

The Stone types of [1] **are** closed under Σ, by their Theorem 4.18, but
the notion of a Stone type considered there is not the same as ours.
The Stone spaces there are the spectra of the countably presented
boolean algebras, and the boolean algebra of clopens of such a space
is overtly discrete, so that the equality of two clopens is open
rather than decidable, and becomes decidable only when it is closed as
well, by their Corollary 1.22. So their Stone spaces are not Π-compact
in general, whereas our definition includes Π-compactness via the
discreteness of the type of clopens. Their proof of the closure under
Σ appeals to their Axiom 3, local choice, in their Lemma 4.11, to
replace data that varies pointwise over the base by data uniform in
the base. Our definition lacks precisely that, as we saw above, where
a sum of Stone types over a Stone type is a Stone type when the
clopens of the fibers are restrictions of clopens of the sum, and that
condition is refutable when ¬ WLPO holds.

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
ultrafilter of the clopens of such a type is nonprincipal, and ℕ∞ is
compact and totally separated, whereas with choice there is a
nonprincipal ultrafilter of the clopens of ℕ∞, as discussed
above. Hence the statement is not provable.

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
 → (ℱ : Clopen (Clopen X))
 → is-ultrafilter ℱ
 → is-principal ℱ
ultrafilters-on-compact-totally-separated-types-are-principal c X κ τ ℱ i
 = ultrafilters-of-pre-stone-types-are-principal
    (stone-types-are-pre-stone-types (c X κ τ)) ℱ i

ultrafilters-on-ℕ∞-are-principal
 : Compact-Totally-Separated-Types-Are-Stone-Types 𝓤₀
 → (ℱ : Clopen (Clopen ℕ∞))
 → is-ultrafilter ℱ
 → is-principal ℱ
ultrafilters-on-ℕ∞-are-principal c
 = ultrafilters-on-compact-totally-separated-types-are-principal
    c
    ℕ∞
    ℕ∞-compact
    (ℕ∞-is-totally-separated fe)

nonprincipal-ultrafilter-on-ℕ∞-gives-failure
 : (ℱ : Clopen (Clopen ℕ∞))
 → is-ultrafilter ℱ
 → is-nonprincipal ℱ
 → ¬ Compact-Totally-Separated-Types-Are-Stone-Types 𝓤₀
nonprincipal-ultrafilter-on-ℕ∞-gives-failure ℱ i ν c
 = ν (ultrafilters-on-ℕ∞-are-principal c ℱ i)

\end{code}
