Martin Escardo, 20th December 2021

Some thoughts about Dedekind reals.

A proper development of Dedekind reals is at Dedekind.index, by Andrew
Sneap, started March 2021. Here we duplicate some definitions, and the
aim is to explore ideas about Dedekind reals, and not to define a
library of Dedekind reals, like Andrew has done.

A Dedekind real in constructive type theory is defined as a triple
(L , U , p) where L and U are data, namely given sets of rational
numbers, and p is property of (L , U).

But actually, given a lower Dedekind section L, there is at most one
pair (U , p) such that (L , U , p) is a Dedekind real. Hence the
Dedekind data (U , p) is property of the lower real L rather than
data. A more precise statement of this phenomenon is given below.

We generalize the rationals to any type with a proposition-valued,
irreflexive relation _<_, simply to avoid having to define the
rational numbers, but also because we could replace the rationals by
e.g. the dyadic rationals, or indeed by any dense countable subset.
But also it is interesting than nothing other than a
proposition-valued irreflexive relation is needed for the above
discussion.

We also discuss a version of the Dedekind reals proposed by Troelstra.
To show that it agrees with the usual one, we further assume that _<_
is dense, upper open, and satisfies p ≠ q → p ≮ q → p < q (which the
type of rationals does).

We also discuss what happens when we assume the principle of
excluded middle.

Here we adopt HoTT/UF as our type-theoretic foundation, which, in
particular, is well-suited to discuss the distinction between data and
property. The univalence axiom is not used anywhere here, but we
mention it in some discussions.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import Naturals.Order hiding (<-≤-trans)
open import Notation.CanonicalMap
open import Notation.Order
open import TypeTopology.CompactTypes
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module Various.Dedekind
        (pt                   : propositional-truncations-exist)
        (fe                   : Fun-Ext)
        (pe                   : Prop-Ext)
        {𝓤                    : Universe}
        (ℚ                    : 𝓤 ̇ )
        (_<-ℚ-ℚ_              : ℚ → ℚ → 𝓤 ̇ )
        (<-ℚ-ℚ-is-prop-valued : (p q : ℚ) → is-prop (p <-ℚ-ℚ q))
        (<-ℚ-ℚ-irrefl         : (q : ℚ) → ¬ (q <-ℚ-ℚ q))
       where

open PropositionalTruncation pt
open inhabited-subsets pt

instance
 strict-order-ℚ : Strict-Order ℚ ℚ
 _<_ {{strict-order-ℚ}} = _<-ℚ-ℚ_

𝓤⁺ = 𝓤 ⁺

\end{code}

Lower-real conditions:

\begin{code}

is-lower : 𝓟 ℚ → 𝓤 ̇
is-lower L = (q : ℚ) → q ∈ L → (p : ℚ) → p < q → p ∈ L

is-upper-open : 𝓟 ℚ → 𝓤 ̇
is-upper-open L = (p : ℚ) → p ∈ L → ∃ p' ꞉ ℚ , ((p < p') × p' ∈ L)

is-lower-real : 𝓟 ℚ → 𝓤 ̇
is-lower-real L = is-inhabited L × is-lower L × is-upper-open L

\end{code}

Upper-real conditions:

\begin{code}

is-upper : 𝓟 ℚ → 𝓤 ̇
is-upper U = (p : ℚ) → p ∈ U → (q : ℚ) → p < q → q ∈ U

is-lower-open : 𝓟 ℚ → 𝓤 ̇
is-lower-open U = (q : ℚ) → q ∈ U → ∃ q' ꞉ ℚ , ((q' < q) × q' ∈ U)

is-upper-real : 𝓟 ℚ → 𝓤 ̇
is-upper-real U = is-inhabited U × is-upper U × is-lower-open U

\end{code}

The conditions are property:

\begin{code}

being-lower-is-prop : (L : 𝓟 ℚ) → is-prop (is-lower L)
being-lower-is-prop L = Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop L _)

being-upper-open-is-prop : (L : 𝓟 ℚ) → is-prop (is-upper-open L)
being-upper-open-is-prop L = Π₂-is-prop fe (λ _ _ → ∃-is-prop)

being-lower-real-is-prop : (L : 𝓟 ℚ) → is-prop (is-lower-real L)
being-lower-real-is-prop L = ×₃-is-prop
                              (being-inhabited-is-prop L)
                              (being-lower-is-prop L)
                              (being-upper-open-is-prop L)

being-upper-is-prop : (L : 𝓟 ℚ) → is-prop (is-upper L)
being-upper-is-prop L = Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop L _)

being-lower-open-is-prop : (L : 𝓟 ℚ) → is-prop (is-lower-open L)
being-lower-open-is-prop L = Π₂-is-prop fe (λ _ _ → ∃-is-prop)

being-upper-real-is-prop : (L : 𝓟 ℚ) → is-prop (is-upper-real L)
being-upper-real-is-prop L = ×₃-is-prop
                              (being-inhabited-is-prop L)
                              (being-upper-is-prop L)
                              (being-lower-open-is-prop L)
\end{code}

The sets of lower and upper reals:

\begin{code}

ℝᴸ : 𝓤⁺ ̇
ℝᴸ = Σ L ꞉ 𝓟 ℚ , is-lower-real L

ℝᵁ : 𝓤⁺ ̇
ℝᵁ = Σ U ꞉ 𝓟 ℚ , is-upper-real U

ℝᴸ-is-set : is-set ℝᴸ
ℝᴸ-is-set = subsets-of-sets-are-sets (𝓟 ℚ)
             is-lower-real
             (powersets-are-sets'' fe fe pe)
             (λ {l} → being-lower-real-is-prop l)

ℝᵁ-is-set : is-set ℝᵁ
ℝᵁ-is-set = subsets-of-sets-are-sets (𝓟 ℚ)
             is-upper-real
             (powersets-are-sets'' fe fe pe)
             (λ {l} → being-upper-real-is-prop l)

ℝᴸ-to-𝓟ℚ : ℝᴸ → 𝓟 ℚ
ℝᴸ-to-𝓟ℚ = pr₁

ℝᵁ-to-𝓟ℚ : ℝᵁ → 𝓟 ℚ
ℝᵁ-to-𝓟ℚ = pr₁

instance
 canonical-map-ℝᴸ-to-𝓟ℚ : Canonical-Map ℝᴸ (𝓟 ℚ)
 ι {{canonical-map-ℝᴸ-to-𝓟ℚ}} = ℝᴸ-to-𝓟ℚ

 canonical-map-ℝᵁ-to-𝓟ℚ : Canonical-Map ℝᵁ (𝓟 ℚ)
 ι {{canonical-map-ℝᵁ-to-𝓟ℚ}} = ℝᵁ-to-𝓟ℚ

ℝᴸ-to-𝓟ℚ-is-embedding : is-embedding (canonical-map ℝᴸ (𝓟 ℚ))
ℝᴸ-to-𝓟ℚ-is-embedding = pr₁-is-embedding being-lower-real-is-prop

ℝᵁ-to-𝓟ℚ-is-embedding : is-embedding (canonical-map ℝᵁ (𝓟 ℚ))
ℝᵁ-to-𝓟ℚ-is-embedding = pr₁-is-embedding being-upper-real-is-prop

\end{code}

Next we define the set of Dedekind reals as a subset of the lower
reals, after some preparation.

\begin{code}

are-ordered : 𝓟 ℚ → 𝓟 ℚ → 𝓤 ̇
are-ordered L U = (p q : ℚ) → p ∈ L → q ∈ U → p < q

are-located : 𝓟 ℚ → 𝓟 ℚ → 𝓤 ̇
are-located L U = (p q : ℚ) → p < q → p ∈ L ∨ q ∈ U

being-ordered-is-prop : (L U : 𝓟 ℚ) → is-prop (are-ordered L U)
being-ordered-is-prop _ _ = Π₄-is-prop fe (λ _ _ _ _ → <-ℚ-ℚ-is-prop-valued _ _)

being-located-is-prop : (L U : 𝓟 ℚ) → is-prop (are-located L U)
being-located-is-prop _ _ = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

order-lemma : (L U L' U' : 𝓟 ℚ)
            → is-lower-open U'
            → are-located L  U
            → are-ordered L' U'
            → L  ⊆ L'
            → U' ⊆ U
order-lemma L U L' U'
            U'-lower-open
            LU-located
            LU'-ordered
            L-contained-in-L'
            q
            q-in-U'             = γ
 where
  I : ∃ q' ꞉ ℚ , (q' < q) × q' ∈ U'
  I = U'-lower-open q q-in-U'

  II : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ U') → q ∈ U
  II (q' , l , i) = VI
   where
    III : q' ∈ L ∨ q ∈ U
    III = LU-located q' q l

    IV : q' ∉ L
    IV j = <-ℚ-ℚ-irrefl q' b
     where
      a : q' ∈ L'
      a = L-contained-in-L' q' j

      b : q' < q'
      b = LU'-ordered q' q' a i

    V : (q' ∈ L) + (q ∈ U) → q ∈ U
    V (inl j) = 𝟘-elim (IV j)
    V (inr k) = k

    VI : q ∈ U
    VI = ∥∥-rec (∈-is-prop U q) V III

  γ : q ∈ U
  γ = ∥∥-rec (∈-is-prop U q) II I

order-lemma-converse : (L U L' U' : 𝓟 ℚ)
                     → is-upper-open L
                     → are-located L' U'
                     → are-ordered L  U
                     → U' ⊆ U
                     → L  ⊆ L'
order-lemma-converse L U L' U'
                     L-upper-open
                     LU'-located
                     LU-ordered
                     U'-contained-in-U
                     q
                     q-in-L             = γ
 where
  I : ∃ q' ꞉ ℚ , (q < q') × q' ∈ L
  I = L-upper-open q q-in-L

  II : (Σ q' ꞉ ℚ , (q < q') × q' ∈ L) → q ∈ L'
  II (q' , l , i) = VI
   where
    III : q ∈ L' ∨ q' ∈ U'
    III = LU'-located q q' l

    IV : q' ∉ U'
    IV j = <-ℚ-ℚ-irrefl q' b
     where
      a : q' ∈ U
      a = U'-contained-in-U q' j

      b : q' < q'
      b = LU-ordered q' q' i a

    V : (q ∈ L') + (q' ∈ U') → q ∈ L'
    V (inl j) = j
    V (inr k) = 𝟘-elim (IV k)

    VI : q ∈ L'
    VI = ∥∥-rec (∈-is-prop L' q) V III

  γ : q ∈ L'
  γ = ∥∥-rec (∈-is-prop L' q) II I

\end{code}

The following definition is of an auxiliary character:

\begin{code}

_is-an-upper-section-of_ : 𝓟 ℚ → 𝓟 ℚ → 𝓤 ̇
U is-an-upper-section-of L = is-lower-open U × are-ordered L U × are-located L U

any-two-upper-sections-are-equal : (L U U' : 𝓟 ℚ)
                                 → U  is-an-upper-section-of L
                                 → U' is-an-upper-section-of L
                                 → U ＝ U'
any-two-upper-sections-are-equal L U U' (a , b , c) (u , v , w) = γ
 where
  i : U ⊆ U'
  i = order-lemma L U' L U  a w b (⊆-refl' L)

  j : U ⊇ U'
  j = order-lemma L U  L U' u c v (⊆-refl' L)

  γ : U ＝ U'
  γ = subset-extensionality'' pe fe fe i j

\end{code}

The following is the version of the definition we are interested in:

\begin{code}

_is-upper-section-of_ : ℝᵁ → ℝᴸ → 𝓤 ̇
(U , _) is-upper-section-of  (L , _) = are-ordered L U × are-located L U

being-upper-section-is-prop : (x : ℝᴸ) (y : ℝᵁ)
                            → is-prop (y is-upper-section-of x)
being-upper-section-is-prop (L , _) (U , _) = ×-is-prop
                                               (being-ordered-is-prop L U)
                                               (being-located-is-prop L U)
\end{code}

We use the above auxiliary definition and lemma to establish the following:

\begin{code}

at-most-one-upper-section : (l : ℝᴸ) (u₀ u₁ : ℝᵁ)
                          → u₀ is-upper-section-of l
                          → u₁ is-upper-section-of l
                          → u₀ ＝ u₁
at-most-one-upper-section (L , _)
                          u₀@(U₀ , _ , _ , U₀-is-lower-open)
                          u₁@(U₁ , _ , _ , U₁-is-lower-open)
                          (lu₀-ordered , lu₀-located)
                          (lu₁-ordered , lu₁-located)      = γ
 where
  γ : u₀ ＝ u₁
  γ = to-subtype-＝
       being-upper-real-is-prop
       (any-two-upper-sections-are-equal L U₀ U₁
        (U₀-is-lower-open , lu₀-ordered , lu₀-located)
        (U₁-is-lower-open , lu₁-ordered , lu₁-located))

\end{code}

The Dedekind condition for a lower real:

\begin{code}

is-dedekind : ℝᴸ → 𝓤⁺ ̇
is-dedekind l = Σ u ꞉ ℝᵁ , (u is-upper-section-of l)

being-dedekind-is-prop : (l : ℝᴸ) → is-prop (is-dedekind l)
being-dedekind-is-prop l (u₀ , p₀) (u₁ , p₁) =
 to-subtype-＝
  (being-upper-section-is-prop l)
  (at-most-one-upper-section l u₀ u₁ p₀ p₁)

\end{code}

We define the Dedekind reals as a subset of the lower reals:

\begin{code}

ℝ : 𝓤⁺ ̇
ℝ = Σ l ꞉ ℝᴸ , is-dedekind l

\end{code}

The forgetful map of the reals into the lower reals is an embedding
and hence ℝ is a set:

\begin{code}

ℝ-to-ℝᴸ : ℝ → ℝᴸ
ℝ-to-ℝᴸ = pr₁

ℝ-to-ℝᴸ-is-embedding : is-embedding ℝ-to-ℝᴸ
ℝ-to-ℝᴸ-is-embedding = pr₁-is-embedding being-dedekind-is-prop

ℝ-is-set : is-set ℝ
ℝ-is-set = subsets-of-sets-are-sets ℝᴸ
            is-dedekind
            ℝᴸ-is-set
            (λ {l} → being-dedekind-is-prop l)

instance
 canonical-map-ℝ-to-ℝᴸ : Canonical-Map ℝ ℝᴸ
 ι {{canonical-map-ℝ-to-ℝᴸ}} = ℝ-to-ℝᴸ

\end{code}

NB. This won't be a *topological* embedding in topological
models. Because ℝ and ℝᴸ are sets, in the sense of HoTT/UF, the
embedding condition merely says that the map is left-cancellable.

We unpack and reorder the definition to emphasize that it amounts to
the usual one:

\begin{code}

is-dedekind-section : 𝓟 ℚ × 𝓟 ℚ → 𝓤 ̇
is-dedekind-section (L , U) = is-inhabited L × is-lower L × is-upper-open L
                            × is-inhabited U × is-upper U × is-lower-open U
                            × are-ordered L U × are-located L U


NB₁ : ℝ ≃ (Σ (L , R) ꞉ 𝓟 ℚ × 𝓟 ℚ , is-dedekind-section (L , R))
NB₁ = qinveq
       (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
         → ((L , U) , Li , Ll , Lo , Ui , Uu , Uo , o , l))
       ((λ ((L , U) , Li , Ll , Lo , Ui , Uu , Uo , o , l)
         → ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)) ,
        (λ _ → refl) ,
        (λ _ → refl))

\end{code}

The following shows that there is some redundancy in the definition of
Dedekind real:

\begin{code}

ordered-located-gives-lower : (L U : 𝓟 ℚ)
                            → are-ordered L U
                            → are-located L U
                            → is-lower L
ordered-located-gives-lower L U LU-ordered LU-located = γ
 where
  γ : is-lower L
  γ q l p m = ∥∥-rec (∈-is-prop L p) b a
   where
    a : p ∈ L ∨ q ∈ U
    a = LU-located p q m

    b : (p ∈ L) + (q ∈ U) → p ∈ L
    b (inl u) = u
    b (inr v) = 𝟘-elim (<-ℚ-ℚ-irrefl q (LU-ordered q q l v))

ordered-located-gives-upper : (L U : 𝓟 ℚ)
                            → are-ordered L U
                            → are-located L U
                            → is-upper U
ordered-located-gives-upper L U LU-ordered LU-located = γ
 where
  γ : is-upper U
  γ q l p m = ∥∥-rec (∈-is-prop U p) b a
   where
    a : q ∈ L ∨ p ∈ U
    a = LU-located q p m

    b : (q ∈ L) + (p ∈ U) → p ∈ U
    b (inl u) = 𝟘-elim (<-ℚ-ℚ-irrefl q (LU-ordered q q u l))
    b (inr v) = v


NB₂ : ℝ ≃ (Σ (L , U) ꞉ 𝓟 ℚ × 𝓟 ℚ
                     , is-inhabited L × is-upper-open L
                     × is-inhabited U × is-lower-open U
                     × are-ordered L U × are-located L U)
NB₂ = qinveq
       (λ ((L , Li , _ , Lo) , (U , Ui , _ , Uo) , o , l)
         → ((L , U) , Li , Lo , Ui , Uo , o , l))

       ((λ ((L , U) , Li , Lo , Ui , Uo , o , l)
         → ((L , Li , ordered-located-gives-lower L U o l , Lo) ,
            (U , Ui , ordered-located-gives-upper L U o l , Uo) ,
            o , l)) ,
        (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
          → to-subtype-＝ being-dedekind-is-prop
             (to-subtype-＝ being-lower-real-is-prop refl)) ,
        (λ ((L , U) , Li , Lo , Ui , Uo , o , l)
         → to-subtype-＝ (λ (L , U) → ×₆-is-prop
                                      (being-inhabited-is-prop L)
                                      (being-upper-open-is-prop L)
                                      (being-inhabited-is-prop U)
                                      (being-lower-open-is-prop U)
                                      (being-ordered-is-prop L U)
                                      (being-located-is-prop L U))
             refl))
\end{code}

Sometimes a disjointness condition rather than the order condition is
used in the definition of Dedekind reals.

\begin{code}

disjoint-criterion : (L U : 𝓟 ℚ)
                   → are-ordered L U
                   → are-disjoint L U
disjoint-criterion L U o p (p-in-L , p-in-U) = <-ℚ-ℚ-irrefl p (o p p p-in-L p-in-U)

\end{code}

From now on we assume the properties of ℚ and its order alluded above,
and a few more:

\begin{code}

module ℚ-assumptions
        (ℚ-density         : (p r : ℚ) → p < r → Σ q ꞉ ℚ , (p < q) × (q < r))
        (ℚ-transitivity    : (p q r : ℚ) → p < q → q < r → p < r)
        (ℚ-order-criterion : (p q : ℚ) → q ≮ p → p ≠ q → p < q)
        (ℚ-cotransitivity  : (p q r : ℚ) → p < r → (p < q) ∨ (q < r))
        (ℚ-tightness       : (p q : ℚ) → q ≮ p → p ≮ q → p ＝ q)
        (ℚ-is-lower-open   : (q : ℚ) → ∃ p ꞉ ℚ , (p < q))
        (ℚ-is-upper-open   : (p : ℚ) → ∃ q ꞉ ℚ , (p < q))
        (𝟎 ½ 𝟏             : ℚ)
        (𝟎-is-less-than-½  : 𝟎 < ½)
        (½-is-less-than-𝟏  : ½ < 𝟏)
      where

 𝟎-is-less-than-𝟏 : 𝟎 < 𝟏
 𝟎-is-less-than-𝟏 = ℚ-transitivity 𝟎 ½ 𝟏 𝟎-is-less-than-½ ½-is-less-than-𝟏

 instance
  order-ℚ-ℚ : Order ℚ ℚ
  _≤_ {{order-ℚ-ℚ}} p q = (r : ℚ) → r < p → r < q

 ℚ-≤-antisym : (p q : ℚ) → p ≤ q → q ≤ p → p ＝ q
 ℚ-≤-antisym p q i j = ℚ-tightness p q (λ ℓ → <-ℚ-ℚ-irrefl q (i q ℓ))
                                       (λ ℓ → <-ℚ-ℚ-irrefl p (j p ℓ))

 <-or-＝-gives-≤-on-ℚ : (p q : ℚ) → (p < q) + (p ＝ q) → p ≤ q
 <-or-＝-gives-≤-on-ℚ p q (inl ℓ)    r m = ℚ-transitivity r p q m ℓ
 <-or-＝-gives-≤-on-ℚ p q (inr refl) r ℓ = ℓ

 ℚ-trichotomy = (p q : ℚ) → (p < q) + (p ＝ q) + (p > q)

 ≤-on-ℚ-gives-＝-or-< : ℚ-trichotomy
                     → (p q : ℚ) → p ≤ q → (p < q) + (p ＝ q)
 ≤-on-ℚ-gives-＝-or-< τ p q ℓ = γ (τ p q)
  where
   I : q ≮ p
   I m = <-ℚ-ℚ-irrefl q (ℓ q m)

   γ : (p < q) + (p ＝ q) + (p > q) → (p < q) + (p ＝ q)
   γ (inl i)       = inl i
   γ (inr (inl e)) = inr e
   γ (inr (inr j)) = 𝟘-elim (I j)

 ordered-criterion : (L U : 𝓟 ℚ)
                   → is-lower L
                   → are-disjoint L U
                   → are-ordered L U
 ordered-criterion L U L-lower LU-disjoint p q p-in-L q-in-U = γ
  where
   I : p ∉ U
   I p-in-U = LU-disjoint p (p-in-L , p-in-U)

   II : p ≠ q
   II refl = I q-in-U

   III : q ≮ p
   III ℓ = LU-disjoint q (L-lower p p-in-L q ℓ , q-in-U)

   γ : p < q
   γ = ℚ-order-criterion p q III II

\end{code}

The following alternative definition of the Dedekind reals is often
found in the literature:

\begin{code}

 NB₃ : ℝ ≃ (Σ (L , U) ꞉ 𝓟 ℚ × 𝓟 ℚ
                      , is-inhabited L × is-lower L × is-upper-open L
                      × is-inhabited U × is-upper U × is-lower-open U
                      × are-disjoint L U × are-located L U)
 NB₃ =
  qinveq
   (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
     → ((L , U) , Li , Ll , Lo , Ui , Uu , Uo , disjoint-criterion L U o , l))
   ((λ ((L , U) , Li , Ll , Lo , Ui , Uu , Uo , d , l)
     → ((L , Li , Ll , Lo) ,
        (U , Ui , Uu , Uo) ,
        ordered-criterion L U Ll d , l)) ,
    (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
     → to-subtype-＝ being-dedekind-is-prop
        (to-subtype-＝ being-lower-real-is-prop
          refl)) ,
    (λ ((L , U) , Li , Lo , Ui , Uo , o , l)
     → to-subtype-＝ (λ (L , U) → ×₈-is-prop
                                  (being-inhabited-is-prop L)
                                  (being-lower-is-prop L)
                                  (being-upper-open-is-prop L)
                                  (being-inhabited-is-prop U)
                                  (being-upper-is-prop U)
                                  (being-lower-open-is-prop U)
                                  (being-disjoint-is-prop fe L U)
                                  (being-located-is-prop L U))
       refl))

\end{code}

We now consider an alternative definition of the Dedekind reals
offered by Troelstra.

\begin{code}

 is-bounded-above : 𝓟 ℚ → 𝓤 ̇
 is-bounded-above L = ∃ s ꞉ ℚ , s ∉ L

 is-located : 𝓟 ℚ → 𝓤 ̇
 is-located L = ((r s : ℚ) → r < s → r ∈ L ∨ s ∉ L)

 is-troelstra : ℝᴸ → 𝓤 ̇
 is-troelstra (L , _) = is-bounded-above L × is-located L

 being-bounded-above-is-prop : (L : 𝓟 ℚ) → is-prop (is-bounded-above L)
 being-bounded-above-is-prop L = ∃-is-prop

 being-troelstra-located-is-prop : (L : 𝓟 ℚ) → is-prop (is-located L)
 being-troelstra-located-is-prop L = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

 being-troelstra-is-prop : (l : ℝᴸ) → is-prop (is-troelstra l)
 being-troelstra-is-prop (L , _) = ×-is-prop
                                    (being-bounded-above-is-prop L)
                                    (being-troelstra-located-is-prop L)
\end{code}

The Dedekind and Troelstra conditions are equivalent:

\begin{code}

 dedekind-gives-troelstra : (l : ℝᴸ) → is-dedekind l → is-troelstra l
 dedekind-gives-troelstra l@(L , _ , _ , _)
                          ((U , U-inhabited , _ , _) ,
                           LU-ordered ,
                           LU-located) = γ
  where
   bounded : (∃ s ꞉ ℚ , s ∉ L)
   bounded = ∥∥-functor f U-inhabited
    where
     f : (Σ q ꞉ ℚ , q ∈ U) → Σ q ꞉ ℚ , q ∉ L
     f (q , q-in-U) = q , (λ q-in-L → <-ℚ-ℚ-irrefl q (c q-in-L))
      where
       c : q ∈ L → q < q
       c q-in-L = LU-ordered q q q-in-L q-in-U

   located : (r s : ℚ) → r < s → r ∈ L ∨ s ∉ L
   located r s ℓ = ∥∥-functor f (LU-located r s ℓ)
    where
     f : (r ∈ L) + (s ∈ U) → (r ∈ L) + (s ∉ L)
     f (inl r-in-L) = inl r-in-L
     f (inr r-in-L) = inr (λ s-in-L → <-ℚ-ℚ-irrefl s (d s-in-L))
      where
       d : s ∈ L → s < s
       d s-in-L = LU-ordered s s s-in-L r-in-L

   γ : is-troelstra l
   γ = bounded , located

\end{code}

A lower Dedekind real may or may not have an upper section. If it
does, it is given by the following candidate.

\begin{code}

 candidate-upper-section : 𝓟 ℚ → 𝓟 ℚ
 candidate-upper-section L = λ q → (∃ p ꞉ ℚ , (p < q) × (p ∉ L)) , ∃-is-prop

 candidate-upper-section-is-lower-open
  : (L : 𝓟 ℚ)
  → is-lower-open (candidate-upper-section L)
 candidate-upper-section-is-lower-open L q q-in-U = γ
  where
   f : (Σ p ꞉ ℚ , (p < q) × (p ∉ L))
     → ∃ p' ꞉ ℚ , (p' < q) × (∃ p ꞉ ℚ , (p < p') × (p ∉ L))
   f (p , i , p-not-in-L) = g (ℚ-density p q i)
    where
     g : (Σ p' ꞉ ℚ , (p < p') × (p' < q))
       →  ∃ p' ꞉ ℚ , (p' < q) × (∃ p ꞉ ℚ , (p < p') × (p ∉ L))
     g (p' , j , k) = ∣ p' , k , ∣ p , j , p-not-in-L ∣ ∣

   γ : ∃ q' ꞉ ℚ , ((q' < q) × (q' ∈ candidate-upper-section L))
   γ = ∥∥-rec ∃-is-prop f q-in-U

 candidate-upper-section-is-ordered
  : (L : 𝓟 ℚ)
  → is-lower L
  → is-located L
  → are-ordered L (candidate-upper-section L)
 candidate-upper-section-is-ordered L L-lower located p q p-in-L q-in-U = γ
  where
   f : (Σ r ꞉ ℚ , (r < q) × (r ∉ L)) → p < q
   f (r , i , r-not-in-L) = ∥∥-rec (<-ℚ-ℚ-is-prop-valued p q) g (located r q i)
    where
     g : (r ∈ L) + (q ∉ L) → p < q
     g (inl r-in-L)     = 𝟘-elim (r-not-in-L r-in-L)
     g (inr q-not-in-L) = ℚ-order-criterion p q II I
      where
       I : p ≠ q
       I refl = q-not-in-L p-in-L

       II : q ≮ p
       II ℓ = q-not-in-L (L-lower p p-in-L q ℓ)

   γ : p < q
   γ = ∥∥-rec (<-ℚ-ℚ-is-prop-valued p q) f q-in-U

 candidate-upper-section-is-located
  : (L : 𝓟 ℚ)
  → is-located L
  → are-located L (candidate-upper-section L)
 candidate-upper-section-is-located L located p q ℓ = ∥∥-rec ∨-is-prop II I
  where
   I : ∃ p' ꞉ ℚ , (p < p') × (p' < q)
   I = ∣ ℚ-density p q ℓ ∣

   II : (Σ p' ꞉ ℚ , (p < p') × (p' < q)) → p ∈ L ∨ q ∈ candidate-upper-section L
   II (p' , i , j) = ∥∥-rec ∨-is-prop IV III
    where
     III : p ∈ L ∨ p' ∉ L
     III = located p p' i

     IV : (p ∈ L) + (p' ∉ L) → p ∈ L ∨ q ∈ candidate-upper-section L
     IV (inl p-in-L)      = ∣ inl p-in-L ∣
     IV (inr p'-not-in-L) = ∣ inr ∣ (p' , j , p'-not-in-L) ∣ ∣

 candidate-upper-section-is-inhabited
  : (L : 𝓟 ℚ)
  → is-bounded-above L
  → is-inhabited (candidate-upper-section L)
 candidate-upper-section-is-inhabited L bounded =  γ
  where
   f : (Σ s ꞉ ℚ , s ∉ L) → is-inhabited (candidate-upper-section L)
   f (s , ν) = ∥∥-functor g (ℚ-is-upper-open s)
    where
     g : (Σ p ꞉ ℚ , s < p) → Σ p ꞉ ℚ , p ∈ candidate-upper-section L
     g (p , i) = p , ∣ s , i , ν ∣

   γ : is-inhabited (candidate-upper-section L)
   γ = ∥∥-rec (being-inhabited-is-prop (candidate-upper-section L)) f bounded

 candidate-upper-section-is-upper
  : (L : 𝓟 ℚ)
  → is-lower L
  → is-located L
  → is-upper (candidate-upper-section L)
 candidate-upper-section-is-upper L lower located p p-in-U q ℓ = γ
  where
   γ : ∃ q' ꞉ ℚ , (q' < q) × (q' ∉ L)
   γ = ∣ p ,
        ℓ ,
        (λ p-in-L → <-ℚ-ℚ-irrefl p
                     (candidate-upper-section-is-ordered
                       L lower located p p p-in-L p-in-U)) ∣
\end{code}

The candidate upper section is the unique candidate in the following
sense:

\begin{code}

 unique-candidate
  : (L U : 𝓟 ℚ)
  → is-dedekind-section (L , U)
  → U ＝ candidate-upper-section L
 unique-candidate L U (Li , Ll , Lo , Ui , Uu , Uo , ordered , located) = γ
  where
   l : ℝᴸ
   l = (L , Li , Ll , Lo)

   u : ℝᵁ
   u = (U , Ui , Uu , Uo)

   I : is-dedekind l
   I = u , ordered , located

   II : is-located L
   II = pr₂ (dedekind-gives-troelstra l I)

   III : (candidate-upper-section L) is-an-upper-section-of L
   III = candidate-upper-section-is-lower-open L ,
         candidate-upper-section-is-ordered L Ll II ,
         candidate-upper-section-is-located L II

   γ : U ＝ candidate-upper-section L
   γ = any-two-upper-sections-are-equal L U
        (candidate-upper-section L)
        (Uo , ordered , located)
        III

\end{code}

And, as promised, the Troelstra condition implies the Dedekind condition:

\begin{code}

 troelstra-gives-dedekind : (l : ℝᴸ) → is-troelstra l → is-dedekind l
 troelstra-gives-dedekind l@(L , L-inhabited , L-lower , L-upper-open)
                            (bounded , located) = γ
  where
   γ : is-dedekind l
   γ = ((candidate-upper-section L ,
         (candidate-upper-section-is-inhabited L bounded ,
          candidate-upper-section-is-upper L L-lower located ,
          candidate-upper-section-is-lower-open L)) ,
        candidate-upper-section-is-ordered L L-lower located ,
        candidate-upper-section-is-located L located)

\end{code}

The set of Troelstra reals, again as a subset of the lower reals:

\begin{code}

 ℝᵀ : 𝓤⁺ ̇
 ℝᵀ = Σ l ꞉ ℝᴸ , is-troelstra l

\end{code}

Question. Can we prove that ℝ = ℝᵀ with propositional and functional
extensionality, without univalence? The problem is that the Dedekind
condition and the troelstra condition have different universe levels,
and hence propositional extensionality is not applicable to show that
they are equal, as their equality doesn't even type check. Would
universe lifting help? I haven't thought about this.

\begin{code}

 dedekind-agrees-with-troelstra : ℝ ≃ ℝᵀ
 dedekind-agrees-with-troelstra = γ
  where
   f : ℝ → ℝᵀ
   f (l , h) = l , dedekind-gives-troelstra l h

   g : ℝᵀ → ℝ
   g (l , k) = l , troelstra-gives-dedekind l k

   γ : ℝ ≃ ℝᵀ
   γ = qinveq f (g ,
                (λ (l , h) → to-subtype-＝ being-dedekind-is-prop refl) ,
                (λ (l , k) → to-subtype-＝ being-troelstra-is-prop refl))
\end{code}

We now consider consequences of excluded middle. Notice that if A is a
proposition, then so is A + ¬ A, and thus A + ¬ A is equivalent to A ∨ ¬ A.

\begin{code}

 LEM = (A : 𝓤 ̇ ) → is-prop A → A + ¬ A

 LEM-gives-locatedness : LEM → ((L , _) : ℝᴸ) → is-located L
 LEM-gives-locatedness
  lem l@(L , L-inhabited , L-lower , L-upper-open) r s ℓ = γ δ
  where
   δ : (s ∈ L) + (s ∉ L)
   δ = lem (s ∈ L) (∈-is-prop L s)

   γ : type-of δ → (r ∈ L) ∨ (s ∉ L)
   γ (inl s-in-L)     = ∣ inl (L-lower s s-in-L r ℓ) ∣
   γ (inr s-not-in-L) = ∣ inr s-not-in-L ∣

\end{code}

The bounded lower reals:

\begin{code}

 ℝᴮᴸ : 𝓤⁺ ̇
 ℝᴮᴸ = Σ (L , _) ꞉ ℝᴸ , is-bounded-above L

\end{code}

The boundedness condition only excludes a point at infinity in the
lower reals:

\begin{code}

 infty : 𝓟 ℚ
 infty = λ _ → ⊤

 infty-is-lower-real : is-lower-real infty
 infty-is-lower-real = ∣ 𝟎 , ⋆ ∣ ,
                       (λ _ _ _ _ → ⋆) ,
                       (λ p ⋆ → ∥∥-rec
                                 ∃-is-prop
                                 (λ (q , i) → ∣ q , i , ⋆ ∣)
                                 (ℚ-is-upper-open p))

 infty-is-not-bounded-above : ¬ is-bounded-above infty
 infty-is-not-bounded-above bounded =
  ∥∥-rec
   𝟘-is-prop
   (λ (q , q-not-in-infty) → q-not-in-infty ⋆)
   bounded

\end{code}

In connection with a discussion above, notice that we don't need
univalence for the following, which says that the Troelstra reals
agree with the bounded lower reals if we assume excluded middle:

\begin{code}

 ℝᵀ-and-ℝᴮᴸ-agree-under-LEM : LEM → ℝᵀ ＝ ℝᴮᴸ
 ℝᵀ-and-ℝᴮᴸ-agree-under-LEM lem = ap Σ γ
  where
   δ : is-troelstra ∼ λ (L , _) → is-bounded-above L
   δ l@(L , _) = pe (being-troelstra-is-prop l)
                    (being-bounded-above-is-prop L)
                    pr₁
                    (λ β → β , LEM-gives-locatedness lem l)

   γ : is-troelstra ＝ (λ (L , _) → is-bounded-above L)
   γ = dfunext fe δ

\end{code}

Therefore, under excluded middle, the Dedekind reals agree with the
bounded lower reals:

\begin{code}

 ℝ-and-ℝᴮᴸ-agree-under-LEM : LEM → ℝ ≃ ℝᴮᴸ
 ℝ-and-ℝᴮᴸ-agree-under-LEM lem = transport (ℝ ≃_)
                                  (ℝᵀ-and-ℝᴮᴸ-agree-under-LEM lem)
                                  (dedekind-agrees-with-troelstra)
\end{code}

It follows that bounded lower reals are Dedekind under excluded middle.

\begin{code}

 LEM-gives-all-bounded-lower-reals-are-dedekind
  : LEM
  → ((l , _) : ℝᴮᴸ) → is-dedekind l
 LEM-gives-all-bounded-lower-reals-are-dedekind lem (l , bounded) = γ
  where
   γ : is-dedekind l
   γ = troelstra-gives-dedekind l (bounded , LEM-gives-locatedness lem l)

\end{code}

And the converse also holds. We use a method of proof suggested
independently by Steve Vickers and Toby Bartels.

\begin{code}

 all-bounded-lower-reals-are-dedekind-gives-LEM
  : (((l , _) : ℝᴮᴸ) → is-dedekind l)
  → LEM
 all-bounded-lower-reals-are-dedekind-gives-LEM α A A-is-prop = γ
  where
   L : 𝓟 ℚ
   L p = ((p < 𝟎) ∨ (A × (p < 𝟏))) , ∨-is-prop

   L-inhabited : is-inhabited L
   L-inhabited = ∥∥-functor h (ℚ-is-lower-open 𝟎)
    where
     h : (Σ p ꞉ ℚ , p < 𝟎) → Σ p ꞉ ℚ , p ∈ L
     h (p , ℓ) = p , ∣ inl ℓ ∣

   L-lower : is-lower L
   L-lower p p-in-L p' j = ∥∥-functor h p-in-L
    where
     h : (p < 𝟎) + (A × (p < 𝟏)) → (p' < 𝟎) + (A × (p' < 𝟏))
     h (inl ℓ)       = inl (ℚ-transitivity p' p 𝟎 j ℓ)
     h (inr (a , ℓ)) = inr (a , ℚ-transitivity p' p 𝟏 j ℓ)

   L-upper-open : is-upper-open L
   L-upper-open p p-in-L = ∥∥-rec ∃-is-prop h p-in-L
    where
     h : (p < 𝟎) + (A × (p < 𝟏)) → ∃ p' ꞉ ℚ , (p < p') × (p' ∈ L)
     h (inl ℓ) = k (ℚ-density p 𝟎 ℓ)
      where
       k : (Σ p' ꞉ ℚ , (p < p') × (p' < 𝟎)) → ∃ p' ꞉ ℚ , (p < p') × (p' ∈ L)
       k (p' , i , j) = ∣ p' , i , ∣ inl j ∣ ∣
     h (inr (a , ℓ)) = k (ℚ-density p 𝟏 ℓ)
      where
       k : (Σ p' ꞉ ℚ , (p < p') × (p' < 𝟏)) → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
       k (p' , i , j) = ∣ p' , i , ∣ inr (a , j) ∣ ∣

   l : ℝᴸ
   l = (L , L-inhabited , L-lower , L-upper-open)

   l-dedekind-gives-A-decidable : is-dedekind l → A + ¬ A
   l-dedekind-gives-A-decidable ((U , _ , _) , LU-ordered , LU-located) = δ
    where
     δ : A + ¬ A
     δ = ∥∥-rec
          (decidability-of-prop-is-prop fe A-is-prop)
          h
          (LU-located 𝟎 ½ 𝟎-is-less-than-½)
      where
       h : (𝟎 ∈ L) + (½ ∈ U) → A + ¬ A
       h (inl 𝟘-in-L) = inl (∥∥-rec A-is-prop k 𝟘-in-L)
        where
         k : (𝟎 < 𝟎) + (A × (𝟎 < 𝟏)) → A
         k (inl ℓ)       = 𝟘-elim (<-ℚ-ℚ-irrefl 𝟎 ℓ)
         k (inr (a , _)) = a
       h (inr ½-in-U) = inr ν
        where
         ν : ¬ A
         ν a = disjoint-criterion L U LU-ordered ½ (½-in-L , ½-in-U)
          where
           ½-in-L : ½ ∈ L
           ½-in-L = ∣ inr (a , ½-is-less-than-𝟏) ∣

   L-bounded-above : is-bounded-above L
   L-bounded-above = ∣ 𝟏 , (λ 𝟏-in-L → ∥∥-rec 𝟘-is-prop h 𝟏-in-L) ∣
    where
     h : ¬((𝟏 < 𝟎) + (A × (𝟏 < 𝟏)))
     h (inl ℓ)       = <-ℚ-ℚ-irrefl 𝟎 (ℚ-transitivity 𝟎 𝟏 𝟎 𝟎-is-less-than-𝟏 ℓ)
     h (inr (_ , ℓ)) = <-ℚ-ℚ-irrefl 𝟏 ℓ

   b : ℝᴮᴸ
   b = (l , L-bounded-above)

   γ : A + ¬ A
   γ = l-dedekind-gives-A-decidable (α b)

\end{code}

The canonical embedding of the rationals into the reals:

\begin{code}

 ℚ-to-ℝᴸ : ℚ → ℝᴸ
 ℚ-to-ℝᴸ q = (λ p → (p < q) , <-ℚ-ℚ-is-prop-valued p q) ,
             ℚ-is-lower-open q ,
             (λ p i r j → ℚ-transitivity r p q j i) ,
             (λ p i → ∣ ℚ-density p q i ∣)

 ℚ-to-ℝᵁ : ℚ → ℝᵁ
 ℚ-to-ℝᵁ q = (λ p → (q < p) , <-ℚ-ℚ-is-prop-valued q p) ,
             ℚ-is-upper-open q ,
             (λ p i r j → ℚ-transitivity q p r i j) ,
             (λ p i → ∣(λ (r , j , k) → r , k , j) (ℚ-density q p i)∣)

 ℚ-to-ℝᵁ-is-upper-section-of-ℚ-to-ℝᴸ
  : (q : ℚ)
  → (ℚ-to-ℝᵁ q) is-upper-section-of (ℚ-to-ℝᴸ q)
 ℚ-to-ℝᵁ-is-upper-section-of-ℚ-to-ℝᴸ q
  = (λ p → ℚ-transitivity p q) ,
    (λ p → ℚ-cotransitivity p q)

 ℚ-to-ℝᴸ-is-dedekind : (q : ℚ) → is-dedekind (ℚ-to-ℝᴸ q)
 ℚ-to-ℝᴸ-is-dedekind q = ℚ-to-ℝᵁ q ,
                         ℚ-to-ℝᵁ-is-upper-section-of-ℚ-to-ℝᴸ q

 ℚ-to-ℝ : ℚ → ℝ
 ℚ-to-ℝ q = ℚ-to-ℝᴸ q , ℚ-to-ℝᴸ-is-dedekind q

 ℚ-to-ℝᴸ-is-embedding : is-embedding ℚ-to-ℝᴸ
 ℚ-to-ℝᴸ-is-embedding l (p , a) (q , b) = γ
  where
   I = ℚ-to-ℝᴸ p ＝⟨ a ⟩
       l         ＝⟨ b ⁻¹ ⟩
       ℚ-to-ℝᴸ q ∎

   II : (λ r → (r < p) , _) ＝ (λ r → (r < q) , _)
   II = ap pr₁ I

   III : (λ r → r < p) ＝ (λ r → r < q)
   III = ap (λ f r → pr₁ (f r)) II

   A : (r : ℚ) → r < p → r < q
   A r = idtofun (r < p) (r < q) (happly III r)

   B : (r : ℚ) → r < q → r < p
   B r = idtofun (r < q) (r < p) (happly (III ⁻¹) r)

   V : p ＝ q
   V =  ℚ-≤-antisym p q A B

   γ : (p , a) ＝ (q , b)
   γ = to-subtype-＝ (λ _ → ℝᴸ-is-set) V

 instance
  canonical-map-ℚ-to-ℝ : Canonical-Map ℚ ℝ
  ι {{canonical-map-ℚ-to-ℝ}} = ℚ-to-ℝ

 ℚ-to-ℝ-is-embedding : is-embedding (canonical-map ℚ ℝ)
 ℚ-to-ℝ-is-embedding = factor-is-embedding
                        ℚ-to-ℝ
                        ℝ-to-ℝᴸ
                        ℚ-to-ℝᴸ-is-embedding
                        ℝ-to-ℝᴸ-is-embedding
  where
   notice-that : ℝ-to-ℝᴸ ∘ ℚ-to-ℝ ＝ ℚ-to-ℝᴸ
   notice-that = refl

 is-rational : ℝ → 𝓤⁺ ̇
 is-rational x = Σ q ꞉ ℚ , ι q ＝ x

 being-rational-is-prop : (x : ℝ) → is-prop (is-rational x)
 being-rational-is-prop = ℚ-to-ℝ-is-embedding

\end{code}

We could also define

 instance
  canonical-map-ℚ-to-ℝᴸ : Canonical-Map ℚ ℝᴸ
  ι {{canonical-map-ℚ-to-ℝᴸ}} = ℚ-to-ℝᴸ

  canonical-map-ℚ-to-ℝᵁ : Canonical-Map ℚ ℝᵁ
  ι {{canonical-map-ℚ-to-ℝᵁ}} = ℚ-to-ℝᵁ

but this would give us trouble with unsolved constraints.

We now consider order and apartness on real numbers.

\begin{code}

 lowercut : ℝ → 𝓟 ℚ
 lowercut ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = L

 uppercut : ℝ → 𝓟 ℚ
 uppercut ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = U

 instance
  strict-order-ℚ-ℝ : Strict-Order ℚ ℝ
  _<_ {{strict-order-ℚ-ℝ}} p x = p ∈ lowercut x

  strict-order-ℝ-ℚ : Strict-Order ℝ ℚ
  _<_ {{strict-order-ℝ-ℚ}} x q = q ∈ uppercut x

  strict-order-ℝ-ℝ : Strict-Order ℝ ℝ
  _<_ {{strict-order-ℝ-ℝ}} x y = ∃ q ꞉ ℚ , (x < q) × (q < y)

 <-ℚ-ℝ-is-prop-valued : (p : ℚ) (x : ℝ) → is-prop (p < x)
 <-ℚ-ℝ-is-prop-valued p x = ∈-is-prop (lowercut x) p

 <-ℝ-ℚ-is-prop-valued : (x : ℝ) (q : ℚ) → is-prop (x < q)
 <-ℝ-ℚ-is-prop-valued x q = ∈-is-prop (uppercut x) q

 <-ℝ-ℝ-is-prop-valued : (x y : ℝ) → is-prop (x < y)
 <-ℝ-ℝ-is-prop-valued x y = ∃-is-prop

\end{code}

We now name all the remaining projections out of ℝ. We first give
their types and then define them, for the sake of clarity.

\begin{code}

 lowercut-is-inhabited  : (x : ℝ) → ∃ p ꞉ ℚ , p < x
 uppercut-is-inhabited  : (x : ℝ) → ∃ q ꞉ ℚ , x < q
 lowercut-is-lower      : (x : ℝ) (q : ℚ) → q < x → (p : ℚ) → p < q → p < x
 uppercut-is-upper      : (x : ℝ) (p : ℚ) → x < p → (q : ℚ) → p < q → x < q
 lowercut-is-upper-open : (x : ℝ) (p : ℚ) → p < x → ∃ q ꞉ ℚ , (p < q) × (q < x)
 uppercut-is-lower-open : (x : ℝ) (q : ℚ) → x < q → ∃ p ꞉ ℚ , (p < q) × (x < p)
 cuts-are-ordered       : (x : ℝ) (p q : ℚ) → p < x → x < q → p < q
 cuts-are-located       : (x : ℝ) (p q : ℚ) → p < q → (p < x) ∨ (x < q)
 cuts-are-disjoint      : (x : ℝ) (p : ℚ) → p < x → x ≮ p
 lowercut-is-bounded    : (x : ℝ) → ∃ p ꞉ ℚ , p ≮ x
 lowercut-is-located    : (x : ℝ) (p q : ℚ) → p < q → (p < x) ∨ (q ≮ x)

 lowercut-is-inhabited  ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = Li
 uppercut-is-inhabited  ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = Ui
 lowercut-is-lower      ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = Ll
 uppercut-is-upper      ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = Uu
 lowercut-is-upper-open ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = Lo
 uppercut-is-lower-open ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = Uo
 cuts-are-ordered       ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = o
 cuts-are-located       ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l) = l

 cuts-are-disjoint x p l m = disjoint-criterion
                              (lowercut x) (uppercut x)
                              (cuts-are-ordered x)
                              p
                              (l , m)

 lowercut-is-bounded (l , δ) = pr₁ (dedekind-gives-troelstra l δ)
 lowercut-is-located (l , δ) = pr₂ (dedekind-gives-troelstra l δ)

\end{code}

The lower and upper cut projections are left-cancellable (and hence
embeddings, as the types under consideration are all sets).

\begin{code}

 lowercut-lc : (x y : ℝ) → lowercut x ＝ lowercut y → x ＝ y
 lowercut-lc x y e = to-subtype-＝ being-dedekind-is-prop
                      (to-subtype-＝ being-lower-real-is-prop e)

 uppercut-lc : (x y : ℝ) → uppercut x ＝ uppercut y → x ＝ y
 uppercut-lc x y p = lowercut-lc x y III
  where
   I : lowercut x ⊆ lowercut y
   I = order-lemma-converse (lowercut x) (uppercut x) (lowercut y) (uppercut y)
        (lowercut-is-upper-open x) (cuts-are-located y) (cuts-are-ordered x)
        (transport (_⊆ uppercut x) p (⊆-refl (uppercut x)))

   II : lowercut x ⊇ lowercut y
   II = order-lemma-converse (lowercut y) (uppercut y) (lowercut x) (uppercut x)
         (lowercut-is-upper-open y) (cuts-are-located x) (cuts-are-ordered y)
         (transport (uppercut x ⊆_) p (⊆-refl (uppercut x)))

   III : lowercut x ＝ lowercut y
   III = subset-extensionality'' pe fe fe I II

\end{code}

We now develop the basic properties of the _<_ order.

\begin{code}

 <-irrefl : (x : ℝ) → x ≮ x
 <-irrefl x ℓ = γ
  where
   δ : ¬ (Σ q ꞉ ℚ , ((x < q) × (q < x)))
   δ (q , a , b) = cuts-are-disjoint x q b a

   γ : 𝟘
   γ = ∥∥-rec 𝟘-is-prop δ ℓ

 <-ℝ-ℝ-trans : (x y z : ℝ) → x < y → y < z → x < z
 <-ℝ-ℝ-trans x y z i j = ∥∥-functor₂ f i j
  where
   f : (Σ p ꞉ ℚ , (x < p) × (p < y))
     → (Σ q ꞉ ℚ , (y < q) × (q < z))
     →  Σ r ꞉ ℚ , (x < r) × (r < z)
   f (p , i , j) (q , k , l) = p , i , v
    where
     u : p < q
     u = cuts-are-ordered y p q j k

     v : p < z
     v = lowercut-is-lower z q l p u

 <-cotrans-ℚ : (p q : ℚ) → p < q → (z : ℝ) → (p < z) ∨ (z < q)
 <-cotrans-ℚ p q ℓ z = cuts-are-located z p q ℓ

 <-cotrans : (x y : ℝ) → x < y → (z : ℝ) → (x < z) ∨ (z < y)
 <-cotrans x y ℓ z = V
  where
   I : (Σ q ꞉ ℚ , ((x < q) × (q < y))) → (x < z) ∨ (z < y)
   I (q , a , b) = ∥∥-rec ∨-is-prop III II
    where
     II : ∃ p ꞉ ℚ , (p < q) × (x < p)
     II = uppercut-is-lower-open x q a

     III : (Σ p ꞉ ℚ , (p < q) × (x < p)) → (x < z) ∨ (z < y)
     III (p , c , d) = ∥∥-functor IV (<-cotrans-ℚ p q c z)
       where
        IV : (p < z) + (z < q) → (x < z) + (z < y)
        IV (inl ℓ) = inl ∣ p , d , ℓ ∣
        IV (inr ℓ) = inr ∣ q , ℓ , b ∣

   V : (x < z) ∨ (z < y)
   V = ∥∥-rec ∨-is-prop I ℓ

\end{code}

There are a number of equivalent ways to define the _≤_ order on ℝ. We
give four for now, and three more later.

\begin{code}

 _≤₀_ _≤₁_ _≤₂_ _≤₃_ : ℝ → ℝ → 𝓤 ̇
 x ≤₀ y  = (p : ℚ) → p < x → p < y
 x ≤₁ y  = (q : ℚ) → y < q → x < q
 x ≤₂ y  = y ≮ x
 x ≤₃ y  = (p q : ℚ) → p < x → y < q → p < q

\end{code}

Definition (3) has the advantage that it is applicable when x is a
lower real and y is an upper real. See the interval domain below. But
we adopted the first definition for reals before we realized that. It
doesn't matter much, because we can switch between all the definitions
in the case of the Dedekind reals.

\begin{code}

 ≤₀-is-prop-valued : (x y : ℝ) → is-prop (x ≤₀ y)
 ≤₁-is-prop-valued : (x y : ℝ) → is-prop (x ≤₁ y)
 ≤₂-is-prop-valued : (x y : ℝ) → is-prop (x ≤₂ y)
 ≤₃-is-prop-valued : (x y : ℝ) → is-prop (x ≤₃ y)

 ≤₀-is-prop-valued x y = Π₂-is-prop fe (λ _ _ → <-ℚ-ℝ-is-prop-valued _ y)
 ≤₁-is-prop-valued x y = Π₂-is-prop fe (λ _ _ → <-ℝ-ℚ-is-prop-valued x _)
 ≤₂-is-prop-valued x y = negations-are-props fe
 ≤₃-is-prop-valued x y = Π₄-is-prop fe (λ _ _ _ _ → <-ℚ-ℚ-is-prop-valued _ _)

 instance
  order-ℝ-ℝ : Order ℝ ℝ
  _≤_ {{order-ℝ-ℝ}} = _≤₀_

 ≤-gives-≤₁ : (x y : ℝ) → x ≤ y → x ≤₁ y
 ≤-gives-≤₁ x y ℓ = order-lemma
                     (lowercut x) (uppercut x)
                     (lowercut y) (uppercut y)
                     (uppercut-is-lower-open y)
                     (cuts-are-located x)
                     (cuts-are-ordered y)
                     ℓ

 ≤₁-gives-≤ : (x y : ℝ) → x ≤₁ y → x ≤ y
 ≤₁-gives-≤ x y ℓ = order-lemma-converse
                     (lowercut x) (uppercut x)
                     (lowercut y) (uppercut y)
                     (lowercut-is-upper-open x)
                     (cuts-are-located y)
                     (cuts-are-ordered x)
                     ℓ

 ≤₂-gives-≤ : (x y : ℝ) → x ≤₂ y → x ≤ y
 ≤₂-gives-≤ x y ν q ℓ = VI
  where
   I : (p : ℚ) → p < x → y ≮ p
   I p m l = ν ∣ p , l , m ∣

   II : ∃ p ꞉ ℚ , (q < p) × (p < x)
   II = lowercut-is-upper-open x q ℓ

   III : (Σ p ꞉ ℚ , (q < p) × (p < x)) → q < y
   III (p , i , j) = ∥∥-rec (<-ℚ-ℝ-is-prop-valued q y) V IV
    where
     IV : (q < y) ∨ (y < p)
     IV = <-cotrans-ℚ q p i y

     V : (q < y) + (y < p) → q < y
     V (inl k) = k
     V (inr l) = 𝟘-elim (I p j l)

   VI : q < y
   VI = ∥∥-rec (<-ℚ-ℝ-is-prop-valued q y) III II

 ≤-gives-≤₂ : (x y : ℝ) → x ≤ y → x ≤₂ y
 ≤-gives-≤₂ x y ℓ i = II
  where
   I : ¬ (Σ p ꞉ ℚ , (y < p) × (p < x))
   I (p , j , k) = cuts-are-disjoint y p (ℓ p k) j

   II : 𝟘
   II = ∥∥-rec 𝟘-is-prop I i

 ≤₃-gives-≤ : (x y : ℝ) → x ≤₃ y → x ≤ y
 ≤₃-gives-≤ x y l = III
  where
   I : ¬ (Σ p ꞉ ℚ , (y < p) × (p < x))
   I (p , i , j) = <-ℚ-ℚ-irrefl p (l p p j i)

   II : y ≮ x
   II m = ∥∥-rec 𝟘-is-prop I m

   III : x ≤ y
   III = ≤₂-gives-≤ x y II

 ≤-gives-≤₃ : (x y : ℝ) → x ≤ y → x ≤₃ y
 ≤-gives-≤₃ x y l p q i j = II
  where
   I : p < y
   I = l p i

   II : p < q
   II = cuts-are-ordered y p q I j

 ≤-ℝ-refl : (x : ℝ) → x ≤ x
 ≤-ℝ-refl x q ℓ = ℓ

 ≤-ℝ-ℝ-trans : (x y z : ℝ) → x ≤ y → y ≤ z → x ≤ z
 ≤-ℝ-ℝ-trans x y z l m p i = m p (l p i)

 ≤-ℝ-ℝ-antisym : (x y : ℝ) → x ≤ y → y ≤ x → x ＝ y
 ≤-ℝ-ℝ-antisym x y l m = lowercut-lc x y γ
  where
   γ : lowercut x ＝ lowercut y
   γ = subset-extensionality'' pe fe fe l m

\end{code}

The type ℝ is large, in the sense that it lives in 𝓤⁺ rather than 𝓤,
but it is locally small, in the sense that each identity type x ＝ y
with x,y:ℝ, which also lives in 𝓤⁺, has copy in the universe 𝓤, namely
the type (x ≤ y) × (y ≤ x).

\begin{code}

 ℝ-is-locally-small : is-locally-small ℝ
 ℝ-is-locally-small x y = γ
  where
   f : (x ≤ y) × (y ≤ x) → x ＝ y
   f = uncurry (≤-ℝ-ℝ-antisym x y)

   g : x ＝ y → (x ≤ y) × (y ≤ x)
   g refl = ≤-ℝ-refl x , ≤-ℝ-refl x

   e : ((x ≤ y) × (y ≤ x)) ≃ (x ＝ y)
   e = qinveq
        f
        (g ,
         (λ a → ×-is-prop
                 (≤₀-is-prop-valued x y)
                 (≤₀-is-prop-valued y x)
                 (g (f a)) a) ,
         (λ b → ℝ-is-set (f (g b)) b))

   γ : (x ＝ y) is 𝓤 small
   γ = ((x ≤ y) × (y ≤ x)) , e

\end{code}

Relationship between the orders of ℚ and ℝ:

\begin{code}

 ℚ-to-ℝ-preserves-< : (p q : ℚ) → p < q → ι p < ι q
 ℚ-to-ℝ-preserves-< p q l = ∣ ℚ-density p q l ∣

 ℚ-to-ℝ-reflects-< : (p q : ℚ) → ι p < ι q → p < q
 ℚ-to-ℝ-reflects-< p q = ∥∥-rec
                          (<-ℚ-ℚ-is-prop-valued p q)
                          (λ (r , i , j) → ℚ-transitivity p r q i j)

 ≤-on-ℚ-agrees-with-≤-on-ℝ : (p q : ℚ) → (p ≤ q) ＝ (ι p ≤ ι q)
 ≤-on-ℚ-agrees-with-≤-on-ℝ p q = refl

 ≤-on-ℚ-is-prop-valued : (p q : ℚ) → is-prop (ι p ≤ ι q)
 ≤-on-ℚ-is-prop-valued p q = ≤₀-is-prop-valued (ι p) (ι q)

 ℚ-to-ℝ-preserves-≤ : (p q : ℚ) → p ≤ q → ι p ≤ ι q
 ℚ-to-ℝ-preserves-≤ p q = id

 ℚ-to-ℝ-reflects-≤ : (p q : ℚ) → ι p ≤ ι q → p ≤ q
 ℚ-to-ℝ-reflects-≤ p q = id

 ℚ-to-ℝ-left : (p : ℚ) (x : ℝ) → p < x → ι p < x
 ℚ-to-ℝ-left p x = lowercut-is-upper-open x p

 ℚ-to-ℝ-left-converse : (p : ℚ) (x : ℝ) → ι p < x → p < x
 ℚ-to-ℝ-left-converse p x = ∥∥-rec
                             (<-ℚ-ℝ-is-prop-valued p x)
                             (λ (q , m , o) → lowercut-is-lower x q o p m)

 ℚ-to-ℝ-right : (x : ℝ) (q : ℚ) → x < q → x < ι q
 ℚ-to-ℝ-right x q l = ∥∥-functor
                       (λ (p , m , o) → p , o , m)
                       (uppercut-is-lower-open x q l)

 ℚ-to-ℝ-right-converse : (x : ℝ) (q : ℚ) → x < ι q → x < q
 ℚ-to-ℝ-right-converse x q = ∥∥-rec
                              (<-ℝ-ℚ-is-prop-valued x q)
                              (λ (p , m , o) → uppercut-is-upper x p m q o)
\end{code}

The promised three more ways to define _≤_ on ℝ:

\begin{code}

 _≤₀ₐ_ _≤₁ₐ_ _≤₃ₐ_ : ℝ → ℝ → 𝓤⁺ ̇
 x ≤₀ₐ y = (z : ℝ) → z < x → z < y
 x ≤₁ₐ y = (z : ℝ) → y < z → x < z
 x ≤₃ₐ y = (z t : ℝ) → z < x → y < t → z < t

 ≤₀ₐ-is-prop-valued : (x y : ℝ) → is-prop (x ≤₀ₐ y)
 ≤₁ₐ-is-prop-valued : (x y : ℝ) → is-prop (x ≤₁ₐ y)
 ≤₃ₐ-is-prop-valued : (x y : ℝ) → is-prop (x ≤₃ₐ y)

 ≤₀ₐ-is-prop-valued x y = Π₂-is-prop fe (λ z _ → <-ℝ-ℝ-is-prop-valued z y)
 ≤₁ₐ-is-prop-valued x y = Π₂-is-prop fe (λ z _ → <-ℝ-ℝ-is-prop-valued x z)
 ≤₃ₐ-is-prop-valued x y = Π₄-is-prop fe (λ z t _ _ → <-ℝ-ℝ-is-prop-valued z t)

 ≤₀-gives-≤₀ₐ : (x y : ℝ) → x ≤₀ y → x ≤₀ₐ y
 ≤₀-gives-≤₀ₐ x y l z = ∥∥-functor f
  where
   f : (Σ p ꞉ ℚ , (z < p) × (p < x))
     → (Σ p ꞉ ℚ , (z < p) × (p < y))
   f (p , u , v) = p , u , l p v

 ≤₀ₐ-gives-≤₀ : (x y : ℝ) → x ≤₀ₐ y → x ≤₀ y
 ≤₀ₐ-gives-≤₀ x y l p m = II
  where
   I : ι p < y
   I = l (ι p) (ℚ-to-ℝ-left p x m)

   II : p < y
   II = ℚ-to-ℝ-left-converse p y I

 ≤₁-gives-≤₁ₐ : (x y : ℝ) → x ≤₁ y → x ≤₁ₐ y
 ≤₁-gives-≤₁ₐ x y l z = ∥∥-functor f
  where
   f : (Σ p ꞉ ℚ , (y < p) × (p < z))
     → (Σ p ꞉ ℚ , (x < p) × (p < z))
   f (p , u , v) = p , l p u , v

 ≤₁ₐ-gives-≤₁ : (x y : ℝ) → x ≤₁ₐ y → x ≤₁ y
 ≤₁ₐ-gives-≤₁ x y l p m = II
  where
   I : x < ι p
   I = l (ι p) (ℚ-to-ℝ-right y p m)

   II : x < p
   II = ℚ-to-ℝ-right-converse x p I

 ≤₃ₐ-gives-≤₃ : (x y : ℝ) → x ≤₃ₐ y → x ≤₃ y
 ≤₃ₐ-gives-≤₃ x y l p q m o = ℚ-to-ℝ-reflects-< p q γ
  where
   γ : ι p < ι q
   γ = l (ι p) (ι q) (ℚ-to-ℝ-left p x m) (ℚ-to-ℝ-right y q o)

 ≤₃-gives-≤₃ₐ : (x y : ℝ) → x ≤₃ y → x ≤₃ₐ y
 ≤₃-gives-≤₃ₐ x y l z t m o = ∥∥-functor₂ f m o
  where
   f : (Σ p ꞉ ℚ , (z < p) × (p < x))
     → (Σ q ꞉ ℚ , (y < q) × (q < t))
     → (Σ p ꞉ ℚ , (z < p) × (p < t))
   f (p , i , j) (q , u , v) = p , i , II
    where
     I : p < q
     I = l p q j u

     II : p < t
     II = lowercut-is-lower t q v p I

\end{code}

Relationship between _<_ and _≤_ on ℝ:

\begin{code}

 <-gives-≤' : (x y : ℝ) → x < y → x ≤ y
 <-gives-≤' x y l = ≤₀ₐ-gives-≤₀ x y f
  where
   f : (z : ℝ) → z < x → z < y
   f z m = <-ℝ-ℝ-trans z x y m l

 <-≤-trans : (x y z : ℝ) → x < y → y ≤ z → x < z
 <-≤-trans x y z l m = ≤₀-gives-≤₀ₐ y z m x l

 ≤-<-ℝ-ℝ-trans : (x y z : ℝ) → x ≤ y → y < z → x < z
 ≤-<-ℝ-ℝ-trans x y z l m = ≤₁-gives-≤₁ₐ x y (≤-gives-≤₁ x y l) z m

\end{code}

Apartness of real numbers and its basic properties:

\begin{code}

 _♯_ : ℝ → ℝ → 𝓤 ̇
 x ♯ y = (x < y) + (y < x)

 ♯-is-prop-valued : (x y : ℝ) → is-prop (x ♯ y)
 ♯-is-prop-valued x y = sum-of-contradictory-props
                         (<-ℝ-ℝ-is-prop-valued x y)
                         (<-ℝ-ℝ-is-prop-valued y x)
                         (λ i j → <-irrefl x (<-ℝ-ℝ-trans x y x i j))

 ♯-irrefl : (x : ℝ) → ¬ (x ♯ x)
 ♯-irrefl x (inl ℓ) = <-irrefl x ℓ
 ♯-irrefl x (inr ℓ) = <-irrefl x ℓ

 ♯-gives-≠ : (x y : ℝ) → x ♯ y → x ≠ y
 ♯-gives-≠ x x s refl = ♯-irrefl x s

 ♯-sym : (x y : ℝ) → x ♯ y → y ♯ x
 ♯-sym x y (inl ℓ) = inr ℓ
 ♯-sym x y (inr ℓ) = inl ℓ

 ♯-cotrans : (x y : ℝ) → x ♯ y → (z : ℝ) → (x ♯ z) ∨ (y ♯ z)
 ♯-cotrans x y (inl ℓ) z = ∥∥-functor
                            (cases (λ (ℓ : x < z) → inl (inl ℓ))
                                   (λ (ℓ : z < y) → inr (inr ℓ)))
                            (<-cotrans x y ℓ z)
 ♯-cotrans x y (inr ℓ) z = ∥∥-functor
                            (cases (λ (ℓ : y < z) → inr (inl ℓ))
                                   (λ (ℓ : z < x) → inl (inr ℓ)))
                            (<-cotrans y x ℓ z)

 ♯-is-tight : (x y : ℝ) → ¬ (x ♯ y) → x ＝ y
 ♯-is-tight x y ν = ≤-ℝ-ℝ-antisym x y III IV
  where
   I : x ≮ y
   I ℓ = ν (inl ℓ)

   II : y ≮ x
   II ℓ = ν (inr ℓ)

   III : x ≤ y
   III = ≤₂-gives-≤ x y II

   IV : y ≤ x
   IV = ≤₂-gives-≤ y x I

 ℝ-is-¬¬-separated : (x y : ℝ) → ¬¬ (x ＝ y) → x ＝ y
 ℝ-is-¬¬-separated x y ϕ = ♯-is-tight x y (c ϕ)
  where
   c : ¬¬ (x ＝ y) → ¬ (x ♯ y)
   c = contrapositive (♯-gives-≠ x y)

 strict-ℝ-order-criterion : (x y : ℝ) → x ≤ y → x ♯ y → x < y
 strict-ℝ-order-criterion x y ℓ (inl m) = m
 strict-ℝ-order-criterion x y ℓ (inr m) = 𝟘-elim (≤-gives-≤₂ x y ℓ m)

 is-irrational : ℝ → 𝓤⁺ ̇
 is-irrational x = ¬ (Σ q ꞉ ℚ , ι q ＝ x)

 is-strongly-irrational : ℝ → 𝓤 ̇
 is-strongly-irrational x = (q : ℚ) → ι q ♯ x

 being-irrational-is-prop : (x : ℝ) → is-prop (is-irrational x)
 being-irrational-is-prop x = negations-are-props fe

 being-strongly-irrational-is-prop
  : (x : ℝ)
  → is-prop (is-strongly-irrational x)
 being-strongly-irrational-is-prop x
  = Π-is-prop fe (λ q → ♯-is-prop-valued (ι q) x)

\end{code}

We now consider the existence of least upper bounds of bounded
families x : 𝐼 → ℝ with 𝐼 inhabited.

A sufficient condition, given by Bishop (using his version of Cauchy
reals, rather than our version of Dedekind reals, which is what we are
working with here), is that

  (p q : ℚ) → p < q → (∃ i ꞉ 𝐼 , p < x i)
                    ∨ (Π i ꞉ 𝐼 , x i < q).

We observe that the weaker condition

  (p q : ℚ) → p < q →  (∃ i ꞉ 𝐼 , p < x i)
                    ∨ ¬(∃ i ꞉ 𝐼 , q < x i)

suffices (see below for the formal fact that it is indeed weaker).

If we define (p < x) = (∃ i ꞉ 𝐼 , p < x i), then this weaker sufficient
condition reads

  (p q : ℚ) → p < q → (p < x) ∨ (q ≮ x)

so that we see that it is analogous to Troelstra's locatedness
condition discussed above.

In the following, we write x ≤ y to mean that the real number y is an
upper bound of the family x.

\begin{code}

 module _ {𝐼 : 𝓤 ̇ } where

  private
   F = 𝐼 → ℝ

  instance
   order-F-ℝ : Order F ℝ
   _≤_ {{order-F-ℝ}} x y = (i : 𝐼) → x i ≤ y

  ≤-F-ℝ-is-prop-valued : (x : F) (y : ℝ)
                       → is-prop (x ≤ y)
  ≤-F-ℝ-is-prop-valued x y = Π-is-prop fe (λ i → ≤₀-is-prop-valued (x i) y)

  _has-lub_ : F → ℝ → 𝓤⁺ ̇
  x has-lub y = (x ≤ y) × ((z : ℝ) → x ≤ z → y ≤ z)

  _has-a-lub : F → 𝓤⁺ ̇
  x has-a-lub = Σ y ꞉ ℝ , (x has-lub y)

  having-lub-is-prop : (x : F) (y : ℝ)
                     → is-prop (x has-lub y)
  having-lub-is-prop x y = ×-is-prop
                            (≤-F-ℝ-is-prop-valued x y)
                            (Π₂-is-prop fe (λ z _ → ≤₀-is-prop-valued y z))

  having-a-lub-is-prop : (x : F) → is-prop (x has-a-lub)
  having-a-lub-is-prop x (y , a , b) (y' , a' , b') = γ
   where
    I : y ＝ y'
    I = ≤-ℝ-ℝ-antisym y y' (b y' a') (b' y a)

    γ : (y , a , b) ＝ (y' , a' , b')
    γ = to-subtype-＝ (having-lub-is-prop x) I

  instance
   strict-order-ℚ-F : Strict-Order ℚ F
   _<_ {{strict-order-ℚ-F}} p x = ∃ i ꞉ 𝐼 , p < x i

  strict-order-ℚ-F-is-prop : (p : ℚ) (x : F) → is-prop (p < x)
  strict-order-ℚ-F-is-prop p x = ∃-is-prop

  strict-order-ℚ-F-observation : (p : ℚ) (x : F)
                               → (p ≮ x) ↔ (x ≤ ι p)
  strict-order-ℚ-F-observation p x = f , g
   where
    f : p ≮ x → x ≤ ι p
    f ν i = I
     where
      I : (q : ℚ) → q < x i → q < p
      I q l = ℚ-order-criterion q p II III
       where
        II : p ≮ q
        II m = ν ∣ i , lowercut-is-lower (x i) q l p m ∣

        III : q ≠ p
        III refl = ν ∣ i , l ∣

    g : x ≤ ι p → p ≮ x
    g l = ∥∥-rec 𝟘-is-prop I
     where
      I : ¬ (Σ i ꞉ 𝐼 , p < x i)
      I (i , m) = <-ℚ-ℚ-irrefl p (l i p m)

  is-upper-bounded : F → 𝓤⁺ ̇
  is-upper-bounded x = ∃ y ꞉ ℝ , (x ≤ y)

  is-located-family : F → 𝓤 ̇
  is-located-family x = (p q : ℚ) → p < q → (p < x) ∨ (q ≮ x)

  lub-sufficient-conditions : F → 𝓤⁺ ̇
  lub-sufficient-conditions x = ∥ 𝐼 ∥
                              × is-upper-bounded x
                              × is-located-family x

  lub : (x : F) → lub-sufficient-conditions x → x has-a-lub
  lub x (𝐼-inhabited , x-bounded , x-located) = y , a , b
   where
    L : 𝓟 ℚ
    L p = (p < x) , strict-order-ℚ-F-is-prop p x

    L-inhabited : ∃ p ꞉ ℚ , p < x
    L-inhabited = ∥∥-rec ∃-is-prop I 𝐼-inhabited
     where
      I : 𝐼 → ∃ p ꞉ ℚ , ∃ i ꞉ 𝐼 , p < x i
      I i = III II
       where
        II : Σ i ꞉ 𝐼 , ∃ p ꞉ ℚ , p < x i
        II = i , lowercut-is-inhabited (x i)

        III : type-of II → ∃ p ꞉ ℚ , ∃ i ꞉ 𝐼 , p < x i
        III (i , s) = ∥∥-functor IV s
         where
          IV : (Σ p ꞉ ℚ , p < x i) → Σ p ꞉ ℚ , ∃ i ꞉ 𝐼 , p < x i
          IV (p , l) = p , ∣ i , l ∣

    L-lower : (q : ℚ) → q < x → (p : ℚ) → p < q → p < x
    L-lower q l p m = ∥∥-functor
                       (λ (i , k) → i , lowercut-is-lower (x i) q k p m)
                       l

    L-upper-open : (p : ℚ) → p < x → ∃ p' ꞉ ℚ , ((p < p') × (p' < x))
    L-upper-open p = ∥∥-rec ∃-is-prop f
     where
      f : (Σ i ꞉ 𝐼 , p < x i) → ∃ p' ꞉ ℚ , ((p < p') × (p' < x))
      f (i , l) = ∥∥-functor g (lowercut-is-upper-open (x i) p l)
       where
        g : (Σ p' ꞉ ℚ , (p < p') × (p' < x i))
          → (Σ p' ꞉ ℚ , (p < p') × (p' < x))
        g (p' , m , o) = p' , m , ∣ i , o ∣

    yᴸ : ℝᴸ
    yᴸ = (L , L-inhabited , L-lower , L-upper-open)

    L-bounded-above : ∃ q ꞉ ℚ , q ≮ x
    L-bounded-above = ∥∥-rec ∃-is-prop I x-bounded
     where
      I : (Σ β ꞉ ℝ , x ≤ β) → ∃ q ꞉ ℚ , q ≮ x
      I (β , l) = ∥∥-functor II (uppercut-is-inhabited β)
       where
        II : (Σ q ꞉ ℚ , β < q) → Σ q ꞉ ℚ , q ≮ x
        II (q , m) = q , ∥∥-rec 𝟘-is-prop III
         where
          III : ¬ (Σ i ꞉ 𝐼 , q < x i)
          III (i , o) = <-ℚ-ℚ-irrefl q (cuts-are-ordered β q q (l i q o) m)

    L-located : (p q : ℚ) → p < q → (p < x) ∨ (q ≮ x)
    L-located = x-located

    τ : is-troelstra yᴸ
    τ = L-bounded-above , L-located

    y : ℝ
    y = (yᴸ , troelstra-gives-dedekind yᴸ τ)

    a : x ≤ y
    a i p l = ∣ i , l ∣

    b : (z : ℝ) → x ≤ z → y ≤ z
    b z l p = ∥∥-rec (<-ℚ-ℝ-is-prop-valued p z) f
     where
      f : (Σ i ꞉ 𝐼 , p < x i) → p < z
      f (i , m) = l i p m

  instance
   strict-order-F-ℚ : Strict-Order F ℚ
   _<_ {{strict-order-F-ℚ}} x q = (i : 𝐼) → x i < q

  <-F-ℚ-is-prop-valued : (q : ℚ) (x : F) → is-prop (x < q)
  <-F-ℚ-is-prop-valued q x = Π-is-prop fe (λ i → <-ℝ-ℚ-is-prop-valued (x i) q)

  is-bishop-located : F → 𝓤 ̇
  is-bishop-located x = (p q : ℚ) → p < q → (p < x) ∨ (x < q)

  bishop-located-families-are-located
   : (x : F)
   → is-bishop-located x
   → is-located-family x
  bishop-located-families-are-located x located p q l = IV
   where
    I : x < q → q ≮ x
    I m = ∥∥-rec 𝟘-is-prop II
     where
      II : ¬ (Σ i ꞉ 𝐼 , q < x i)
      II (i , o) = <-ℚ-ℚ-irrefl q (cuts-are-ordered (x i) q q o (m i))

    III : (p < x) + (x < q) → (p < x) + (q ≮ x)
    III (inl l) = inl l
    III (inr m) = inr (I m)

    IV : (p < x) ∨ (q ≮ x)
    IV = ∥∥-functor III (located p q l)

\end{code}

The partial reals, or interval domain, arise from dropping the
locatedness condition from the Dedekind reals.

\begin{code}

 instance
  strict-order-ℚ-ℝᴸ : Strict-Order ℚ ℝᴸ
  _<_ {{strict-order-ℚ-ℝᴸ}} p (L , _) = p ∈ L

  strict-order-ℝᵁ-ℚ : Strict-Order ℝᵁ ℚ
  _<_ {{strict-order-ℝᵁ-ℚ}} (U , _) p = p ∈ U

 instance
  order-ℝᴸ-ℝᵁ : Order ℝᴸ ℝᵁ
  _≤_ {{order-ℝᴸ-ℝᵁ}} x y = (p q : ℚ) → p < x → y < q → p < q

 𝓡 : 𝓤⁺ ̇
 𝓡 = Σ (x , y) ꞉ ℝᴸ × ℝᵁ , (x ≤ y)

 𝓡-is-set : is-set 𝓡
 𝓡-is-set = subsets-of-sets-are-sets (ℝᴸ × ℝᵁ) (λ (x , y) → x ≤ y)
             (×-is-set ℝᴸ-is-set ℝᵁ-is-set)
             (Π₄-is-prop fe (λ _ _ _ _ → <-ℚ-ℚ-is-prop-valued _ _))

 NB₄ : 𝓡 ≃ (Σ (L , U) ꞉ 𝓟 ℚ × 𝓟 ℚ
                       , (is-inhabited L × is-lower L × is-upper-open L)
                       × (is-inhabited U × is-upper U × is-lower-open U)
                       × are-ordered L U)

 NB₄ = qinveq
        (λ (((L , Li , Ll , Lo) , (U , Ui , Uu , Uo)) , o)
          → (L , U) , (Li , Ll , Lo) , ((Ui , Uu , Uo) , o))
        ((λ ((L , U) , (Li , Ll , Lo) , ((Ui , Uu , Uo) , o))
          → (((L , Li , Ll , Lo) , (U , Ui , Uu , Uo)) , o)) ,
         (λ _ → refl) ,
         (λ _ → refl))

 ℝ-to-𝓡 : ℝ → 𝓡
 ℝ-to-𝓡 (x , y , o , _) = (x , y) , o

 instance
  canonical-map-ℝ-to-𝓡 : Canonical-Map ℝ 𝓡
  ι {{canonical-map-ℝ-to-𝓡}} = ℝ-to-𝓡

  order-ℝᴸ-ℝᴸ : Order ℝᴸ ℝᴸ
  _≤_ {{order-ℝᴸ-ℝᴸ}} x y = (p : ℚ) → p < x → p < y

  order-ℝᵁ-ℝᵁ : Order ℝᵁ ℝᵁ
  _≤_ {{order-ℝᵁ-ℝᵁ}} x y = (p : ℚ) → y < p → x < p

  square-order-𝓡-𝓡 : Square-Order 𝓡 𝓡
  _⊑_ {{square-order-𝓡-𝓡}} ((x , y) , _) ((x' , y') , _) =
   (x ≤ x') × (y' ≤ y)

 ℝ-to-𝓡-is-embedding : is-embedding (canonical-map ℝ 𝓡)
 ℝ-to-𝓡-is-embedding ((x , y) , o)
                     ((x , y , o , l) , refl)
                     ((x , y , o , m) , refl) = γ
  where
   δ : l ＝ m
   δ = being-located-is-prop (ι x) (ι y) l m

   γ : ((x , y , o , l) , refl) ＝ ((x , y , o , m) , refl)
   γ = ap (λ - → (x , y , o , -) , refl) δ

\end{code}

Notice that this is reverse inclusion of intervals: wider intervals
are lower in the square order.

If we drop the inhabitation conditions, the endpoints can be ±∞:

\begin{code}

 𝓡∞ = (Σ (L , U) ꞉ 𝓟 ℚ × 𝓟 ℚ
             , (is-lower L × is-upper-open L)
             × (is-upper U × is-lower-open U)
             × are-ordered L U)

\end{code}

Added 9 January 2026 by Tom de Jong.  Note that an alternative
formulation of the axioms is given by the following.

\begin{code}

 roundness : (x : 𝓟 ℚ × 𝓟 ℚ) → 𝓤 ̇
 roundness (L , U) =
    ((p : ℚ) → p ∈ L ↔ (∃ r ꞉ ℚ , (p < r) × (r ∈ L)))
  × ((q : ℚ) → q ∈ U ↔ (∃ s ꞉ ℚ , (s < q) × (s ∈ U)))

 roundness-equivalence
  : ((L , U) : 𝓟 ℚ × 𝓟 ℚ)
  → is-lower L × is-upper-open L × is-upper U × is-lower-open U
  ↔ roundness (L , U)
 roundness-equivalence (L , U) = I , II
  where
   I : is-lower L × is-upper-open L × is-upper U × is-lower-open U
     → roundness (L , U)
   I (L-low , L-uo , U-up , U-lo) =
    (λ p → L-uo p ,
           ∥∥-rec (∈-is-prop L p) (λ (r , l , r-in-L) → L-low r r-in-L p l)) ,
    (λ q → U-lo q ,
           ∥∥-rec (∈-is-prop U q) (λ (s , l , s-in-U) → U-up s s-in-U q l))
   II : roundness (L , U)
      → is-lower L × is-upper-open L × is-upper U × is-lower-open U
   II (ρ₁ , ρ₂) =
    (λ q q-in-L p l → rl-implication (ρ₁ p) ∣ q , l , q-in-L ∣) ,
    (λ p → lr-implication (ρ₁ p)) ,
    (λ p p-in-U q l → rl-implication (ρ₂ q) ∣ p , l , p-in-U ∣) ,
    (λ q → lr-implication (ρ₂ q))

\end{code}

End of addition.

\begin{code}

 𝓡-to-𝓡∞ : 𝓡 → 𝓡∞
 𝓡-to-𝓡∞ (((L , _ , Ll , Lo) , (U , _ , Uu , Uo)) , o)
  = (L , U) , (Ll , Lo) , (Uu , Uo) , o

 ⊥𝓡∞ : 𝓡∞
 ⊥𝓡∞ = (∅ , ∅) , ((λ _ ()) , (λ _ ())) , ((λ _ ()) , (λ _ ())) , (λ p q ())

 instance
  canonical-map-𝓡-to-𝓡∞ : Canonical-Map 𝓡 𝓡∞
  ι {{canonical-map-𝓡-to-𝓡∞}} = 𝓡-to-𝓡∞

 𝓡-to-𝓡∞-is-embedding : is-embedding (canonical-map 𝓡 𝓡∞)
 𝓡-to-𝓡∞-is-embedding ((L , U) , (Ll , Lo) , (Uu , Uo) , o)
                        ((((L , i , Ll , Lo) , U , k , Uu , Uo) , o) , refl)
                        ((((L , j , Ll , Lo) , U , l , Uu , Uo) , o) , refl)
   = (((L , i , Ll , Lo) , U , k , Uu , Uo) , o) , refl ＝⟨ I ⟩
     (((L , j , Ll , Lo) , U , l , Uu , Uo) , o) , refl ∎
  where
   I = ap₂ (λ i k → (((L , i , Ll , Lo) , U , k , Uu , Uo) , o) , refl)
           (being-inhabited-is-prop L i j)
           (being-inhabited-is-prop U k l)

 𝓡∞-is-set : is-set 𝓡∞
 𝓡∞-is-set = subsets-of-sets-are-sets (𝓟 ℚ × 𝓟 ℚ) _
              (×-is-set (𝓟-is-set' fe pe) (𝓟-is-set' fe pe))
              (λ {(L , U)} → ×₃-is-prop
                              (×-is-prop (being-lower-is-prop L)
                                         (being-upper-open-is-prop L))
                              (×-is-prop (being-upper-is-prop U)
                                         (being-lower-open-is-prop U))
                             (being-ordered-is-prop L U))

\end{code}

TODO. Show that 𝓡∞ is isomorphic, as a dcpo, to the ideal completion
of the dyadic intervals.

The notion of a locator for a real number was studied by my former PhD
student Auke Booij in his PhD thesis.

 Auke Booij. Extensional constructive real analysis via locators
 Mathematical Structures in Computer Science, Volume 31, Issue 1,
 January 2021, pp. 64 - 88 https://doi.org/10.1017/S0960129520000171
 https://arxiv.org/abs/1805.06781

\begin{code}

 locator : ℝ → 𝓤 ̇
 locator x = (p q : ℚ) → p < q → (p < x) + (x < q)

\end{code}

We also consider the following notion of locator for families:

\begin{code}

 bishop-locator : {𝐼 : 𝓤 ̇ } → (𝐼 → ℝ) → 𝓤 ̇
 bishop-locator {𝐼} x = (p q : ℚ)
                      → p < q
                      → (Σ i ꞉ 𝐼 , p < x i)
                      + (Π i ꞉ 𝐼 , x i < q)

 pointwise-locator-gives-bishop-locator
  : (𝐼 : 𝓤 ̇ ) (x : 𝐼 → ℝ)
  → is-compact∙ 𝐼
  → ((i : 𝐼) → locator (x i))
  → bishop-locator x
 pointwise-locator-gives-bishop-locator 𝐼 x κ ℓ p q l = γ
  where
   γ : (Σ i ꞉ 𝐼 , p < x i) + (Π i ꞉ 𝐼 , x i < q)
   γ = compact-gives-Σ+Π 𝐼
        (λ i → p < x i) (λ i → x i < q)
        (compact∙-types-are-compact κ)
        (λ i → ℓ i p q l)

 lub-with-locators : (𝐼 : 𝓤 ̇ ) (x : 𝐼 → ℝ)
                   → is-compact∙ 𝐼
                   → is-upper-bounded x
                   → ((i : 𝐼) → locator (x i))
                   → Σ y ꞉ ℝ , (x has-lub y) × locator y
 lub-with-locators 𝐼 x κ β ℓ = γ
  where
   h : ∥ 𝐼 ∥
   h = ∣ compact∙-types-are-pointed κ ∣

   I : bishop-locator x
   I = pointwise-locator-gives-bishop-locator 𝐼 x κ ℓ

   II : (p q : ℚ)
      → p < q
      → ((Σ i ꞉ 𝐼 , p < x i) + (Π i ꞉ 𝐼 , x i < q))
      → (p < x) ∨ (x < q)
   II p q l (inl (i , m)) = ∣ inl ∣ i , m ∣ ∣
   II p q l (inr ϕ)       = ∣ inr ϕ ∣

   III : is-bishop-located x
   III p q l = II p q l (I p q l)

   IV : x has-a-lub
   IV = lub x (h , β , bishop-located-families-are-located x III)

   y : ℝ
   y = pr₁ IV

   V : x has-lub y
   V = pr₂ IV

   VI : (p q : ℚ) → p < q → (p < y) + (y < q)
   VI p q l = δ (ℚ-density p q l)
    where
     δ : (Σ q' ꞉ ℚ , (p < q') × (q' < q)) → (p < y) + (y < q)
     δ (q' , i , j) = VII (I p q' i)
      where
       VII : ((Σ i ꞉ 𝐼 , p < x i) + (Π i ꞉ 𝐼 , x i < q')) → (p < y) + (y < q)
       VII (inl (o , m)) = inl ∣ o , m ∣
       VII (inr ϕ)       = inr IX
        where
         VIII : q' ≮ y
         VIII = ∥∥-rec 𝟘-is-prop
                 (λ (i , o) → <-ℚ-ℚ-irrefl q'
                               (cuts-are-ordered (x i) q' q' o (ϕ i)))

         IX : ∃ q' ꞉ ℚ , (q' < q) × q' ≮ y
         IX = ∣ q' , j , VIII ∣

   γ : Σ y ꞉ ℝ , (x has-lub y) × locator y
   γ = (y , V , VI)

\end{code}

Limits of sequences, but using the topological, rather than metric, structure of the reals.

\begin{code}

 ⦅_,_⦆ : ℚ → ℚ → (ℝ → Ω 𝓤)
 ⦅ p , q ⦆ = λ x → ((p < x) × (x < q)) ,
                    ×-is-prop
                     (<-ℚ-ℝ-is-prop-valued p x)
                     (<-ℝ-ℚ-is-prop-valued x q)

 _has-limit_ : (ℕ → ℝ) → ℝ → 𝓤 ̇
 x has-limit x∞ = (p q : ℚ)
                 → x∞ ∈ ⦅ p , q ⦆
                 → ∃ n ꞉ ℕ , ((k : ℕ) → k ≥ n → x k ∈ ⦅ p , q ⦆)

 open import CoNaturals.Type

 is-continuous-ℕ∞-ℝ : (ℕ∞ → ℝ) → 𝓤 ̇
 is-continuous-ℕ∞-ℝ x = (𝓃 : ℕ∞) (p q : ℚ)
                      → x 𝓃 ∈ ⦅ p , q ⦆
                      → ∃ 𝓀 ꞉ ℕ∞
                            , (𝓀 ≺ 𝓃)
                            × ((𝒾 : ℕ∞) → 𝒾 ≽ 𝓀 → x 𝒾 ∈ ⦅ p , q ⦆)

\end{code}

TODO. Some (overlapping) problems:

\begin{code}

 Problem₁ = (x : ℕ → ℝ) (x∞ : ℝ)
          → x has-limit x∞
          → Σ x̂ ꞉ (ℕ∞ → ℝ)
                 , ((n : ℕ) → x̂ (ι n) ＝ x n)
                 × (x̂ ∞ ＝ x∞)

 Problem₂ = (x : ℕ → ℝ) (x∞ : ℝ)
          → ((n : ℕ) → locator (x n))
          → locator x∞
          → x has-limit x∞
          → Σ x̂ ꞉ (ℕ∞ → ℝ)
                 , ((n : ℕ) → x̂ (ι n) ＝ x n)
                 × (x̂ ∞ ＝ x∞)
                 × ((𝓃 : ℕ∞) → locator (x̂ 𝓃))

 Problem₃ = (x : ℕ∞ → ℝ)
          → (x ∘ ι) has-limit (x ∞)
          → ((n : ℕ) → locator (x (ι n)))
          → locator (x ∞)

 Problem₄ = Σ A ꞉ (ℝ → Ω 𝓤) , (Σ x ꞉ ℝ , x ∈ A) ≃ ℕ∞

 Problem₅ = Σ A ꞉ (ℝ → Ω 𝓤)
                , ((Σ x ꞉ ℝ , x ∈ A) ≃ ℕ∞)
                × ((x : ℝ) → x ∈ A → locator x)

 Problem₆ = (A : ℝ → Ω 𝓤)
          → ((Σ x ꞉ ℝ , x ∈ A) ≃ ℕ∞)
          → (x : ℝ)
          → x ∈ A
          → locator x

\end{code}

Should some of the above ∃ be Σ and/or vice-versa?

Added 22 August 2023. The lower reals have arbitrary sups if we remove
the inhabitation condition, so that we get a point -∞, in addition to
a point ∞ which is already present (this is well known).

TODO. Maybe remove the the inhabitation condition from the lower
reals. It doesn't really belong there.
