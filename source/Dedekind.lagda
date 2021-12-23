Martin Escardo, 20th December 2021

Some thoughts about Dedekind reals.

A Dedekind real in constructive type theory is defined as a triple
(L , U , p) where L and U are data, namely given sets of rational
numbers, and p is property of (L , U).

But actually, given a lower Dedekind section L, there is at most one
pair (U , p) such that (L , U , p) is a Dedekind real. Hence the
Dedekind data (U , p) is actually property of the lower real L. A more
precise statement of this phenomenon is given below.

We generalize the rationals to any type with a proposition-valued,
irreflexive relation _<_, simply to avoid having to define the
rational numbers. But also it is interesting than nothing other than
a proposition-valued irreflexive relation is needed for the above
discussion.

We also discuss a version of the Dedekind reals proposed by Troelstra.
To show that it agrees with the usual one, we further assume that _<_
is dense, upper open, and satisfies p ≢ q → ¬(q < p) → p < q (which
the type of rationals does).

We also discuss what happens when we assume the principle of
excluded middle.

Here we adopt HoTT/UF as our type-theoretic foundation, which, in
particular, is well-suited to discuss the distinction between data and
property.

See also the discussion at https://twitter.com/EscardoMartin/status/1473393261012295681

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc
open import UF-FunExt
open import UF-Subsingletons

module Dedekind
        (pt  : propositional-truncations-exist)
        (fe' : FunExt)
        (pe' : PropExt)
        {𝓣  : Universe}
        (ℚ   : 𝓣 ̇ )
        (_<_ : ℚ → ℚ → 𝓣 ̇ )
        (order-is-prop-valued : (p q : ℚ) → is-prop (p < q))
        (order-is-irrefl      : (q : ℚ) → ¬(q < q))
       where

fe : Fun-Ext
fe {𝓤} {𝓥} = fe' 𝓤 𝓥

pe : Prop-Ext
pe {𝓤} = pe' 𝓤

open PropositionalTruncation pt

record further-properties-of-ℚ-and-its-order : 𝓣 ̇ where
 constructor
  further
 field
  ℚ-is-inhabited  : ∥ ℚ ∥
  ℚ-is-dense      : (p r : ℚ) → p < r → ∃ q ꞉ ℚ , (p < q) × (q < r)
  transitivity    : (p q r : ℚ) → p < q → q < r → p < r
  order-criterion : (p q : ℚ) → p ≢ q → ¬(q < p) → p < q
  cotransitivity  : (p q r : ℚ) → p < r → (p < q) ∨ (q < r)
  ℚ-is-lower-open : (q : ℚ) → ∃ p ꞉ ℚ , (p < q)
  ℚ-is-upper-open : (p : ℚ) → ∃ q ꞉ ℚ , (p < q)

open import UF-Powerset
open import UF-Subsingletons-FunExt

𝓣⁺ = 𝓣 ⁺

\end{code}

Lower real conditions:

\begin{code}

is-lower : 𝓟 ℚ → 𝓣 ̇
is-lower L = (q : ℚ) → q ∈ L → (p : ℚ) → p < q → p ∈ L

is-upper-open : 𝓟 ℚ → 𝓣 ̇
is-upper-open L = (p : ℚ) → p ∈ L → ∃ p' ꞉ ℚ , ((p < p') × p' ∈ L)

is-lower-real : 𝓟 ℚ → 𝓣 ̇
is-lower-real L = is-inhabited L × is-lower L × is-upper-open L

\end{code}

Upper real conditions:

\begin{code}

is-upper : 𝓟 ℚ → 𝓣 ̇
is-upper U = (p : ℚ) → p ∈ U → (q : ℚ) → p < q → q ∈ U

is-lower-open : 𝓟 ℚ → 𝓣 ̇
is-lower-open U = (q : ℚ) → q ∈ U → ∃ q' ꞉ ℚ , ((q' < q) × q' ∈ U)

is-upper-real : 𝓟 ℚ → 𝓣 ̇
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

ℝᴸ : 𝓣⁺ ̇
ℝᴸ = Σ L ꞉ 𝓟 ℚ , is-lower-real L

ℝᵁ : 𝓣⁺ ̇
ℝᵁ = Σ U ꞉ 𝓟 ℚ , is-upper-real U

ℝᴸ-is-set : is-set ℝᴸ
ℝᴸ-is-set = subsets-of-sets-are-sets (𝓟 ℚ) is-lower-real
             (powersets-are-sets'' fe fe pe)
             (λ {l} → being-lower-real-is-prop l)

ℝᵁ-is-set : is-set ℝᵁ
ℝᵁ-is-set = subsets-of-sets-are-sets (𝓟 ℚ) is-upper-real
             (powersets-are-sets'' fe fe pe)
             (λ {l} → being-upper-real-is-prop l)
\end{code}

Next we define the set of Dedekind reals as a subset of the lower
reals, after some preparation.

\begin{code}

are-ordered : 𝓟 ℚ → 𝓟 ℚ → 𝓣  ̇
are-ordered L U = (p q : ℚ) → p ∈ L → q ∈ U → p < q

are-located : 𝓟 ℚ → 𝓟 ℚ → 𝓣  ̇
are-located L U = (p q : ℚ) → p < q → p ∈ L ∨ q ∈ U

being-ordered-is-prop : (L U : 𝓟 ℚ) → is-prop (are-ordered L U)
being-ordered-is-prop _ _ = Π₄-is-prop fe (λ _ _ _ _ → order-is-prop-valued _ _)

being-located-is-prop : (L U : 𝓟 ℚ) → is-prop (are-located L U)
being-located-is-prop _ _ = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

technical-lemma : (L U L' U' : 𝓟 ℚ)
                → is-lower-open U'
                → are-located L  U
                → are-ordered L' U'
                → L  ⊆ L'
                → U' ⊆ U
technical-lemma L U L' U'
                U'-lower-open
                LU-located
                LU'-ordered
                L-is-contained-in-L'
                q
                q-is-in-U'        = γ
 where
  I : ∃ q' ꞉ ℚ , (q' < q) × q' ∈ U'
  I = U'-lower-open q q-is-in-U'

  II : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ U') → q ∈ U
  II (q' , l , i) = VI
   where
    III : q' ∈ L ∨ q ∈ U
    III = LU-located q' q l

    IV : ¬ (q' ∈ L)
    IV j = order-is-irrefl q' b
     where
      a : q' ∈ L'
      a = L-is-contained-in-L' q' j

      b : q' < q'
      b = LU'-ordered q' q' a i

    V : (q' ∈ L) + (q ∈ U) → q ∈ U
    V (inl j) = 𝟘-elim (IV j)
    V (inr k) = k

    VI : q ∈ U
    VI = ∥∥-rec (∈-is-prop U q) V III

  γ : q ∈ U
  γ = ∥∥-rec (∈-is-prop U q) II I

\end{code}

The following definition is of an auxiliary character:

\begin{code}

_is-an-upper-section-of_ : 𝓟 ℚ → 𝓟 ℚ → 𝓣 ̇
U is-an-upper-section-of L = is-lower-open U × are-ordered L U × are-located L U

any-two-upper-sections-are-equal : (L U U' : 𝓟 ℚ)
                                 → U  is-an-upper-section-of L
                                 → U' is-an-upper-section-of L
                                 → U ≡ U'
any-two-upper-sections-are-equal L U U' (a , b , c) (u , v , w) = γ
 where
  i : U ⊆ U'
  i = technical-lemma L U' L U  a w b (⊆-refl' L)

  j : U' ⊆ U
  j = technical-lemma L U  L U' u c v (⊆-refl' L)

  γ : U ≡ U'
  γ = subset-extensionality'' pe fe fe i j

\end{code}

The following is the version of the definition we are interested in:

\begin{code}

_is-upper-section-of_ : ℝᵁ → ℝᴸ → 𝓣 ̇
(U , _) is-upper-section-of  (L , _) = are-ordered L U × are-located L U

being-upper-section-is-prop : (l : ℝᴸ) (u : ℝᵁ)
                            → is-prop (u is-upper-section-of l)
being-upper-section-is-prop (L , _) (U , _) = ×-is-prop
                                               (being-ordered-is-prop L U)
                                               (being-located-is-prop L U)
\end{code}

We use the above auxiliary definition and lemma to establish the following:

\begin{code}

at-most-one-upper-section : (l : ℝᴸ) (u₀ u₁ : ℝᵁ)
                          → u₀ is-upper-section-of l
                          → u₁ is-upper-section-of l
                          → u₀ ≡ u₁
at-most-one-upper-section (L , _)
                          u₀@(U₀ , _ , _ , U₀-is-lower-open)
                          u₁@(U₁ , _ , _ , U₁-is-lower-open)
                          (lu₀-ordered , lu₀-located)
                          (lu₁-ordered , lu₁-located)      = γ
 where
  γ : u₀ ≡ u₁
  γ = to-subtype-≡
        being-upper-real-is-prop
        (any-two-upper-sections-are-equal L U₀ U₁
            (U₀-is-lower-open , lu₀-ordered , lu₀-located)
            (U₁-is-lower-open , lu₁-ordered , lu₁-located))
\end{code}

The Dedekind condition for a lower real:

\begin{code}

is-dedekind : ℝᴸ → 𝓣⁺ ̇
is-dedekind l = Σ u ꞉ ℝᵁ , (u is-upper-section-of l)

being-dedekind-is-prop : (l : ℝᴸ) → is-prop (is-dedekind l)
being-dedekind-is-prop l (u₀ , p₀) (u₁ , p₁) = to-subtype-≡
                                                 (being-upper-section-is-prop l)
                                                 (at-most-one-upper-section l u₀ u₁ p₀ p₁)
\end{code}

We define the Dedekind reals as a subset of the lower reals:

\begin{code}

ℝ : 𝓣⁺ ̇
ℝ = Σ l ꞉ ℝᴸ , is-dedekind l

\end{code}

The forgetful map of the reals into the lower reals is an embedding
and hence ℝ is a set:

\begin{code}

ℝ-to-ℝᴸ : ℝ → ℝᴸ
ℝ-to-ℝᴸ = pr₁

open import UF-Embeddings

ℝ-to-ℝᴸ-is-embedding : is-embedding ℝ-to-ℝᴸ
ℝ-to-ℝᴸ-is-embedding = pr₁-is-embedding being-dedekind-is-prop

ℝ-is-set : is-set ℝ
ℝ-is-set = subsets-of-sets-are-sets ℝᴸ is-dedekind
             ℝᴸ-is-set
             (λ {l} → being-dedekind-is-prop l)
\end{code}

NB. This won't be a *topological* embedding in topological
models. Because ℝ and ℝᴸ are sets, in the sense of HoTT/UF, the
embedding condition merely says that the map is left-cancellable.

We unpack and reorder the definition to emphasize that it amounts to
the usual one:

\begin{code}

open import UF-Equiv

is-dedekind-section : 𝓟 ℚ × 𝓟 ℚ → 𝓣 ̇
is-dedekind-section (L , U) = is-inhabited L × is-lower L × is-upper-open L
                            × is-inhabited U × is-upper U × is-lower-open U
                            × are-ordered L U × are-located L U


NB : ℝ ≃ (Σ (L , R) ꞉ 𝓟 ℚ × 𝓟 ℚ , is-dedekind-section (L , R))

NB = qinveq (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
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
    b (inr v) = 𝟘-elim (order-is-irrefl q (LU-ordered q q l v))

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
    b (inl u) = 𝟘-elim (order-is-irrefl q (LU-ordered q q u l))
    b (inr v) = v

open import UF-Base

NB₂ : ℝ ≃ (Σ (L , U) ꞉ 𝓟 ℚ × 𝓟 ℚ
                , is-inhabited L × is-upper-open L
                × is-inhabited U × is-lower-open U
                × are-ordered L U × are-located L U)

NB₂ = qinveq (λ ((L , Li , _ , Lo) , (U , Ui , _ , Uo) , o , l)
              → ((L , U) , Li , Lo , Ui , Uo , o , l))

            ((λ ((L , U) , Li , Lo , Ui , Uo , o , l)
              → ((L , Li , ordered-located-gives-lower L U o l , Lo) ,
                 (U , Ui , ordered-located-gives-upper L U o l , Uo) ,
                 o , l)) ,

             (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
              → to-Σ-≡ (to-subtype-≡ being-lower-real-is-prop refl ,
                        being-dedekind-is-prop (L , Li , Ll , Lo) _ _)) ,

             (λ ((L , U) , Li , Lo , Ui , Uo , o , l)
              → to-subtype-≡ (λ (L , U) → ×₆-is-prop
                                           (being-inhabited-is-prop L)
                                           (being-upper-open-is-prop L)
                                           (being-inhabited-is-prop U)
                                           (being-lower-open-is-prop U)
                                           (being-ordered-is-prop L U)
                                           (being-located-is-prop L U))
                              refl))
\end{code}

And there is a further set of axioms for defining ℝ, assuming the
above further properties of order:

\begin{code}

disjoint-criterion : (L U : 𝓟 ℚ)
                   → are-ordered L U
                   → are-disjoint L U
disjoint-criterion L U o p (p-is-in-L , p-is-in-U) =
 order-is-irrefl p (o p p p-is-in-L p-is-in-U)

module _ (ϕ : further-properties-of-ℚ-and-its-order) where

 open further-properties-of-ℚ-and-its-order ϕ

 ordered-criterion : (L U : 𝓟 ℚ)
                   → is-lower L
                   → are-disjoint L U
                   → are-ordered L U
 ordered-criterion L U L-is-lower LU-disjoint p q p-in-L q-in-U = γ
  where
   I : p ∉ U
   I p-in-U = LU-disjoint p (p-in-L , p-in-U)

   II : p ≢ q
   II e = I (transport (_∈ U) (e ⁻¹) q-in-U)

   III : ¬(q < p)
   III l = LU-disjoint q (L-is-lower p p-in-L q l , q-in-U)

   γ : p < q
   γ = order-criterion p q II III


 NB₃ : ℝ ≃ (Σ (L , U) ꞉ 𝓟 ℚ × 𝓟 ℚ
                 , is-inhabited L × is-lower L × is-upper-open L
                 × is-inhabited U × is-upper U × is-lower-open U
                 × are-disjoint L U × are-located L U)

 NB₃ = qinveq (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
               → ((L , U) , Li , Ll , Lo , Ui , Uu , Uo , disjoint-criterion L U o , l))

             ((λ ((L , U) , Li , Ll , Lo , Ui , Uu , Uo , d , l)
               → ((L , Li , Ll , Lo) ,
                  (U , Ui , Uu , Uo) ,
                  ordered-criterion L U Ll d , l)) ,

              (λ ((L , Li , Ll , Lo) , (U , Ui , Uu , Uo) , o , l)
               → to-Σ-≡ (to-subtype-≡ being-lower-real-is-prop refl ,
                         being-dedekind-is-prop (L , Li , Ll , Lo) _ _)) ,

              (λ ((L , U) , Li , Lo , Ui , Uo , o , l)
               → to-subtype-≡ (λ (L , U) → ×₈-is-prop
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

is-bounded-above : 𝓟 ℚ → 𝓣 ̇
is-bounded-above L = ∃ s ꞉ ℚ , s ∉ L

is-located : 𝓟 ℚ → 𝓣 ̇
is-located L = ((r s : ℚ) → r < s → r ∈ L ∨ s ∉ L)

is-troelstra : ℝᴸ → 𝓣 ̇
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
                          ((U , U-is-inhabited , _ , _) , LU-ordered , LU-located) = γ
 where
  bounded : (∃ s ꞉ ℚ , s ∉ L)
  bounded = ∥∥-functor f U-is-inhabited
   where
    f : (Σ q ꞉ ℚ , q ∈ U) → Σ q ꞉ ℚ , q ∉ L
    f (q , q-is-in-U) = q , (λ q-is-in-L → order-is-irrefl q (c q-is-in-L))
     where
      c : q ∈ L → q < q
      c q-is-in-L = LU-ordered q q q-is-in-L q-is-in-U

  located : (r s : ℚ) → r < s → r ∈ L ∨ s ∉ L
  located r s less = ∥∥-functor f (LU-located r s less)
   where
    f : (r ∈ L) + (s ∈ U) → (r ∈ L) + (s ∉ L)
    f (inl r-is-in-L) = inl r-is-in-L
    f (inr r-is-in-L) = inr (λ s-is-in-L → order-is-irrefl s (d s-is-in-L))
     where
      d : s ∈ L → s < s
      d s-is-in-L = LU-ordered s s s-is-in-L r-is-in-L

  γ : is-troelstra l
  γ = bounded , located

\end{code}

For the converse, we need the further assumptions on _<_ mentioned
above. A lower Dedekind real may or may not have an upper section. If
it does, it is given by the following candidate.

\begin{code}

candidate-upper-section : 𝓟 ℚ → 𝓟 ℚ
candidate-upper-section L = λ q → (∃ p ꞉ ℚ , (p < q) × (p ∉ L)) , ∃-is-prop

module _ (ϕ : further-properties-of-ℚ-and-its-order) where

 open further-properties-of-ℚ-and-its-order ϕ

 candidate-upper-section-is-lower-open : (L : 𝓟 ℚ)
                                       → is-lower-open (candidate-upper-section L)
 candidate-upper-section-is-lower-open L q q-is-in-U = γ
  where
   f : (Σ p ꞉ ℚ , (p < q) × (p ∉ L)) → ∃ p' ꞉ ℚ , (p' < q) × (∃ p ꞉ ℚ , (p < p') × (p ∉ L))
   f (p , i , p-is-not-in-L) = ∥∥-functor g (ℚ-is-dense p q i)
    where
     g : (Σ p' ꞉ ℚ , (p < p') × (p' < q))
       → Σ p' ꞉ ℚ , (p' < q) × (∃ p ꞉ ℚ , (p < p') × (p ∉ L))
     g (p' , j , k) = p' , k , ∣ p , j , p-is-not-in-L ∣

   γ : ∃ q' ꞉ ℚ , ((q' < q) × (q' ∈ candidate-upper-section L))
   γ = ∥∥-rec ∃-is-prop f q-is-in-U

 candidate-upper-section-is-ordered : (L : 𝓟 ℚ)
                                    → is-lower L
                                    → is-located L
                                    → are-ordered L (candidate-upper-section L)
 candidate-upper-section-is-ordered L L-is-lower b p q p-is-in-L q-is-in-U = γ
    where
     f : (Σ r ꞉ ℚ , (r < q) × (r ∉ L)) → p < q
     f (r , i , r-is-not-in-L) = ∥∥-rec (order-is-prop-valued p q) g (b r q i)
      where
       g : (r ∈ L) + (q ∉ L) → p < q
       g (inl r-is-in-L)     = 𝟘-elim (r-is-not-in-L r-is-in-L)
       g (inr q-is-not-in-L) = order-criterion p q I II
        where
         I : p ≢ q
         I refl = q-is-not-in-L p-is-in-L

         II : ¬(q < p)
         II less = q-is-not-in-L (L-is-lower p p-is-in-L q less)

     γ : p < q
     γ = ∥∥-rec (order-is-prop-valued p q) f q-is-in-U

 candidate-upper-section-is-located : (L : 𝓟 ℚ)
                                    → is-located L
                                    → are-located L (candidate-upper-section L)
 candidate-upper-section-is-located L located p q less = ∥∥-rec ∨-is-prop II I
    where
     I : ∃ p' ꞉ ℚ , (p < p') × (p' < q)
     I = ℚ-is-dense p q less

     II : (Σ p' ꞉ ℚ , (p < p') × (p' < q)) → p ∈ L ∨ q ∈ candidate-upper-section L
     II (p' , i , j) = ∥∥-rec ∨-is-prop IV III
      where
       III : p ∈ L ∨ p' ∉ L
       III = located p p' i

       IV : (p ∈ L) + (p' ∉ L) → p ∈ L ∨ q ∈ candidate-upper-section L
       IV (inl p-is-in-L) = ∣ inl p-is-in-L ∣
       IV (inr p'-is-not-in-L) = ∣ inr ∣ (p' , j , p'-is-not-in-L) ∣ ∣

 candidate-upper-section-is-inhabited : (L : 𝓟 ℚ)
                                      → is-bounded-above L
                                      → is-located L
                                      → is-inhabited (candidate-upper-section L)
 candidate-upper-section-is-inhabited L bounded located =  γ
    where
     f : (Σ s ꞉ ℚ , s ∉ L) → is-inhabited (candidate-upper-section L)
     f (s , ν) = ∥∥-functor g (ℚ-is-upper-open s)
      where
       g : (Σ p ꞉ ℚ , s < p) → Σ p ꞉ ℚ , p ∈ candidate-upper-section L
       g (p , i) = p , ∣ s , i , ν ∣

     γ : is-inhabited (candidate-upper-section L)
     γ = ∥∥-rec (being-inhabited-is-prop (candidate-upper-section L)) f bounded

 candidate-upper-section-is-upper : (L : 𝓟 ℚ)
                                  → is-lower L
                                  → is-bounded-above L
                                  → is-located L
                                  → is-upper (candidate-upper-section L)
 candidate-upper-section-is-upper L lower bounded located p p-is-in-U q less = γ
  where
   γ : ∃ q' ꞉ ℚ , (q' < q) × (q' ∉ L)
   γ = ∣ p ,
        less ,
        (λ p-is-in-L → order-is-irrefl p
                        (candidate-upper-section-is-ordered
                          L lower located p p p-is-in-L p-is-in-U)) ∣

\end{code}

The candidate upper section is the unique candidate in the following sense:

\begin{code}

 unique-candidate : (L U : 𝓟 ℚ)
                  → is-dedekind-section (L , U) → U ≡ candidate-upper-section L
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

   γ : U ≡ candidate-upper-section L
   γ = any-two-upper-sections-are-equal L U
        (candidate-upper-section L)
        (Uo , ordered , located)
        III

\end{code}

And, as promised, the Troelstra condition implies the Dedekind condition:

\begin{code}

 troelstra-gives-dedekind : (l : ℝᴸ) → is-troelstra l → is-dedekind l
 troelstra-gives-dedekind (L , L-is-inhabited , L-is-lower , L-is-upper-open)
                          (bounded , located) =
  (candidate-upper-section L ,
    (candidate-upper-section-is-inhabited L bounded located ,
     candidate-upper-section-is-upper L L-is-lower bounded located ,
     candidate-upper-section-is-lower-open L)) ,
   candidate-upper-section-is-ordered L L-is-lower located ,
   candidate-upper-section-is-located L located

\end{code}

The set of Troelstra reals, again as a subset of the lower reals:

\begin{code}

ℝᵀ : 𝓣⁺ ̇
ℝᵀ = Σ l ꞉ ℝᴸ , is-troelstra l

\end{code}

Question. Can we prove that ℝ = ℝᵀ with propositional and functional
extensionality, without univalence? The problem is that the Dedekind
condition and the troelstra condition have different universe levels,
and hence propositional extensionality is not applicable to show that
they are equal, as their equality doesn't even type check. Would
universe lifting help? I haven't thought about this.

\begin{code}

dedekind-agrees-with-troelstra : further-properties-of-ℚ-and-its-order → ℝ ≃ ℝᵀ
dedekind-agrees-with-troelstra ϕ = γ
 where
  f : ℝ → ℝᵀ
  f (l , h) = l , dedekind-gives-troelstra l h

  g : ℝᵀ → ℝ
  g (l , k) = l , troelstra-gives-dedekind ϕ l k

  γ : ℝ ≃ ℝᵀ
  γ = qinveq f (g ,
               (λ (l , h) → to-subtype-≡ being-dedekind-is-prop refl) ,
               (λ (l , k) → to-subtype-≡ being-troelstra-is-prop refl))
\end{code}

We now consider consequences of excluded middle.

\begin{code}

open import UF-ExcludedMiddle

EM-gives-troelstra-locatedness : EM 𝓣 → ((L , _) : ℝᴸ) → is-located L
EM-gives-troelstra-locatedness
  em l@(L , L-is-inhabited , L-is-lower , L-is-upper-open) r s less = γ δ
 where
  δ : (s ∈ L) + (s ∉ L)
  δ = em (s ∈ L) (∈-is-prop L s)

  γ : type-of δ → (r ∈ L) ∨ (s ∉ L)
  γ (inl s-is-in-L)     = ∣ inl (L-is-lower s s-is-in-L r less) ∣
  γ (inr s-is-not-in-L) = ∣ inr s-is-not-in-L ∣

\end{code}

The bounded lower reals:

\begin{code}

ℝᴮᴸ : 𝓣⁺ ̇
ℝᴮᴸ = Σ (L , _) ꞉ ℝᴸ , is-bounded-above L

\end{code}

The boundedness condition only excludes a point at infinity in the
lower reals:

\begin{code}

∞ : 𝓟 ℚ
∞ = λ q → ⊤Ω

∞-is-lower-real-but-not-bounded-above : further-properties-of-ℚ-and-its-order
                                      → (is-lower-real ∞) × (¬ is-bounded-above ∞)
∞-is-lower-real-but-not-bounded-above ϕ = a , b
 where
  open further-properties-of-ℚ-and-its-order ϕ

  a : is-lower-real ∞
  a = ∥∥-rec (being-inhabited-is-prop ∞) (λ q → ∣ q , * ∣) ℚ-is-inhabited ,
      (λ _ _ _ _ → *) ,
      (λ p * → ∥∥-rec ∃-is-prop (λ (q , i) → ∣ q , i , * ∣) (ℚ-is-upper-open p))

  b : ¬ is-bounded-above ∞
  b bounded = ∥∥-rec 𝟘-is-prop (λ (q , q-is-not-in-∞) → q-is-not-in-∞ *) bounded

\end{code}

In connection with a discussion above, notice that we don't need
univalence for the following, which says that the Troelstra reals
agree with the bounded lower reals if we assume excluded middle:

\begin{code}

ℝᵀ-and-ℝᴮᴸ-agree-under-EM : EM 𝓣 → further-properties-of-ℚ-and-its-order → ℝᵀ ≡ ℝᴮᴸ
ℝᵀ-and-ℝᴮᴸ-agree-under-EM em ϕ = ap Σ γ
 where
  δ : is-troelstra ∼ λ (L , _) → is-bounded-above L
  δ l@(L , c) = pe (being-troelstra-is-prop l)
                   (being-bounded-above-is-prop L)
                   pr₁
                   (λ β → β , EM-gives-troelstra-locatedness em l)

  γ : is-troelstra ≡ (λ (L , _) → is-bounded-above L)
  γ = dfunext fe δ

\end{code}

Therefore, under excluded middle, the Dedekind reals agree with the
bounded lower reals:

\begin{code}

ℝ-and-ℝᴮᴸ-agree-under-EM : EM 𝓣
                         → further-properties-of-ℚ-and-its-order
                         → ℝ ≃ ℝᴮᴸ
ℝ-and-ℝᴮᴸ-agree-under-EM em ϕ = transport (ℝ ≃_)
                                 (ℝᵀ-and-ℝᴮᴸ-agree-under-EM em ϕ)
                                 (dedekind-agrees-with-troelstra ϕ)
\end{code}

We also need further properties of order for embedding the rationals into the reals:

\begin{code}

module rational-reals (ϕ : further-properties-of-ℚ-and-its-order) where

 open further-properties-of-ℚ-and-its-order ϕ

 ℚ-to-ℝᴸ : ℚ → ℝᴸ
 ℚ-to-ℝᴸ q = L ,
             ℚ-is-lower-open q ,
             (λ p i r j → transitivity r p q j i) ,
             (λ p →  ℚ-is-dense p q)
  where
   L : 𝓟 ℚ
   L p = (p < q) , order-is-prop-valued p q

 ℚ-to-ℝᵁ : ℚ → ℝᵁ
 ℚ-to-ℝᵁ q = U ,
             ℚ-is-upper-open q ,
             (λ p i r j → transitivity q p r i j) ,
             (λ p i → ∥∥-functor (λ (r , j , k) → r , k , j) (ℚ-is-dense q p i))
  where
   U : 𝓟 ℚ
   U p = (q < p) , order-is-prop-valued q p


 ℚ-to-ℝᵁ-is-upper-section-of-ℚ-to-ℝᴸ : (q : ℚ) → (ℚ-to-ℝᵁ q) is-upper-section-of (ℚ-to-ℝᴸ q)
 ℚ-to-ℝᵁ-is-upper-section-of-ℚ-to-ℝᴸ q = (λ p → transitivity p q) , (λ p → cotransitivity p q)

 ℚ-to-ℝᴸ-is-dedekind : (q : ℚ) → is-dedekind (ℚ-to-ℝᴸ q)
 ℚ-to-ℝᴸ-is-dedekind q = ℚ-to-ℝᵁ q , ℚ-to-ℝᵁ-is-upper-section-of-ℚ-to-ℝᴸ q

 ℚ-to-ℝ : ℚ → ℝ
 ℚ-to-ℝ q = ℚ-to-ℝᴸ q , ℚ-to-ℝᴸ-is-dedekind q

{- TODO.
 ℚ-to-ℝ-is-embedding : is-embedding ℚ-to-ℝ
 ℚ-to-ℝ-is-embedding = {!!}
-}

\end{code}

TODO. Derive a constructive taboo from the assumption that every
bounded lower real is a Dedekind real.

\begin{code}
{-
blah : (A : 𝓣 ̇ ) → is-prop A → ℚ → ℚ → ℝᴸ
blah A i p₀ p₁ = L , L-is-inhabited , L-is-lower , L-is-upper-open
 where
  L : 𝓟 ℚ
  L p = (((p < p₀) × (A → p < p₁)) ,
        ×-is-prop
         (order-is-prop-valued p p₀)
         (Π-is-prop fe (λ _ → order-is-prop-valued p p₁)))


  L-is-inhabited : is-inhabited L
  L-is-inhabited = {!!}

  L-is-lower : is-lower L
  L-is-lower = {!!}

  L-is-upper-open : is-upper-open L
  L-is-upper-open = {!!}
-}
\end{code}
