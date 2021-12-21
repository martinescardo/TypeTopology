Martin Escardo, 20th December 2021

Some thoughts about Dedekind reals.

We generalize the rationals to any type with a prop-valued,
irreflexive relation _<_.

To show that the Dedekind reals agree with their version proposed by Troelstra,
we further assume that _<_ is dense, upper open, and satisfies p ≢ q →
¬(q < p) → p < q (which the type of rationals does).

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

record further-properties-of-order : 𝓣 ̇ where
 constructor
  further
 field
  ℚ-is-dense      : (p r : ℚ) → p < r → ∃ q ꞉ ℚ , (p < q) × (q < r)
  order-criterion : (p q : ℚ) → p ≢ q → ¬(q < p) → p < q
  ℚ-is-upper-open : (p : ℚ) → ∃ q ꞉ ℚ , (p < q)


open import UF-Powerset
open import UF-Subsingletons-FunExt

𝓣⁺ = 𝓣 ⁺

is-lower : 𝓟 ℚ → 𝓣 ̇
is-lower L = (q : ℚ) → q ∈ L → (p : ℚ) → p < q → p ∈ L

is-upper-open : 𝓟 ℚ → 𝓣 ̇
is-upper-open A = (p : ℚ) → p ∈ A → ∃ p' ꞉ ℚ , ((p < p') × p' ∈ A)

is-upper : 𝓟 ℚ → 𝓣 ̇
is-upper U = (p : ℚ) → p ∈ U → (q : ℚ) → p < q → q ∈ U

is-lower-open : 𝓟 ℚ → 𝓣 ̇
is-lower-open A = (q : ℚ) → q ∈ A → ∃ q' ꞉ ℚ , ((q' < q) × q' ∈ A)

is-lower-real : 𝓟 ℚ → 𝓣 ̇
is-lower-real L = is-inhabited L × is-lower L × is-upper-open L

is-upper-real : 𝓟 ℚ → 𝓣 ̇
is-upper-real U = is-inhabited U × is-upper U × is-lower-open U

being-lower-real-is-prop : (L : 𝓟 ℚ) → is-prop (is-lower-real L)
being-lower-real-is-prop L = ×₃-is-prop
                               ∃-is-prop
                               (Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop L _))
                               (Π₂-is-prop fe (λ _ _ → ∃-is-prop))

being-upper-real-is-prop : (U : 𝓟 ℚ) → is-prop (is-upper-real U)
being-upper-real-is-prop U = ×₃-is-prop
                               ∃-is-prop
                               (Π₄-is-prop fe (λ _ _ _ _ → ∈-is-prop U _))
                               (Π₂-is-prop fe (λ _ _ → ∃-is-prop))
\end{code}

The set of lower reals:

\begin{code}

𝕃 : 𝓣⁺  ̇
𝕃 = Σ L ꞉ 𝓟 ℚ , is-lower-real L

𝕃-is-set : is-set 𝕃
𝕃-is-set = subsets-of-sets-are-sets (𝓟 ℚ) is-lower-real
            (powersets-are-sets'' fe fe pe)
            (λ {l} → being-lower-real-is-prop l)

𝕌 : 𝓣⁺  ̇
𝕌 = Σ U ꞉ 𝓟 ℚ , is-upper-real U

located : 𝓟 ℚ → 𝓟 ℚ → 𝓣  ̇
located L U = (p q : ℚ) → p < q → p ∈ L ∨ q ∈ U

ordered : 𝓟 ℚ → 𝓟 ℚ → 𝓣  ̇
ordered L U = (p q : ℚ) → p ∈ L → q ∈ U → p < q

lemma₀ : (L L' U U' : 𝓟 ℚ)
       → is-lower-open U'
       → located L U
       → ordered L' U'
       → L  ⊆ L'
       → U' ⊆ U
lemma₀ L L' U U'
       U'-lower-open
       LU-located
       LU'-ordered
       L-is-contained-in-L'
       q
       q-is-in-U'  = γ
 where
  I : ∃ q' ꞉ ℚ , (q' < q) × q' ∈ U'
  I = U'-lower-open q q-is-in-U'

  II : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ U') → q ∈ U
  II (q' , l , i) = ∥∥-rec (∈-is-prop U q) V III
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

  γ : q ∈ U
  γ = ∥∥-rec (∈-is-prop U q) II I

_upper-section-of_ : 𝓟 ℚ → 𝓟 ℚ → 𝓣 ̇
U upper-section-of L = is-lower-open U × ordered L U × located L U

any-two-upper-sections-are-equal : (L U U' : 𝓟 ℚ)
                                 → U  upper-section-of L
                                 → U' upper-section-of L
                                 → U ≡ U'
any-two-upper-sections-are-equal L U U' (a , b , c) (u , v , w) =
  subset-extensionality'' pe fe fe
   (lemma₀ L L U' U a w b (⊆-refl' L))
   (lemma₀ L L U U' u c v (⊆-refl' L))

_is-upper-section-of_ : 𝕌 → 𝕃 → 𝓣 ̇
(U , _) is-upper-section-of  (L , _) = ordered L U × located L U

at-most-one-upper-section : (l : 𝕃) (u₀ u₁ : 𝕌)
                          → u₀ is-upper-section-of l
                          → u₁ is-upper-section-of l
                          → u₀ ≡ u₁
at-most-one-upper-section (L , l)
                          (U₀ , _ , _ , U₀-is-lower-open)
                          (U₁ , _ , _ , U₁-is-lower-open)
                          (lu₀-ordered , lu₀-located)
                          (lu₁-ordered , lu₁-located)
  = to-subtype-≡
      being-upper-real-is-prop
      (any-two-upper-sections-are-equal L U₀ U₁
          (U₀-is-lower-open , lu₀-ordered , lu₀-located)
          (U₁-is-lower-open , lu₁-ordered , lu₁-located))

is-dedekind : 𝕃 → 𝓣⁺ ̇
is-dedekind l = Σ u ꞉ 𝕌 , (u is-upper-section-of l)

being-upper-section-is-prop : (l : 𝕃) (u : 𝕌) → is-prop (u is-upper-section-of l)
being-upper-section-is-prop l u = ×-is-prop
                                   (Π₄-is-prop fe (λ _ _ _ _ → order-is-prop-valued _ _))
                                   (Π₃-is-prop fe (λ _ _ _ → ∨-is-prop))

being-dedekind-is-prop : (l : 𝕃) → is-prop (is-dedekind l)
being-dedekind-is-prop l (u₀ , p₀) (u₁ , p₁) =
      to-subtype-≡
        (being-upper-section-is-prop l)
        (at-most-one-upper-section l u₀ u₁ p₀ p₁)

\end{code}

The Dedekind reals:

\begin{code}

ℝ : 𝓣⁺  ̇
ℝ = Σ l ꞉ 𝕃 , is-dedekind l

\end{code}

The following shows that there is some redundancy in the definition of
Dedekind real:

\begin{code}

subset-with-upper-section-is-prop : (L : 𝓟 ℚ)
                                  → (Σ U ꞉ 𝓟 ℚ , U upper-section-of L)
                                  → is-lower L
subset-with-upper-section-is-prop L
  (U , U-lower-open , LU-ordered , LU-located ) = γ
 where
  γ : is-lower L
  γ q l p m = ∥∥-rec (∈-is-prop L p) b a
   where
    a : p ∈ L ∨ q ∈ U
    a = LU-located p q m

    b : (p ∈ L) + (q ∈ U) → p ∈ L
    b (inl u) = u
    b (inr v) = 𝟘-elim (order-is-irrefl q (LU-ordered q q l v))

\end{code}

The forgetful map of the reals into the lower reals is an embedding
and hence ℝ is a set:

\begin{code}

ℝ-to-𝕃 : ℝ → 𝕃
ℝ-to-𝕃 = pr₁

open import UF-Embeddings

ℝ-to-𝕃-is-embedding : is-embedding ℝ-to-𝕃
ℝ-to-𝕃-is-embedding = pr₁-is-embedding being-dedekind-is-prop

ℝ-is-set : is-set ℝ
ℝ-is-set = subsets-of-sets-are-sets 𝕃 is-dedekind
            𝕃-is-set
            (λ {l} → being-dedekind-is-prop l)

\end{code}

We now consider an alternative definition of the Dedekind reals
offered by Troelstra.

\begin{code}

is-bounded : 𝓟 ℚ → 𝓣 ̇
is-bounded L = ∃ s ꞉ ℚ , s ∉ L

being-bounded-is-prop : (L : 𝓟 ℚ) → is-prop (is-bounded L)
being-bounded-is-prop L = ∃-is-prop

is-troelstra-located : 𝓟 ℚ → 𝓣 ̇
is-troelstra-located L = ((r s : ℚ) → r < s → r ∈ L ∨ s ∉ L)

being-troelstra-located-is-prop : (L : 𝓟 ℚ) → is-prop (is-troelstra-located L)
being-troelstra-located-is-prop L = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

is-troelstra : 𝕃 → 𝓣 ̇
is-troelstra (L , _) = is-bounded L × is-troelstra-located L

being-troelstra-is-prop : (l : 𝕃) → is-prop (is-troelstra l)
being-troelstra-is-prop (L , _) = ×-is-prop
                                   (being-bounded-is-prop L)
                                   (being-troelstra-located-is-prop L)

dedekind-gives-troelstra : (l : 𝕃) → is-dedekind l → is-troelstra l
dedekind-gives-troelstra (L , _ , _ , _)
                       ((U , U-is-inhabited , _ , _) , LU-ordered , LU-located) = a , b
 where
  a : (∃ s ꞉ ℚ , s ∉ L)
  a = ∥∥-functor
       (λ (q , q-is-in-U)
          → q ,
            λ q-is-in-L → order-is-irrefl q (LU-ordered q q q-is-in-L q-is-in-U))
       U-is-inhabited

  b : (r s : ℚ) → r < s → r ∈ L ∨ s ∉ L
  b r s less = ∥∥-functor
                 f
                 (LU-located r s less)
   where
    f : (r ∈ L) + (s ∈ U) → (r ∈ L) + (s ∉ L)
    f (inl r-is-in-L) = inl r-is-in-L
    f (inr r-is-in-L) = inr (λ s-is-in-L → order-is-irrefl s
                                            (LU-ordered s s s-is-in-L r-is-in-L))

\end{code}

For the converse, we need further assumptions on _<_:

\begin{code}

troelstra-gives-dedekind : further-properties-of-order
                         → (l : 𝕃) → is-troelstra l → is-dedekind l
troelstra-gives-dedekind (further ℚ-is-dense order-criterion ℚ-is-upper-open)
                       l@(L , L-is-inhabited , L-is-lower , L-is-upper-open) (a , b) = γ
 where
  U : 𝓟 ℚ
  U q = (∃ p ꞉ ℚ , (p < q) × (p ∉ L)) , ∃-is-prop

  U-is-inhabited : is-inhabited U
  U-is-inhabited = ∥∥-rec (being-inhabited-is-prop U) f a
   where
    f : (Σ s ꞉ ℚ , s ∉ L) → is-inhabited U
    f (s , ν) = ∥∥-functor g (ℚ-is-upper-open s)
     where
      g : (Σ p ꞉ ℚ , s < p) → Σ p ꞉ ℚ , p ∈ U
      g (p , i) = p , ∣ s , i , ν ∣

  LU-ordered : ordered L U
  LU-ordered p q p-is-in-L q-is-in-U = ∥∥-rec (order-is-prop-valued p q) f q-is-in-U
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

  U-is-upper : is-upper U
  U-is-upper p p-is-in-U q less = ∣ p ,
                                   less ,
                                   (λ p-is-in-L → order-is-irrefl p
                                                   (LU-ordered p p p-is-in-L p-is-in-U)) ∣

  U-is-lower-open : is-lower-open U
  U-is-lower-open q q-is-in-U = ∥∥-rec ∃-is-prop f q-is-in-U
   where
    f : (Σ p ꞉ ℚ , (p < q) × (p ∉ L)) → ∃ p' ꞉ ℚ , (p' < q) × (∃ p ꞉ ℚ , (p < p') × (p ∉ L))
    f (p , i , p-is-not-in-L) = ∥∥-functor g (ℚ-is-dense p q i)
     where
      g : (Σ p' ꞉ ℚ , (p < p') × (p' < q))
        → Σ p' ꞉ ℚ , (p' < q) × (∃ p ꞉ ℚ , (p < p') × (p ∉ L))
      g (p' , j , k) = p' , k , ∣ p , j , p-is-not-in-L ∣

  LU-located : located L U
  LU-located p q less = ∥∥-rec ∨-is-prop II I
   where
    I : ∃ p' ꞉ ℚ , (p < p') × (p' < q)
    I = ℚ-is-dense p q less

    II : (Σ p' ꞉ ℚ , (p < p') × (p' < q)) → p ∈ L ∨ q ∈ U
    II (p' , i , j) = ∥∥-rec ∨-is-prop IV III
     where
      III : p ∈ L ∨ p' ∉ L
      III = b p p' i

      IV : (p ∈ L) + (p' ∉ L) → p ∈ L ∨ q ∈ U
      IV (inl p-is-in-L) = ∣ inl p-is-in-L ∣
      IV (inr p'-is-not-in-L) = ∣ inr ∣ (p' , j , p'-is-not-in-L) ∣ ∣

  γ : is-dedekind l
  γ = (U , (U-is-inhabited , U-is-upper , U-is-lower-open)) , LU-ordered , LU-located


𝕋 : 𝓣⁺ ̇
𝕋 = Σ l ꞉ 𝕃 , is-troelstra l

\end{code}

Question. Can we prove that ℝ = troeltra-reals with propositional and
functional extensionality, without univalence? The problem is that the
Dedekind condition and the troelstra condition have different universe
levels, and hence propositional extensionality is not applicable to
show that they are equal, as their equality doesn't even type
check. Would universe lifting help? I haven't thought about this.

\begin{code}

open import UF-Equiv
open import UF-Univalence

dedekind-agrees-with-troelstra : further-properties-of-order
                               → is-univalent (𝓣 ⁺)
                               → ℝ ≡ 𝕋
dedekind-agrees-with-troelstra ϕ ua = eqtoid ua ℝ 𝕋 e
 where
  f : ℝ → 𝕋
  f (l , h) = l , dedekind-gives-troelstra l h

  g : 𝕋 → ℝ
  g (l , k) = l , troelstra-gives-dedekind ϕ l k

  e : ℝ ≃ 𝕋
  e = qinveq f (g ,
               (λ (l , h) → to-subtype-≡ being-dedekind-is-prop refl) ,
               (λ (l , k) → to-subtype-≡ being-troelstra-is-prop refl))
\end{code}

\begin{code}

open import UF-ExcludedMiddle

EM-gives-troelstra-locatedness : EM 𝓣 → ((L , _) : 𝕃) → is-troelstra-located L
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

𝕃β : 𝓣 ⁺ ̇
𝕃β = Σ (L , _) ꞉ 𝕃 , is-bounded L

\end{code}

In connection with a discussion above, notice that we don't need
univalence for the following, which says that the Troelstra reals
agree with the bounded lower reals if we assume excluded middle:

\begin{code}

𝕋-and-𝕃β-agree-under-EM : EM 𝓣 → further-properties-of-order → 𝕋 ≡ 𝕃β
𝕋-and-𝕃β-agree-under-EM em ϕ = ap Σ γ
 where
  δ : is-troelstra ∼ λ (L , _) → is-bounded L
  δ l@(L , c) = pe (being-troelstra-is-prop l) (being-bounded-is-prop L)
                   pr₁
                   λ β → β , EM-gives-troelstra-locatedness em l
  γ : is-troelstra ≡ λ (L , _) → is-bounded L
  γ = dfunext fe δ

\end{code}

And assuming both univalence and excluded middle, the Dedekind reals
agree with the bounded lower reals:

\begin{code}

ℝ-and-𝕃β-agree-under-EM : EM 𝓣
                        → further-properties-of-order
                        → is-univalent 𝓣⁺
                        → ℝ ≡ 𝕃β
ℝ-and-𝕃β-agree-under-EM em ϕ ua = dedekind-agrees-with-troelstra ϕ ua
                                ∙ 𝕋-and-𝕃β-agree-under-EM em ϕ
\end{code}

We will also need ℚ-upper and -lower openness for the following:

\begin{code}

{- TODO:
ℚ-to-𝕃 : ℚ → 𝕃
ℚ-to-𝕃 q = (λ p → (p < q) , order-is-prop-valued p q) ,
           {!!} ,
           {!!} ,
           {!!}

ℚ-to-𝕌 : ℚ → 𝕌
ℚ-to-𝕌 q = {!!} ,
           {!!} ,
           {!!} ,
           {!!}

rational-couple : (q : ℚ) → is-upper-section-of (ℚ-to-𝕃 q) (ℚ-to-𝕌 q)
rational-couple = {!!}

rationals-have-_is-upper-section-of_ : (q : ℚ) → is-dedekind (ℚ-to-𝕃 q)
rationals-have-_is-upper-section-of_ q = ℚ-to-𝕌 q , rational-couple q

ℚ-to-ℝ : ℚ → ℝ
ℚ-to-ℝ q = ℚ-to-𝕃 q , rationals-have-_is-upper-section-of_ q
-}
\end{code}

TODO. Define Dedekind completeness and show that ℝ is Dedekind complete.
