Martin Escardo, 23 June 2025.

The following paper has a notion of flabbiness in the internal
language of a 1-topos.

[1] Ingo Blechschmidt (2018). Flabby and injective objects in toposes.
    https://arxiv.org/abs/1810.12708

    More recent version at
    https://www.speicherleck.de/iblech/stuff/paper-flabby-objects.pdf

This definition of flabbiness uses the two notions of "subterminal"
and "subsingleton" subsets, as defined in e.g.

[2] Kock, A. (1991). Algebras for the partial map classifier
    monad. In: Carboni, A., Pedicchio, M.C., Rosolini, G. (eds)
    Category Theory. Lecture Notes in Mathematics, vol 1488. Springer,
    Berlin, Heidelberg. https://doi.org/10.1007/BFb0084225

We show that the notion of flabbiness defined in [1] coincides with
ours for types that are sets, or 1-types, in the sense of HoTT/UF.

*Terminological warning.* Sometimes we use, in names of functions, and
in discussions, the word "set" to refer to "subset", to e.g. avoid
awkward names such as "is-subterminal-subset".

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.AlternativeFlabbiness
        (fe : Fun-Ext)
       where

open import InjectiveTypes.Blackboard
open import InjectiveTypes.Structure
open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

\end{code}

The references [1] and [2] work with the following two concepts, in
the internal language of an elementary 1-topos.

(1) A set K : 𝓟 X is *subterminal* if and only if any two elements of
    K are equal.

(2) A set K : 𝓟 X is a *subsingleton* if there is x₀ : X with K ⊆ {x₀}.

In our more general setting of HoTT/UF, which can be considered as an
internal language for ∞-toposes, the singleton {x₀} can be formed if X
is a set, or 1-type, in the sense of HoTT/UF (and if and only if x₀ is
homotopy isolated, meaning that the equality x₀ = x is a proposition
for every x : X).

But K ⊆ {x₀}, in their setting, amounts to the implication
x ∈ K → x ＝ x₀, and so that we can circumvent this obstacle.

(2') A set K : 𝓟 X is a *subsingleton* if there is x₀ : X such that
     x ∈ K implies x ＝ x₀ for all x : X.

In the setting of [1] and [2], conditions (2) and (2') are equivalent,
but only (2') makes sense in our setting for an arbitrary type X,
which is what we adopt below.

However, in any case, we will eventually need to assume that X is a
1-type, as the internal definition of flabbiness given in [1] is
tailored for 1-toposes.

We have that (1) is property if X is a set, and that the above
reformulation (2') of (2) is always property.

To begin with, we will work with the following notion, which is data
rather than property.

(3) *Subsingleton data* for a set K : 𝓟 X consists of a designated point
     x₀ : X such that x ∈ K implies x = x₀ for all x : X.

The difference between (2) and (3) is that in (2) the point x₀ merely
exists, but in (3) it is part of the data.

We begin by formally discussing (1) and (3), leaving (2) for later.

\begin{code}

module _ {X : 𝓤 ̇ } (K : 𝓟 X) where

 subterminal-set : 𝓤 ̇
 subterminal-set = (x y : X) → x ∈ K → y ∈ K → x ＝ y

\end{code}

Notice that the above is strictly speaking data unless X is a set.

\begin{code}

 being-subterminal-set-is-prop
  : is-set X
  → is-prop subterminal-set
 being-subterminal-set-is-prop X-is-set
  = Π₄-is-prop fe (λ _ _ _ _ → X-is-set)

 subsingleton-set-data : 𝓤 ̇
 subsingleton-set-data = Σ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀)

 subsingleton-set-point : subsingleton-set-data → X
 subsingleton-set-point = pr₁

 subsingleton-set-condition : (s : subsingleton-set-data)
                            → (x : X) → x ∈ K → x ＝ subsingleton-set-point s
 subsingleton-set-condition = pr₂

\end{code}

As observed in [1], subsingleton sets are subterminal. We also have
the following, replacing the subsigleton property by subsingleton
data.

\begin{code}

 sets-with-subsingleton-data-are-subterminal
  : subsingleton-set-data
  → subterminal-set
 sets-with-subsingleton-data-are-subterminal (x₀ , ϕ) x y i j
  = x  ＝⟨ ϕ x i ⟩
    x₀ ＝⟨ (ϕ y j)⁻¹ ⟩
    y  ∎

\end{code}

The following is the internal definition of functional flabbiness
proposed in [1], as a converse of the above fact.

We make the converse construction, which isn't always possible, into
an alternative definition of flabby structure. This appears in [1]
under the name "functionally flabby".

\begin{code}

functionally-flabby : 𝓤 ̇ → 𝓤 ⁺ ̇
functionally-flabby X = (K : 𝓟 X)
                      → subterminal-set K
                      → subsingleton-set-data K

\end{code}

The following two observations are not used directly in our
discussion, but may be enlightening. They say that the total space
𝕋 K := Σ x ꞉ X , x ∈ K of the subset K of X is a proposition, assuming
that K is subterminal, and, in particular, that it is equipped with
subsingleton data.

\begin{code}

module _ {X : 𝓤 ̇ } (K : 𝓟 X) where

 subterminals-have-propositional-total-space
  : subterminal-set K
  → is-prop (𝕋 K)
 subterminals-have-propositional-total-space s (x , m) (y , n)
  = to-subtype-＝ (∈-is-prop K) (s x y m n)

 types-with-subsubgleton-data-have-propositional-total-space
  : subsingleton-set-data K
  → is-prop (𝕋 K)
 types-with-subsubgleton-data-have-propositional-total-space s
  = subterminals-have-propositional-total-space
     (sets-with-subsingleton-data-are-subterminal K s)

\end{code}

We define, in an imported module, flabby structure for a type X to be
a map ⨆ : (P : Ω) → (P → X) → X together with equality data ⨆ P f = f p
for every p : P.

We now show that we can construct flabby structure from functional
flabbiness, and conversely.

The first direction requires X to be a 1-type, or set.

\begin{code}

module _ {X : 𝓤 ̇ } where

 functionally-flabby-gives-flabby-structure
  : is-set X
  → functionally-flabby X
  → flabby-structure X 𝓤
 functionally-flabby-gives-flabby-structure X-is-set ϕ = ⨆ , e
  where
   module _ (P : Ω 𝓤) (f : P holds → X) where

    K : 𝓟 X
    K x = fiber f x ,
          maps-of-props-into-sets-are-embeddings f (holds-is-prop P) X-is-set x

    I : subterminal-set K
    I x y (p , d) (q , e) = x   ＝⟨ d ⁻¹ ⟩
                            f p ＝⟨ ap f (holds-is-prop P p q) ⟩
                            f q ＝⟨ e ⟩
                            y   ∎

    II : subsingleton-set-data K
    II = ϕ K I

    ⨆ : X
    ⨆ = subsingleton-set-point K II

    _ : (x : X) → fiber f x → x ＝ ⨆
    _ = subsingleton-set-condition K II

    e : (p : P holds) → ⨆ ＝ f p
    e p = (subsingleton-set-condition K II (f p) (to-fiber f p))⁻¹

\end{code}

The converse doesn't require X to be a 1-type.

\begin{code}

 flabby-structure-gives-functionally-flabby
  : flabby-structure X 𝓤
  → functionally-flabby X
 flabby-structure-gives-functionally-flabby (⨆ , e) K K-subterminal = x₀ , I
  where
   P : Ω 𝓤
   P = (Σ x ꞉ X , x ∈ K) ,
       (λ {(x , m) (y , n) → to-subtype-＝
                              (∈-is-prop K)
                              (K-subterminal x y m n)})

   _ : 𝕋-to-carrier K ＝ (pr₁ ∶ ((Σ x ꞉ X , x ∈ K) → X))
   _ = refl

   x₀ : X
   x₀ = ⨆ P (𝕋-to-carrier K)

   I : (x : X) → x ∈ K → x ＝ x₀
   I x m = (e P (𝕋-to-carrier K) (x , m))⁻¹

\end{code}

The above maps are mutually inverse if X is a set, and hence give a
typal equivalence.

\begin{code}

 functionally-flabby-is-equiv-to-flabby-structure
  : propext 𝓤
  → is-set X
  → functionally-flabby X ≃ flabby-structure X 𝓤
 functionally-flabby-is-equiv-to-flabby-structure pe X-is-set =
  qinveq α (β , η , ε)
  where
   α = functionally-flabby-gives-flabby-structure X-is-set
   β = flabby-structure-gives-functionally-flabby

   η : β ∘ α ∼ id
   η ϕ = dfunext fe (λ K →
         dfunext fe (λ s →
         to-subtype-＝
          (λ x → Π₂-is-prop fe (λ _ _ → X-is-set))
          (III K s)))
    where
     module _ (K : 𝓟 X) (s : subterminal-set K) where

      I : ∀ {K' s'}
        → K' ＝ K
        → subsingleton-set-point K' (ϕ K' s') ＝ subsingleton-set-point K (ϕ K s)
      I {.K} {s'} refl = ap (subsingleton-set-point K ∘ ϕ K)
                            (being-subterminal-set-is-prop K X-is-set s' s)

      K' : 𝓟 X
      K' x = fiber (𝕋-to-carrier K) x , _

      II : K' ＝ K
      II = subset-extensionality'' pe fe fe
            (from-𝕋-fiber K ∶ (K' ⊆ K))
            (to-𝕋-fiber K ∶ (K ⊆ K'))

      III : subsingleton-set-point K' (ϕ K' _) ＝ subsingleton-set-point K (ϕ K s)
      III = I II

   ε : α ∘ β ∼ id
   ε (⨆ , e) = to-subtype-＝
                 (λ _ → Π₃-is-prop fe (λ _ _ _ → X-is-set))
                 (dfunext fe (λ P → dfunext fe (I P)))
    where
     module _ (P : Ω 𝓤) (f : P holds → X) where

      P' : Ω 𝓤
      P' = (Σ x ꞉ X , fiber f x) , _

      I : ⨆ P' pr₁ ＝ ⨆ P f
      I = ⨆-change-of-variable-≃ X pe fe ⨆ pr₁ (total-fiber-is-domain f)

\end{code}

We now discuss the truncated version.

We have already defined the notions (1) and (3) above, and it remains
to define the notion (2), which we call is-subsingleton-set. For that
purpose, we need to assume that propositional truncations exist, so
that we have the existential quantifier ∃ available.

\begin{code}

 module _ (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt
  open injective (λ 𝓤 𝓥 → fe {𝓤} {𝓥}) pt

  module _ (K : 𝓟 X) where

   is-subsingleton-set : 𝓤 ̇
   is-subsingleton-set = ∃ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀)

   being-subsingleton-set-is-prop : is-prop is-subsingleton-set
   being-subsingleton-set-is-prop = ∃-is-prop

\end{code}

As observed in [1], subsingleton sets are subterminal. In our more
general setting, we need to assume that X is a 1-type to reach the
same conclusion.

\begin{code}

   subsingleton-sets-are-subterminal
    : is-set X
    → is-subsingleton-set
    → subterminal-set K
   subsingleton-sets-are-subterminal X-is-set =
    ∥∥-rec
     (being-subterminal-set-is-prop K X-is-set)
     (sets-with-subsingleton-data-are-subterminal K)

\end{code}

And the following is the internal definition of flabbiness proposed in [1],
as a converse of the above fact.

\begin{code}

  flabby' : 𝓤 ⁺ ̇
  flabby' = (K : 𝓟 X)
          → subterminal-set K
          → is-subsingleton-set K

\end{code}

In this repository we have our own internal definition of flabbiness
of a type X, called "flabby", which says that for every propositon P
and function f : P → X, there exists x : X such that x = f p
for all p : P.

We now show that this is equivalent to the definition given in [1],
where the first direction assumes that X is a set.

Notice that this is a logical equivalence, as stated, but also a typal
equivalence, as a consequence, because the two notions of flabbiness
are property, when X is a 1-type, or set.

\begin{code}

  flabby'-gives-flabby : is-set X → flabby' → flabby X 𝓤
  flabby'-gives-flabby X-is-set ϕ P P-is-prop f = IV
   where
    K : 𝓟 X
    K x = fiber f x ,
          maps-of-props-into-sets-are-embeddings f P-is-prop X-is-set x

    I : subterminal-set K
    I x y (p , d) (q , e) = x   ＝⟨ d ⁻¹ ⟩
                            f p ＝⟨ ap f (P-is-prop p q) ⟩
                            f q ＝⟨ e ⟩
                            y   ∎

    II : is-subsingleton-set K
    II = ϕ K I

    III : (Σ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀))
        → (Σ x ꞉ X , ((p : P) → x ＝ f p))
    III (x₀ , α) = x₀ , (λ p → (α (f p) (to-fiber f p))⁻¹)

    IV : ∃ x ꞉ X , ((p : P) → x ＝ f p)
    IV = ∥∥-functor III II

  flabby-gives-flabby' : flabby X 𝓤 → flabby'
  flabby-gives-flabby' ϕ K K-subterminal = II
   where
    P : Ω 𝓤
    P = (Σ x ꞉ X , x ∈ K) ,
        (λ {(x , m) (y , n) → to-subtype-＝
                               (∈-is-prop K)
                               (K-subterminal x y m n)})

    f : P holds → X
    f = pr₁

    I : ∃ x₀ ꞉ X , ((p : P holds) → x₀ ＝ pr₁ p)
    I = ϕ (P holds) (holds-is-prop P) f

    II : ∃ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀)
    II = ∥∥-functor (λ (x₀ , e) → x₀ , (λ x m → (e (x , m))⁻¹)) I

\end{code}

So, at least for sets, this justifies our internal definition of
flabbiness used in this repository. Perhaps an ∞-topos theorist can
chime in and discuss whether our proposed internal definition does
correspond to any external definition of flabbiness discussed in the
∞-topos literature.
