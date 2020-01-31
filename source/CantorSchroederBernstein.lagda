Martin Escardo, 22nd January 2020. (This file needs the Agda release candidate 2.6.1.)

There are two parts, which assume function extensionality but not
univalence or the existence of propositional truncations:


(1) A univalent-foundations version of Pierre Pradic and Chad
    E. Brown's argument that Cantor-Schröder-Bernstein implies
    excluded middle in constructive set theory
    (https://arxiv.org/abs/1904.09193).

    Their proof, reproduced here, uses the compactness (also known as
    the searchability or omniscience) of ℕ∞.


(2) A proof that excluded middle implies Cantor-Schröder-Bernstein for
    all homotopy types, or ∞-groupoids. (Added 24th January.)

    For any pair of types, if each one is embedded into the other,
    then they are equivalent.

    For this it is crucial that a map is an embedding if and only if
    its fibers are all propositions (rather than merely the map being
    left-cancellable).

    As far as we know, (2) is a new result.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CantorSchroederBernstein where

open import SpartanMLTT
open import GenericConvergentSequence
open import DecidableAndDetachable
open import Plus-Properties
open import CompactTypes
open import ConvergentSequenceCompact
open import UF-Subsingletons
open import UF-Equiv
open import UF-Embeddings
open import UF-Retracts
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-ExcludedMiddle

\end{code}

Our formulation of Cantor-Schröder-Bernstein:

\begin{code}

CSB : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
CSB X Y = (X ↪ Y) → (Y ↪ X) → X ≃ Y

CantorSchröderBernstein : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
CantorSchröderBernstein 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → CSB X Y

\end{code}

Part 1
------

The following is Lemma 7 of the above reference, using retractions
rather than surjections, for simplicity:

\begin{code}

Pradic-Brown-lemma : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                   → retract (A + X) of X
                   → Compact X
                   → decidable A
Pradic-Brown-lemma {𝓤} {𝓥} {X} {A} (r , s , η) c = γ e
 where
  P : X → 𝓤 ⊔ 𝓥 ̇
  P x = Σ \(a : A) → r x ≡ inl a

  d : (x : X) → decidable (P x)
  d x = equality-cases (r x)
         (λ (a : A) (u : r x ≡ inl a) → inl (a , u))
         (λ (y : X) (v : r x ≡ inr y) → inr (λ (a , u) → +disjoint (inl a ≡⟨ u ⁻¹ ⟩
                                                                    r x   ≡⟨ v    ⟩
                                                                    inr y ∎)))

  e : decidable (Σ \(x : X) → P x)
  e = c P d

  f : A → Σ \(x : X) → P x
  f a = s (inl a) , a , η (inl a)

  γ : decidable (Σ \(x : X) → P x) → decidable A
  γ (inl (x , a , u)) = inl a
  γ (inr φ)           = inr (contrapositive f φ)

\end{code}

Function extensionality is used twice in the following, once to know
that ℕ∞ is a set, and once to know that it is compact.

\begin{code}

CSB-gives-EM : funext 𝓤₀ 𝓤₀
             → (P : 𝓤 ̇ )
             → is-prop P
             → CSB ℕ∞ (P + ℕ∞)
             → P + ¬ P
CSB-gives-EM fe P i csb = γ
 where
  f : ℕ∞ → P + ℕ∞
  f = inr

  j : is-embedding f
  j = inr-is-embedding P ℕ∞

  z : P → ℕ∞
  z _ = Zero

  g : P + ℕ∞ → ℕ∞
  g = cases z Succ

  a : is-embedding z
  a = maps-of-props-into-sets-are-embeddings (λ p → Zero) i (ℕ∞-is-set fe)

  b : is-embedding Succ
  b = lc-maps-into-sets-are-embeddings Succ Succ-lc (ℕ∞-is-set fe)

  c : disjoint-images z Succ
  c = λ (p : P) (x : ℕ∞) (q : Zero ≡ Succ x) → Zero-not-Succ q

  k : is-embedding g
  k = disjoint-cases-embedding z Succ a b c

  e : ℕ∞ ≃ P + ℕ∞
  e = csb (f , j) (g , k)

  ρ : retract (P + ℕ∞) of ℕ∞
  ρ = equiv-retract-r e

  γ : P + ¬ P
  γ = Pradic-Brown-lemma ρ (ℕ∞-Compact fe)

\end{code}

Hence if we assume Cantor-Schröder-Bernstein for the first universe 𝓤₀
and an arbitrary universe 𝓥, as formulated above, then we get excluded
middle for propositions in the universe 𝓥:

\begin{code}

CantorSchröderBernstein-gives-EM : funext 𝓤₀ 𝓤₀
                                 → CantorSchröderBernstein 𝓤₀ 𝓥
                                 → EM 𝓥
CantorSchröderBernstein-gives-EM fe csb P i = CSB-gives-EM fe P i (csb ℕ∞ (P + ℕ∞))

\end{code}

Remark. If instead of requiring that we have a designated equivalence,
we required that there is an unspecified equivalence in the
formulation of Cantor-Schröder-Bernstein, we would still get excluded
middle, because P + ¬ P is a proposition.


Part 2
------

The Cantor-Schröder-Bernstein Theorem holds for all homotopy types, or
∞-gropoids, in the presence of excluded middle. It is crucial here
that embeddings have subsingleton fibers, so that e.g. the function
is-g-point defined in the proof is property rather than data and hence
we can apply univalent excluded middle to it. It is also worth
remembering, for the sake of comparing the classical result for sets
with its generalization to ∞-groupoids, that a map of types that are
sets is an embedding if and only if it is left-cancellable.


Our proof adapts Wikipedia's "alternate proof" (consulted 23rd January 2020)

  https://en.wikipedia.org/wiki/Schr%C3%B6der%E2%80%93Bernstein_theorem#Alternate_proof

to our more general situation.


For foundational reasons, we make clear which instances of function
extensionality and excluded middle are needed to conclude
Cantor-Schröder-Bernstein for arbitrary universes 𝓤 and 𝓥.

Added 28th January. To better understand this proof, you may consult the blog
post

    https://homotopytypetheory.org/2020/01/26/the-cantor-schroder-bernstein-theorem-for-%e2%88%9e-groupoids/

first. However, we try to make the proof understandable as we can
here, and hopefully it should be possible to read it without reference
to the blog post.

\begin{code}

EM-gives-CantorSchröderBernstein : funext 𝓤 (𝓤 ⊔ 𝓥)
                                 → funext (𝓤 ⊔ 𝓥) 𝓤₀
                                 → funext 𝓤₀ (𝓤 ⊔ 𝓥)
                                 → EM (𝓤 ⊔ 𝓥)
                                 → CantorSchröderBernstein 𝓤 𝓥
EM-gives-CantorSchröderBernstein {𝓤} {𝓥} fe fe₀ fe₁ excluded-middle X Y (f , f-is-emb) (g , g-is-emb) =

  need (X ≃ Y) which-is-given-by 𝒽

 where

  remark-f : type-of f ≡ (X → Y)
  remark-f = by-assumption

  remark-g : type-of g ≡ (Y → X)
  remark-g = by-assumption

\end{code}

In order to define 𝒽 : X ≃ Y, we use a notion of g-point.

\begin{code}

  is-g-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  is-g-point x = (x₀ : X) (n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x → fiber g x₀

\end{code}

What is important for our purposes is that this is property rather
than data, using the fact that g is an embedding, which means that its
fibers are all propositions.

\begin{code}

  recall : (x : X) → fiber g x ≡ Σ \(y : Y) → g y ≡ x
  recall _ = by-definition

  also-recall : is-embedding g ≡ ((x : X) → is-prop (fiber g x))
  also-recall = by-definition

\end{code}

We use the fact that propositions are closed under products, which
requires function extensionality:

\begin{code}

  being-g-point-is-a-prop : (x : X) → is-prop (is-g-point x)
  being-g-point-is-a-prop x =
   Π-is-prop fe  (λ (x₀ : X                   ) →
   Π-is-prop fe₁ (λ (n  : ℕ                   ) →
   Π-is-prop fe  (λ (p  : ((g ∘ f) ^ n) x₀ ≡ x) → need (is-prop (fiber g x₀))
                                                  which-is-given-by (g-is-emb x₀))))
\end{code}

We collect the g-points in a subtype of X.

\begin{code}

  G-point : 𝓤 ⊔ 𝓥 ̇
  G-point = Σ \(x : X) → is-g-point x

\end{code}

By construction, considering x₀ = x and n = 0, we have that g is
invertible at g-points, because, by definition, we have that
((g ∘ f) ^ 0) x ≡ x).

\begin{code}

  g-is-invertible-at-g-points : ((x , γ) : G-point) → fiber g x
  g-is-invertible-at-g-points (x , γ) = γ x 0 (by-definition ∶ ((g ∘ f) ^ 0) x ≡ x)

\end{code}

The fiber point is given by the first projection of the fiber:

\begin{code}

  g⁻¹ : G-point → Y
  g⁻¹ (x , γ) = fiber-point g x (g-is-invertible-at-g-points (x , γ))

\end{code}

Because being a g-point is property, we can apply excluded middle to
it:

\begin{code}

  recall-the-notion-of-decidability : {𝓦 : Universe} {A : 𝓦 ̇ } → decidable A ≡ (A + ¬ A)
  recall-the-notion-of-decidability = by-definition

  δ : (x : X) → decidable (is-g-point x)
  δ x = excluded-middle (is-g-point x) (being-g-point-is-a-prop x)

\end{code}

The rest of the proof consists in showing that the following function
is an equivalence:

\begin{code}

  h : X → Y
  h x = Cases (δ x)
        (λ (γ :   is-g-point x) → g⁻¹ (x , γ))
        (λ (ν : ¬ is-g-point x) → f x)

\end{code}

For that purpose, it is enough to show that it is left-cancellable and
split-surjective.

To show that it is left-cancellable, we first show that g⁻¹ is a
two-sided inverse in its domain of definition.

That it is a right inverse follows from the definition of fiber, by
taking the fiber path, which is given by the second projection:

\begin{code}

  g⁻¹-is-rinv : ((x , γ) : G-point) → g (g⁻¹ (x , γ)) ≡ x
  g⁻¹-is-rinv (x , γ) = fiber-path g x (g-is-invertible-at-g-points (x , γ))

\end{code}

That it is a left inverse follows from the above and the fact that g,
being an embedding, is left-cancellable:

\begin{code}

  g⁻¹-is-linv : (y : Y) (γ : is-g-point (g y)) → g⁻¹ (g y , γ) ≡ y
  g⁻¹-is-linv y γ = have (g (g⁻¹ (g y , γ)) ≡⟨ g⁻¹-is-rinv (g y , γ) ⟩
                          g y               ∎)
                    so-apply embeddings-are-left-cancellable g g-is-emb

\end{code}

We also need the following two facts to establish the
left-cancellability of h:

\begin{code}

  α : (x : X) → is-g-point (g (f x)) → is-g-point x
  α x γ = need is-g-point x
          which-is-given-by
           assume x₀ ∶ X                    then
           assume n  ∶ ℕ                    then
           assume p  ∶ ((g ∘ f) ^ n) x₀ ≡ x then
            (need fiber g x₀
             which-is-given-by
               have ap (g ∘ f) p ∶ ((g ∘ f) ^ (succ n)) x₀ ≡ g (f x)
               so-apply γ x₀ (succ n))

  f-g⁻¹-disjoint-images : (x : X) → ¬ is-g-point x → ((x' , γ) : G-point) → f x ≢ g⁻¹ (x' , γ)
  f-g⁻¹-disjoint-images x ν (x' , γ) p = have p ∶ f x ≡ g⁻¹ (x' , γ)
                                         so need contradiction
                                            which-is-given-by
                                             have γ ∶ is-g-point x'
                                             which-is-impossible-by (v ∶ ¬ is-g-point x')
   where
    q : g (f x) ≡ x'
    q = have p ∶ f x ≡ g⁻¹ (x' , γ)
        so-use (g (f x)          ≡⟨ ap g p                ⟩
                g (g⁻¹ (x' , γ)) ≡⟨ g⁻¹-is-rinv (x' , γ)  ⟩
                x'               ∎)
    u : ¬ is-g-point (g (f x))
    u = have ν ∶ ¬ is-g-point x
        so-apply contrapositive (α x)
    v : ¬ is-g-point x'
    v = transport (λ - → ¬ is-g-point -) q u

\end{code}

It is convenient to work with the following auxiliary function H and
prove properties of H and then specialize them to h:

\begin{code}

  H : (x : X) → decidable (is-g-point x) → Y
  H x d = Cases d
           (λ (γ :   is-g-point x) → g⁻¹ (x , γ))
           (λ (ν : ¬ is-g-point x) → f x)

  notice-that : h ≡ λ x → H x (δ x)
  notice-that = by-definition

  h-lc : left-cancellable h
  h-lc {x} {x'} = l (δ x) (δ x')
   where
    l : (d : decidable (is-g-point x)) (d' : decidable (is-g-point x')) → H x d ≡ H x' d' → x ≡ x'

    l (inl γ) (inl γ') p = have p ∶ g⁻¹ (x , γ) ≡ g⁻¹ (x' , γ')
                           so (x                 ≡⟨ (g⁻¹-is-rinv (x , γ))⁻¹ ⟩
                               g (g⁻¹ (x  , γ )) ≡⟨ ap g p                  ⟩
                               g (g⁻¹ (x' , γ')) ≡⟨ g⁻¹-is-rinv (x' , γ')   ⟩
                               x'                ∎)

    l (inl γ) (inr ν') p = have p ∶ g⁻¹ (x , γ) ≡ f x'
                           which-is-impossible-by λ - → f-g⁻¹-disjoint-images x' ν' (x , γ) (- ⁻¹)

    l (inr ν) (inl γ') p = have p ∶ f x ≡ g⁻¹ (x' , γ')
                           which-is-impossible-by f-g⁻¹-disjoint-images x ν (x' , γ')

    l (inr ν) (inr ν') p = have p ∶ f x ≡ f x'
                           so-apply embeddings-are-left-cancellable f f-is-emb

\end{code}

Next we want to show that h is split surjective. For that purpose, we
define the notion of f-point, which is data rather than property (as
several x₀ and n are possible answers in general).

(In particular, excluded middle can't be applied to the type
f-point x, because excluded middle applies only to truth values.)

\begin{code}

  f-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  f-point x = Σ \(x₀ : X) → (Σ \(n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x) × ¬ fiber g x₀

\end{code}

What is important for our argument is that non-f-points are g-points:

\begin{code}

  non-f-point-is-g-point : (x : X) → ¬ f-point x → is-g-point x
  non-f-point-is-g-point x ν x₀ n p = need (fiber g x₀) which-is-given-by
    (Cases (excluded-middle (fiber g x₀) (g-is-emb x₀))
      (λ (σ :   fiber g x₀) → σ)
      (λ (u : ¬ fiber g x₀) → have (x₀ , (n , p) , u) ∶ f-point x
                              which-is-impossible-by (ν ∶ ¬ f-point x)))

\end{code}

We use the notion of f-point to prove the following, whose statement
doesn't refer to the notion of f-point.

\begin{code}

  claim : (y : Y) → ¬ is-g-point (g y) → Σ \((x , p) : fiber f y) → ¬ is-g-point x
  claim y ν = v
   where
    i : ¬¬ f-point (g y)
    i = have ν ∶ ¬ is-g-point (g y)
        so-apply contrapositive (non-f-point-is-g-point (g y))

    ii : f-point (g y) → Σ \((x , p) : fiber f y) → ¬ is-g-point x
    ii (x₀ , (0 , p) , u) = have p ∶ x₀ ≡ g y
                            so have (y , (p ⁻¹)) ∶ fiber g x₀
                               which-is-impossible-by (u ∶ ¬ fiber g x₀)
    ii (x₀ , (succ n , p) , u) = a , b
     where
      q : f (((g ∘ f) ^ n) x₀) ≡ y
      q = have p ∶ ((g ∘ f) ^ (succ n)) x₀  ≡ g y
                 ∶ g (f (((g ∘ f) ^ n) x₀)) ≡ g y
          so-apply embeddings-are-left-cancellable g g-is-emb
      a : fiber f y
      a = ((g ∘ f) ^ n) x₀ , q
      b : ¬ is-g-point (((g ∘ f) ^ n) x₀)
      b = assume γ ∶ is-g-point (((g ∘ f) ^ n) x₀)
          then (have γ x₀ n refl ∶ fiber g x₀
                which-is-impossible-by (u ∶ ¬ fiber g x₀))

    iii : ¬¬ Σ \((x , p) : fiber f y) → ¬ is-g-point x
    iii = double-contrapositive ii i

    iv : is-prop (Σ \((x , p) : fiber f y) → ¬ is-g-point x)
    iv = have f-is-emb y ∶ is-prop (fiber f y)
         so-apply subtype-of-prop-is-a-prop pr₁ (pr₁-lc (λ {σ} → negations-are-props fe₀))

    v : Σ \((x , p) : fiber f y) → ¬ is-g-point x
    v = double-negation-elimination excluded-middle _ iv iii

\end{code}

With this we are ready to show that h is a split surjection. The idea
is that, given y : Y, we check whether g y is a g-point or not, and if
it is we map it to g y, and otherwise we map y to the point x : X
given by the above claim. But then, of course, we also need to argue
that this works. As above, we use the auxiliary function H for that
purpose.

\begin{code}

  h-split-surjection : (y : Y) → Σ \(x : X) → h x ≡ y
  h-split-surjection y = x , p
   where
    a : decidable (is-g-point (g y)) → Σ \(x : X) → (d : decidable (is-g-point x)) → H x d ≡ y
    a (inl γ) = g y , ψ
     where
      ψ : (d : decidable (is-g-point (g y))) → H (g y) d ≡ y
      ψ (inl γ') = H (g y) (inl γ') ≡⟨ by-definition    ⟩
                   g⁻¹ (g y , γ')   ≡⟨ g⁻¹-is-linv y γ' ⟩
                   y                ∎
      ψ (inr ν)  = have ν ∶ ¬ is-g-point (g y)
                   which-contradicts (γ ∶ is-g-point (g y))
    a (inr ν) = x , ψ
     where
      w : Σ \((x , p) : fiber f y) → ¬ is-g-point x
      w = have ν ∶ ¬ is-g-point (g y)
          so-apply claim y
      x : X
      x = fiber-point f y (pr₁ w)
      p : f x ≡ y
      p = fiber-path f y (pr₁ w)
      ψ : (d : decidable (is-g-point x)) → H x d ≡ y
      ψ (inl γ) = have γ ∶ is-g-point x
                  which-is-impossible-by (pr₂ w ∶ ¬ is-g-point x)
      ψ (inr ν) = H x (inr ν) ≡⟨ by-definition ⟩
                  f x         ≡⟨ p             ⟩
                  y           ∎
    b : Σ \(x : X) → (d : decidable (is-g-point x)) → H x d ≡ y
    b = a (δ (g y))
    x : X
    x = pr₁ b
    p : h x ≡ y
    p = pr₂ b (δ x)

\end{code}

And because left-cancellable split surjections are equivalences, we
are done:

\begin{code}

  𝒽 : X ≃ Y
  𝒽 = h , lc-split-surjections-are-equivs h h-lc h-split-surjection

\end{code}

We record the following special case:

\begin{code}

EM-gives-CantorSchröderBernstein₀ : funext 𝓤₀ 𝓤₀
                                  → EM 𝓤₀
                                  → CantorSchröderBernstein 𝓤₀ 𝓤₀
EM-gives-CantorSchröderBernstein₀ fe = EM-gives-CantorSchröderBernstein fe fe fe

\end{code}


APPENDIX
--------

The above is an attempt to make the proof more readable and match the
blog post. Here is a more concise version of the above in a more
direct Agda style which some will prefer (and which could be made even
more concise by avoiding auxiliary definitions used for the purpose of
indicating types explicitly).

\begin{code}

EM-gives-CantorSchröderBernstein' : funext 𝓤 (𝓤 ⊔ 𝓥)
                                  → funext (𝓤 ⊔ 𝓥) 𝓤₀
                                  → funext 𝓤₀ (𝓤 ⊔ 𝓥)
                                  → EM (𝓤 ⊔ 𝓥)
                                  → CantorSchröderBernstein 𝓤 𝓥
EM-gives-CantorSchröderBernstein' {𝓤} {𝓥} fe fe₀ fe₁ excluded-middle X Y (f , f-is-emb) (g , g-is-emb) = 𝒽
 where
  is-g-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  is-g-point x = (x₀ : X) (n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x → fiber g x₀

  G-point : 𝓤 ⊔ 𝓥 ̇
  G-point = Σ \(x : X) → is-g-point x

  g-is-invertible-at-g-points : ((x , γ) : G-point) → fiber g x
  g-is-invertible-at-g-points (x , γ) = γ x 0 refl

  g⁻¹ : G-point → Y
  g⁻¹ (x , γ) = fiber-point g x (g-is-invertible-at-g-points (x , γ))

  g⁻¹-is-rinv : ((x , γ) : G-point) → g (g⁻¹ (x , γ)) ≡ x
  g⁻¹-is-rinv (x , γ) = fiber-path g x (g-is-invertible-at-g-points (x , γ))

  g⁻¹-is-linv : (y : Y) (γ : is-g-point (g y)) → g⁻¹ (g y , γ) ≡ y
  g⁻¹-is-linv y γ = embeddings-are-left-cancellable g g-is-emb (g⁻¹-is-rinv (g y , γ))

  α : (x : X) → is-g-point (g (f x)) → is-g-point x
  α x γ x₀ n p = γ x₀ (succ n) (ap (g ∘ f) p)

  f-g⁻¹-disjoint-images : (x : X) → ¬ is-g-point x → ((x' , γ) : G-point) → f x ≢ g⁻¹ (x' , γ)
  f-g⁻¹-disjoint-images x ν (x' , γ) p = 𝟘-elim (v γ)
   where
    q = g (f x)          ≡⟨ ap g p                ⟩
        g (g⁻¹ (x' , γ)) ≡⟨ g⁻¹-is-rinv (x' , γ)  ⟩
        x'               ∎
    u : ¬ is-g-point (g (f x))
    u = contrapositive (α x) ν
    v : ¬ is-g-point x'
    v = transport (λ - → ¬ is-g-point -) q u

  being-g-point-is-a-prop : (x : X) → is-prop (is-g-point x)
  being-g-point-is-a-prop x = Π-is-prop fe (λ x₀ → Π-is-prop fe₁ (λ _ → Π-is-prop fe (λ _ → g-is-emb x₀)))

  δ : (x : X) → decidable (is-g-point x)
  δ x = excluded-middle (is-g-point x) (being-g-point-is-a-prop x)

  H : (x : X) → decidable (is-g-point x) → Y
  H x (inl γ) = g⁻¹ (x , γ)
  H x (inr _) = f x

  h : X → Y
  h x = H x (δ x)

  h-lc : left-cancellable h
  h-lc {x} {x'} = l (δ x) (δ x')
   where
    l : (d : decidable (is-g-point x)) (d' : decidable (is-g-point x')) → H x d ≡ H x' d' → x ≡ x'
    l (inl γ) (inl γ') p = x                 ≡⟨ (g⁻¹-is-rinv (x , γ))⁻¹ ⟩
                           g (g⁻¹ (x  , γ )) ≡⟨ ap g p                  ⟩
                           g (g⁻¹ (x' , γ')) ≡⟨ g⁻¹-is-rinv (x' , γ')   ⟩
                           x'                ∎
    l (inl γ) (inr ν') p = 𝟘-elim(f-g⁻¹-disjoint-images x' ν' (x  , γ )(p ⁻¹))
    l (inr ν) (inl γ') p = 𝟘-elim(f-g⁻¹-disjoint-images x  ν  (x' , γ') p)
    l (inr ν) (inr ν') p = embeddings-are-left-cancellable f f-is-emb p

  f-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  f-point x = Σ \(x₀ : X) → (Σ \(n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x) × ¬ fiber g x₀

  non-f-point-is-g-point : (x : X) → ¬ f-point x → is-g-point x
  non-f-point-is-g-point x ν x₀ n p =
   Cases (excluded-middle (fiber g x₀) (g-is-emb x₀))
    (λ (σ :   fiber g x₀) → σ)
    (λ (u : ¬ fiber g x₀) → 𝟘-elim(ν (x₀ , (n , p) , u)))

  claim : (y : Y) → ¬ is-g-point (g y) → Σ \((x , p) : fiber f y) → ¬ is-g-point x
  claim y ν = v
   where
   i : ¬¬ f-point (g y)
   i = contrapositive (non-f-point-is-g-point (g y)) ν

   ii : f-point (g y) → Σ \((x , p) : fiber f y) → ¬ is-g-point x
   ii (x₀ , (0      , p) , u) = 𝟘-elim (u (y , (p ⁻¹)))
   ii (x₀ , (succ n , p) , u) = a , b
    where
     q : f (((g ∘ f) ^ n) x₀) ≡ y
     q = embeddings-are-left-cancellable g g-is-emb p
     a : fiber f y
     a = ((g ∘ f) ^ n) x₀ , q
     b : ¬ is-g-point (((g ∘ f) ^ n) x₀)
     b γ = 𝟘-elim (u (γ x₀ n refl))

   iii : ¬¬ Σ \((x , p) : fiber f y) → ¬ is-g-point x
   iii = double-contrapositive ii i

   iv : is-prop (Σ \((x , p) : fiber f y) → ¬ is-g-point x)
   iv = subtype-of-prop-is-a-prop pr₁ (pr₁-lc (λ {σ} → negations-are-props fe₀)) (f-is-emb y)

   v : Σ \((x , p) : fiber f y) → ¬ is-g-point x
   v = double-negation-elimination excluded-middle _ iv iii

  h-split-surjection : (y : Y) → Σ \(x : X) → h x ≡ y
  h-split-surjection y = x , p
   where
    a : decidable (is-g-point (g y)) → Σ \(x : X) → (d : decidable (is-g-point x)) → H x d ≡ y
    a (inl γ) = g y , ψ
     where
      ψ : (d : decidable (is-g-point (g y))) → H (g y) d ≡ y
      ψ (inl γ') = g⁻¹-is-linv y γ'
      ψ (inr ν)  = 𝟘-elim (ν γ)
    a (inr ν) = x , ψ
     where
      w : Σ \((x , p) : fiber f y) → ¬ is-g-point x
      w = claim y ν
      x : X
      x = fiber-point f y (pr₁ w)
      ψ : (d : decidable (is-g-point x)) → H x d ≡ y
      ψ (inl γ) = 𝟘-elim (pr₂ w γ)
      ψ (inr ν) = fiber-path f y (pr₁ w)

    b : Σ \(x : X) → (d : decidable (is-g-point x)) → H x d ≡ y
    b = a (δ (g y))
    x : X
    x = pr₁ b
    p : h x ≡ y
    p = pr₂ b (δ x)

  𝒽 : X ≃ Y
  𝒽 = h , lc-split-surjections-are-equivs h h-lc h-split-surjection

\end{code}

Check our lecture notes https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/
if you want to learn HoTT/UF and Agda.
