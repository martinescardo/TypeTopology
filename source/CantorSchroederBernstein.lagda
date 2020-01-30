Martin Escardo, 22nd January 2020

This file has two parts, which assume function extensionality but not
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

NB. This file needs the Agda release candidate 2.6.1.

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
CantorSchröderBernstein 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → CSB X Y

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
CantorSchröderBernstein-gives-EM fe csb P i = CSB-gives-EM fe P i csb

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

\begin{code}

EM-gives-CantorSchröderBernstein : funext 𝓤 (𝓤 ⊔ 𝓥)
                                 → funext (𝓤 ⊔ 𝓥) 𝓤₀
                                 → funext 𝓤₀ (𝓤 ⊔ 𝓥)
                                 → EM (𝓤 ⊔ 𝓥)
                                 → CantorSchröderBernstein 𝓤 𝓥
EM-gives-CantorSchröderBernstein {𝓤} {𝓥} fe fe₀ fe₁ em {X} {Y} (f , f-is-emb) (g , g-is-emb) = 𝓱
 where
  is-g-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  is-g-point x = (x₀ : X) (n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x → fiber g x₀

  g-is-invertible-at-g-points : (x : X) → is-g-point x → fiber g x
  g-is-invertible-at-g-points x γ = γ x 0 refl

  g⁻¹ : (x : X) → is-g-point x → Y
  g⁻¹ x γ = fiber-point g x (g-is-invertible-at-g-points x γ)

  g⁻¹-is-rinv : (x : X) (γ : is-g-point x) → g (g⁻¹ x γ) ≡ x
  g⁻¹-is-rinv x γ = fiber-path g x (g-is-invertible-at-g-points x γ)

  g⁻¹-is-linv : (y : Y) (γ : is-g-point (g y)) → g⁻¹ (g y) γ ≡ y
  g⁻¹-is-linv y γ = apply (embedding-lc g g-is-emb)
                    to (g⁻¹-is-rinv (g y) γ ∶ g (g⁻¹ (g y) γ) ≡ g y)

  being-g-point-is-a-prop : (x : X) → is-prop (is-g-point x)
  being-g-point-is-a-prop x = Π-is-prop fe  (λ (x₀ : X                   ) →
                              Π-is-prop fe₁ (λ (n  : ℕ                   ) →
                              Π-is-prop fe  (λ (p  : ((g ∘ f) ^ n) x₀ ≡ x) → g-is-emb x₀)))

  δ : (x : X) → decidable (is-g-point x)
  δ x = em (is-g-point x) (being-g-point-is-a-prop x)

  H : (x : X) → decidable (is-g-point x) → Y
  H x d = Cases d
           (λ (γ :   is-g-point x) → g⁻¹ x γ)
           (λ (ν : ¬ is-g-point x) → f x)

  h : X → Y
  h x = H x (δ x)

  α : (x : X) → is-g-point (g (f x)) → is-g-point x
  α x γ x₀ n p = γ x₀ (succ n) (ap (g ∘ f) p)

  f-g⁻¹-disjoint-images : (x x' : X) → ¬ is-g-point x → (γ : is-g-point x') → f x ≢ g⁻¹ x' γ
  f-g⁻¹-disjoint-images x x' ν γ p = have (v ∶ ¬ is-g-point x')
                                     which-contradicts γ
   where
    u : ¬ is-g-point (g (f x))
    u = contrapositive (α x) ν
    q : g (f x) ≡ x'
    q = have (p ∶ f x ≡ g⁻¹ x' γ)
        so-use (g (f x)      ≡⟨ ap g p            ⟩
                g (g⁻¹ x' γ) ≡⟨ g⁻¹-is-rinv x' γ  ⟩
                x'           ∎)
    v : ¬ is-g-point x'
    v = transport (λ - → ¬ is-g-point -) q u

  h-lc : left-cancellable h
  h-lc {x} {x'} = l (δ x) (δ x')
   where
    l : (d : decidable (is-g-point x)) (d' : decidable (is-g-point x'))
      → H x d ≡ H x' d' → x ≡ x'

    l (inl γ) (inl γ') p = have (p ∶ g⁻¹ x γ ≡ g⁻¹ x' γ')
                           so (x             ≡⟨ (g⁻¹-is-rinv x γ)⁻¹ ⟩
                               g (g⁻¹ x γ)   ≡⟨ ap g p              ⟩
                               g (g⁻¹ x' γ') ≡⟨ g⁻¹-is-rinv x' γ'   ⟩
                               x'            ∎)

    l (inl γ) (inr ν') p = have (p ∶ g⁻¹ x γ ≡ f x')
                           which-is-impossible-by (λ - → f-g⁻¹-disjoint-images x' x ν' γ (- ⁻¹))

    l (inr ν) (inl γ') p = have (p ∶ f x ≡ g⁻¹ x' γ')
                           which-is-impossible-by (f-g⁻¹-disjoint-images x x' ν γ')

    l (inr ν) (inr ν') p = have (p ∶ f x ≡ f x')
                           so (embedding-lc f f-is-emb p ∶ x ≡ x')

  f-point : (x : X) → 𝓤 ⊔ 𝓥 ̇
  f-point x = Σ \(x₀ : X) → (Σ \(n : ℕ) → ((g ∘ f) ^ n) x₀ ≡ x) × ¬ fiber g x₀

  non-f-point-is-g-point : (x : X) → ¬ f-point x → is-g-point x
  non-f-point-is-g-point x ν x₀ n p = Cases (em (fiber g x₀) (g-is-emb x₀))
                                       (λ (σ :   fiber g x₀) → σ)
                                       (λ (u : ¬ fiber g x₀) → have ((x₀ , (n , p) , u) ∶ f-point x)
                                                               which-is-impossible-by (ν ∶ ¬ f-point x))

  claim : (y : Y) → ¬ is-g-point (g y) → Σ \((x , p) : fiber f y) → ¬ is-g-point x
  claim y u = v
   where
   i : ¬¬ f-point (g y)
   i = contrapositive (non-f-point-is-g-point (g y)) u

   ii : f-point (g y) → Σ \((x , p) : fiber f y) → ¬ is-g-point x
   ii (x₀ , (0 , p) , ν) = have (p ∶ x₀ ≡ g y) which-is-impossible-by a
    where
     a : x₀ ≢ g y
     a = assume p ∶ x₀ ≡ g y
         then (have ((y , (p ⁻¹)) ∶ fiber g x₀)
               which-is-impossible-by (ν ∶ ¬ fiber g x₀))
   ii (x₀ , (succ n , p) , ν) = a , b
    where
     q : f (((g ∘ f) ^ n) x₀) ≡ y
     q = have (p ∶ ((g ∘ f) ^ (succ n)) x₀ ≡ g y
                 ∶ g (f (((g ∘ f) ^ n) x₀)) ≡ g y)
         so-use (embedding-lc g g-is-emb p)
     a : fiber f y
     a = ((g ∘ f) ^ n) x₀ , q
     b : ¬ is-g-point (((g ∘ f) ^ n) x₀)
     b = assume γ ∶ is-g-point (((g ∘ f) ^ n) x₀)
         then (have (γ x₀ n refl ∶ fiber g x₀)
               which-is-impossible-by (ν ∶ ¬ fiber g x₀))

   iii : ¬¬ Σ \((x , p) : fiber f y) → ¬ is-g-point x
   iii = ¬¬-functor ii i

   iv : is-prop (Σ \((x , p) : fiber f y) → ¬ is-g-point x)
   iv = subtype-of-prop-is-a-prop pr₁ (pr₁-lc (λ {σ} → negations-are-props fe₀)) (f-is-emb y)

   v : Σ \((x , p) : fiber f y) → ¬ is-g-point x
   v = EM-gives-DNE em _ iv iii

  h-split-surjection : (y : Y) → Σ \(x : X) → h x ≡ y
  h-split-surjection y = x , p
   where
    a : decidable (is-g-point (g y)) → Σ \(x : X) → (d : decidable (is-g-point x)) → H x d ≡ y
    a (inl γ) = g y , ψ
     where
      ψ : (d : decidable (is-g-point (g y))) → H (g y) d ≡ y
      ψ (inl γ') = H (g y) (inl γ') ≡⟨ refl             ⟩
                   g⁻¹ (g y) γ'     ≡⟨ g⁻¹-is-linv y γ' ⟩
                   y                ∎
      ψ (inr ν)  = have (ν ∶ ¬ is-g-point (g y))
                   which-contradicts (γ ∶ is-g-point (g y))
    a (inr ν) = x , ψ
     where
      w : Σ \((x , p) : fiber f y) → ¬ is-g-point x
      w = apply (claim y) to (ν ∶ ¬ is-g-point (g y))
      x : X
      x = fiber-point f y (pr₁ w)
      p : f x ≡ y
      p = fiber-path f y (pr₁ w)
      ψ : (d : decidable (is-g-point x)) → H x d ≡ y
      ψ (inl γ) = have (γ ∶ is-g-point x)
                  which-is-impossible-by (pr₂ w ∶ ¬ is-g-point x)
      ψ (inr ν) = H x (inr ν) ≡⟨ refl ⟩
                  f x         ≡⟨ p    ⟩
                  y           ∎
    b : Σ \(x : X) → (d : decidable (is-g-point x)) → H x d ≡ y
    b = a (δ (g y))
    x : X
    x = pr₁ b
    p : h x ≡ y
    p = pr₂ b (δ x)

  𝓱 : X ≃ Y
  𝓱 = h , lc-split-surjections-are-equivs h h-lc h-split-surjection


EM-gives-CantorSchröderBernstein₀ : funext 𝓤₀ 𝓤₀
                                  → EM 𝓤₀
                                  → CantorSchröderBernstein 𝓤₀ 𝓤₀
EM-gives-CantorSchröderBernstein₀ fe = EM-gives-CantorSchröderBernstein fe fe fe

\end{code}

Added 28th January. A blog post with more information in the comments
is available here:

   https://homotopytypetheory.org/2020/01/26/the-cantor-schroder-bernstein-theorem-for-%e2%88%9e-groupoids/
