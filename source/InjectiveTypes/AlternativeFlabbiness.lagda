Martin Escardo, 23 June 2025.

The following paper has a notion of flabbiness in the internal
language of a 1-topos.

[1] Ingo Blechschmidt (2018). Flabby and injective objects in toposes.
    https://arxiv.org/abs/1810.12708

This definition of flabbiness uses the two notions of "subterminal"
and "subsingleton" subsets, as defined in e.g.

[2] Kock, A. (1991). Algebras for the partial map classifier
    monad. In: Carboni, A., Pedicchio, M.C., Rosolini, G. (eds)
    Category Theory. Lecture Notes in Mathematics, vol 1488. Springer,
    Berlin, Heidelberg. https://doi.org/10.1007/BFb0084225

We show that the notion of flabbiness defined in [1] coincides with
ours for types that are sets in the sense of HoTT/UF.

*Terminological warning.* Sometimes we use, in names of functions, the
word "set" to refer to "subset", to e.g. avoid awkward names such as
"is-subterminal-subset".

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module InjectiveTypes.AlternativeFlabbiness
        (fe : Fun-Ext)
       where

open import InjectiveTypes.Structure
open import InjectiveTypes.Blackboard
open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module _ {X : 𝓤 ̇ } (K : 𝓟 X) where

 is-subterminal-set : 𝓤 ̇
 is-subterminal-set = (x y : X) → x ∈ K → y ∈ K → x ＝ y

 being-subterminal-set-is-prop
  : is-set X
  → is-prop is-subterminal-set
 being-subterminal-set-is-prop X-is-set
  = Π₄-is-prop fe (λ _ _ _ _ → X-is-set)

 subsingleton-set-structure : 𝓤 ̇
 subsingleton-set-structure = Σ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀)

 sets-with-subsingleton-structure-are-subterminal
  : subsingleton-set-structure
  → is-subterminal-set
 sets-with-subsingleton-structure-are-subterminal (x₀ , ϕ) x y i j
  = ϕ x i ∙ (ϕ y j)⁻¹

\end{code}

In the above reference [1], we find the alternative definition flabby'
of flabbiness given below. We first consider a "proof relevant"
counterpart.

\begin{code}

aflabby' : 𝓤 ̇ → 𝓤 ⁺ ̇
aflabby' X = (K : 𝓟 X)
           → is-subterminal-set K
           → subsingleton-set-structure K

\end{code}

The following two definitions are not used.

\begin{code}

module _ {X : 𝓤 ̇ } (K : 𝓟 X) where

 subterminals-have-propositional-total-space
  : is-subterminal-set K
  → is-prop (𝕋 K)
 subterminals-have-propositional-total-space s (x , m) (y , n)
  = to-subtype-＝ (∈-is-prop K) (s x y m n)

 types-with-subsubgleton-structure-have-propositional-total-space
  : subsingleton-set-structure K
  → is-prop (𝕋 K)
 types-with-subsubgleton-structure-have-propositional-total-space s
  = subterminals-have-propositional-total-space
     (sets-with-subsingleton-structure-are-subterminal K s)

\end{code}

TODO. I don't think the assumption that X is a set can be removed from
the following.

\begin{code}

module _ {X : 𝓤 ̇ } where

 aflabby'-gives-flabby-structure
   : is-set X
   → aflabby' X
   → flabby-structure X 𝓤
 aflabby'-gives-flabby-structure X-is-set a = ⨆ , e
  where
   module _ (P : Ω 𝓤) (f : P holds → X) where

    K : 𝓟 X
    K x = fiber f x ,
          maps-of-props-into-sets-are-embeddings f (holds-is-prop P) X-is-set x

    I : is-subterminal-set K
    I x y (p , d) (q , e) =
     x   ＝⟨ d ⁻¹ ⟩
     f p ＝⟨ ap f (holds-is-prop P p q) ⟩
     f q ＝⟨ e ⟩
     y   ∎

    II : subsingleton-set-structure K
    II = a K I

    ⨆ : X
    ⨆ = pr₁ II

    _ : (x : X) → fiber f x → x ＝ ⨆
    _ = pr₂ II

    e : (p : P holds) → ⨆ ＝ f p
    e p = (pr₂ II (f p) (p , refl))⁻¹

\end{code}

The converse doesn't require X to be a set.

\begin{code}

 flabby-structure-gives-aflabby'
  : flabby-structure X 𝓤
  → aflabby' X
 flabby-structure-gives-aflabby' (⨆ , e) K K-subterminal = x₀ , I
  where
   P : Ω 𝓤
   P = (Σ x ꞉ X , x ∈ K) ,
       (λ {(x , m) (y , n) → to-subtype-＝
                              (∈-is-prop K)
                              (K-subterminal x y m n)})

   f : P holds → X
   f = pr₁

   x₀ : X
   x₀ = ⨆ P f

   I : (x : X) → x ∈ K → x ＝ x₀
   I x m = (e P f (x , m))⁻¹

\end{code}

We do the truncated version now, which is what is relevant for the
comparison with the reference [1], as it works with the truncated
versions (implicitly, because when one works in the internal language
of a 1-topos, as [1] does, existence takes values in Ω). .

\begin{code}

 module _
          (pt : propositional-truncations-exist)
        where

  open PropositionalTruncation pt
  open injective (λ 𝓤 𝓥 → fe {𝓤} {𝓥}) pt

  module _ (K : 𝓟 X) where

   is-subsingleton-set : 𝓤 ̇
   is-subsingleton-set = ∃ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀)

   being-subsingleton-set-is-prop : is-prop is-subsingleton-set
   being-subsingleton-set-is-prop = ∃-is-prop

   subsingleton-sets-are-subterminal
    : is-set X
    → is-subsingleton-set
    → is-subterminal-set K
   subsingleton-sets-are-subterminal X-is-set =
    ∥∥-rec
     (being-subterminal-set-is-prop K X-is-set)
     (sets-with-subsingleton-structure-are-subterminal K)

  flabby' : 𝓤 ⁺ ̇
  flabby' = (K : 𝓟 {𝓤} X)
          → is-subterminal-set K
          → is-subsingleton-set K

  flabby'-gives-flabby : is-set X → flabby' → flabby X 𝓤
  flabby'-gives-flabby X-is-set ϕ' P P-is-prop f = IV
   where
    K : 𝓟 X
    K x = fiber f x ,
          maps-of-props-into-sets-are-embeddings f P-is-prop X-is-set x

    I : is-subterminal-set K
    I x y (p , d) (q , e) =
     x   ＝⟨ d ⁻¹ ⟩
     f p ＝⟨ ap f (P-is-prop p q) ⟩
     f q ＝⟨ e ⟩
     y   ∎

    II : is-subsingleton-set K
    II = ϕ' K I

    III : (Σ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀))
        → (Σ x ꞉ X , ((p : P) → x ＝ f p))
    III (x₀ , α) = x₀ , (λ p → (α (f p) (p , refl))⁻¹)

    IV : ∃ x ꞉ X , ((p : P) → x ＝ f p)
    IV = ∥∥-functor III II

  flabby-gives-flabby' : flabby X 𝓤 → flabby'
  flabby-gives-flabby' ϕ K K-subterminal = γ
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

    γ : ∃ x₀ ꞉ X , ((x : X) → x ∈ K → x ＝ x₀)
    γ = ∥∥-functor (λ (x₀ , e) → x₀ , (λ x m → (e (x , m))⁻¹)) I

\end{code}
