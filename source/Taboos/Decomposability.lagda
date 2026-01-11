Martin Escardo, 25th August 2022,
written down in Agda 27th August 2022 while travelling back from
Thierry Coquand's 60th birthday celebration.

The type of ordinals is decomposable as a disjoint union of two
pointed types if and only if weak excluded middle holds (every negated
proposition is decidable, which is equivalent to De Morgan's Law).

Equivalently, there is a function f : Ordinal 𝓤 → 𝟚 such that f α ＝ 0
and f β = 1 for some ordinals α and β if and only if weak excluded
middle holds.

In other words, the type Ordinal 𝓤 has no non-trivial decidable
property unless weak excluded middle holds.

Further additions 3rd August 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Taboos.Decomposability (fe : FunExt) where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Base
open import UF.ClassicalLogic
open import UF.Classifiers
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.PropTrunc
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Univalence

private
 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 ⇁_ : Ω 𝓤 → Ω 𝓤
 ⇁_ = not fe'

\end{code}

A type X is decomposable if there are pointed types X₀ and X₁ with
X ≃ X₀ + X₁. Equivalently, X is decomposable if there is a
non-constant function f : X → 𝟚, in the strong sense that there are x₀
and x₁ in X that are mapped to respectively ₀ and ₁ by f.

We first work with the type of all decompositions, in the above two
equivalent manifestations, and later we consider decomposability
defined as its propositional truncation.

\begin{code}

decomposition : 𝓤 ̇ → 𝓤 ̇
decomposition X = Σ f ꞉ (X → 𝟚) , (Σ x₀ ꞉ X , f x₀ ＝ ₀) × (Σ x₁ ꞉ X , f x₁ ＝ ₁)

decomposition' : 𝓤 ̇ → 𝓤 ⁺ ̇
decomposition' {𝓤} X = Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X) × Y ₀ × Y ₁

\end{code}

We remark that the above two decomposition types are equivalent, but
we don't use this fact anywhere for the moment, and we work with the
first one.

\begin{code}

decomposition-lemma : is-univalent 𝓤
                    → (X : 𝓤 ̇ )
                    → (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X))
                    ≃ (X → 𝟚)
decomposition-lemma {𝓤} ua X =
 (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X))       ≃⟨ I ⟩
 (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , ((Σ n ꞉ 𝟚 , Y n) ≃ X)) ≃⟨ II ⟩
 (X → 𝟚)                                    ■
 where
  I  = Σ-cong (λ Y → ≃-cong-left fe (≃-sym alternative-+))
  II = Σ-fibers-≃ ua fe'

decompositions-agree : is-univalent 𝓤
                     → (X : 𝓤 ̇ )
                     → decomposition X ≃ decomposition' X
decompositions-agree {𝓤} ua X =
 (Σ f ꞉ (X → 𝟚) , fiber f ₀ × fiber f ₁)                        ≃⟨ I ⟩
 (Σ (Y , _) ꞉ (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X)) , Y ₀ × Y ₁)  ≃⟨ II ⟩
 (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X) × Y ₀ × Y ₁)                ■
 where
  I  = Σ-change-of-variable-≃ _ (≃-sym (decomposition-lemma ua X))
  II = Σ-assoc

decompositions-as-retracts : (X : 𝓤 ̇ ) → decomposition X ≃ retract 𝟚 of X
decompositions-as-retracts X = Σ-cong I
 where
  I : (f : X → 𝟚) → fiber f ₀ × fiber f ₁ ≃ has-section f
  I f =
   fiber f ₀ × fiber f ₁                           ≃⟨by-definition⟩
   (Σ x₀ ꞉ X , f x₀ ＝ ₀) × (Σ x₁ ꞉ X , f x₁ ＝ ₁) ≃⟨ ≃-sym (alternative-× fe') ⟩
   (Π n ꞉ 𝟚 , Σ x ꞉ X , f x ＝ n)                  ≃⟨ ΠΣ-distr-≃ ⟩
   has-section f                                   ■

WEM-gives-decomposition-of-two-pointed-types : typal-WEM 𝓤
                                             → (X : 𝓤 ̇ )
                                             → has-two-distinct-points X
                                             → decomposition X
WEM-gives-decomposition-of-two-pointed-types wem X ((x₀ , x₁) , d) = γ
 where
  g : (x : X) → ¬ (x ≠ x₀) + ¬¬ (x ≠ x₀) → 𝟚
  g x (inl _) = ₀
  g x (inr _) = ₁

  h : (x : X) → ¬ (x ≠ x₀) + ¬¬ (x ≠ x₀)
  h x = wem (x ≠ x₀)

  f : X → 𝟚
  f x = g x (h x)

  g₀ : (δ : ¬ (x₀ ≠ x₀) + ¬¬ (x₀ ≠ x₀)) → g x₀ δ ＝ ₀
  g₀ (inl _) = refl
  g₀ (inr u) = 𝟘-elim (three-negations-imply-one u refl)

  e₀ : f x₀ ＝ ₀
  e₀ = g₀ (h x₀)

  g₁ : (δ : ¬ (x₁ ≠ x₀) + ¬¬ (x₁ ≠ x₀)) → g x₁ δ ＝ ₁
  g₁ (inl ϕ) = 𝟘-elim (ϕ (≠-sym d))
  g₁ (inr _) = refl

  e₁ : f x₁ ＝ ₁
  e₁ = g₁ (h x₁)

  γ : decomposition X
  γ = f , (x₀ , e₀) , (x₁ , e₁)

WEM-gives-decomposition-of-ordinals-type⁺ : typal-WEM (𝓤 ⁺)
                                          → decomposition (Ordinal 𝓤)
WEM-gives-decomposition-of-ordinals-type⁺ {𝓤} wem =
 WEM-gives-decomposition-of-two-pointed-types wem (Ordinal 𝓤)
  ((𝟙ₒ , 𝟘ₒ) , (λ (e : 𝟙ₒ ＝ 𝟘ₒ) → 𝟘-elim (idtofun 𝟙 𝟘 (ap ⟨_⟩ e) ⋆)))

\end{code}

We can strengthen the hypothesis of the above implication to WEM 𝓤
using the fact that the type Ordinal 𝓤 ̇ is locally small.

\begin{code}

WEM-gives-decomposition-of-two-pointed-types⁺ : typal-WEM 𝓤
                                              → (X : 𝓤 ⁺ ̇ )
                                              → is-locally-small X
                                              → has-two-distinct-points X
                                              → decomposition X
WEM-gives-decomposition-of-two-pointed-types⁺ {𝓤} wem X l ((x₀ , x₁) , d) = γ
 where
  g : (x : X) → ¬ (x ≠⟦ l ⟧ x₀) + ¬¬ (x ≠⟦ l ⟧ x₀) → 𝟚
  g x (inl _) = ₀
  g x (inr _) = ₁

  h : (x : X) → ¬ (x ≠⟦ l ⟧ x₀) + ¬¬ (x ≠⟦ l ⟧ x₀)
  h x = wem (x ≠⟦ l ⟧ x₀)

  f : X → 𝟚
  f x = g x (h x)

  g₀ : (δ : ¬ (x₀ ≠⟦ l ⟧ x₀) + ¬¬ (x₀ ≠⟦ l ⟧ x₀)) → g x₀ δ ＝ ₀
  g₀ (inl _) = refl
  g₀ (inr u) = 𝟘-elim (three-negations-imply-one u ＝⟦ l ⟧-refl)

  e₀ : f x₀ ＝ ₀
  e₀ = g₀ (h x₀)

  g₁ : (δ : ¬ (x₁ ≠⟦ l ⟧ x₀) + ¬¬ (x₁ ≠⟦ l ⟧ x₀)) → g x₁ δ ＝ ₁
  g₁ (inl ϕ) = 𝟘-elim (ϕ (≠-gives-≠⟦ l ⟧ (≠-sym d)))
  g₁ (inr _) = refl

  e₁ : f x₁ ＝ ₁
  e₁ = g₁ (h x₁)

  γ : decomposition X
  γ = f , (x₀ , e₀) , (x₁ , e₁)

WEM-gives-decomposition-of-ordinals-type : is-univalent 𝓤
                                         → typal-WEM 𝓤
                                         → decomposition (Ordinal 𝓤)
WEM-gives-decomposition-of-ordinals-type {𝓤} ua wem =
 WEM-gives-decomposition-of-two-pointed-types⁺ wem (Ordinal 𝓤)
  (the-type-of-ordinals-is-locally-small ua fe')
  ((𝟙ₒ , 𝟘ₒ) , (λ (e : 𝟙ₒ ＝ 𝟘ₒ) → 𝟘-elim (idtofun 𝟙 𝟘 (ap ⟨_⟩ e) ⋆)))

\end{code}

For the converse, we use the following notion, where Ω 𝓤 is the type
of truth values, or propositions, in the universe 𝓤. An Ω-path from x
to y in a type X is a function f ꞉ Ω 𝓥 → X that maps false to x and
true to y. We collect all such functions in a type Ω-Path 𝓥 x y.

\begin{code}

Ω-Path : {X : 𝓤 ̇ } (𝓥 : Universe) → X → X → 𝓤 ⊔ (𝓥 ⁺) ̇
Ω-Path {𝓤} {X} 𝓥 x y = Σ f ꞉ (Ω 𝓥 → X) , (f ⊥ ＝ x) × (f ⊤ ＝ y)

\end{code}

The type of ordinals in any universe has Ω-paths between any two points.

\begin{code}

has-Ω-paths : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
has-Ω-paths 𝓥 X = (x y : X) → Ω-Path 𝓥 x y

type-of-ordinals-has-Ω-paths : is-univalent 𝓤
                             → has-Ω-paths 𝓤 (Ordinal 𝓤)
type-of-ordinals-has-Ω-paths {𝓤} ua α β = f , γ⊥ , γ⊤
 where

  f : Ω 𝓤 → Ordinal 𝓤
  f p = (Ω-to-ordinal (⇁ p) ×ₒ α) +ₒ (Ω-to-ordinal p ×ₒ β)

  γ⊥ : f ⊥ ＝ α
  γ⊥ = eqtoidₒ ua fe' (f ⊥) α (u , o , e , p)
   where
    u : ⟨ f ⊥ ⟩ → ⟨ α ⟩
    u (inl (x , a)) = a

    o : is-order-preserving (f ⊥) α u
    o (inl (x , a)) (inl (y , b)) (inl l) = l

    v : ⟨ α ⟩ → ⟨ f ⊥ ⟩
    v a = inl (𝟘-elim , a)

    vu : v ∘ u ∼ id
    vu (inl (x , a)) = ap inl (to-×-＝ (dfunext fe' (λ z → 𝟘-elim z)) refl)

    uv : u ∘ v ∼ id
    uv a = refl

    e : is-equiv u
    e = qinvs-are-equivs u (v , vu , uv)

    p : is-order-preserving α (f ⊥) v
    p a b l = inl l

  γ⊤ : f ⊤ ＝ β
  γ⊤ = eqtoidₒ ua fe' (f ⊤) β (u , o , e , p)
   where
    u : ⟨ f ⊤ ⟩ → ⟨ β ⟩
    u (inl (f , _)) = 𝟘-elim (f ⋆)
    u (inr (⋆ , b)) = b

    o : is-order-preserving (f ⊤) β u
    o (inl (f , _)) y l = 𝟘-elim (f ⋆)
    o (inr (⋆ , _)) (inr (⋆ , _)) (inl l) = l

    v : ⟨ β ⟩ → ⟨ f ⊤ ⟩
    v b = inr (⋆ , b)

    vu : v ∘ u ∼ id
    vu (inl (f , _)) = 𝟘-elim (f ⋆)
    vu (inr (⋆ , b)) = refl

    uv : u ∘ v ∼ id
    uv b = refl

    e : is-equiv u
    e = qinvs-are-equivs u (v , vu , uv)

    p : is-order-preserving β (f ⊤) v
    p b c l = inl l

decomposition-of-Ω-gives-WEM : propext 𝓤
                             → decomposition (Ω 𝓤)
                             → typal-WEM 𝓤
decomposition-of-Ω-gives-WEM
  {𝓤} pe (f , (p₀@(P₀ , i₀) , e₀) , (p₁@(P₁ , i₁) , e₁)) = V
 where
  g : Ω 𝓤 → Ω 𝓤
  g (Q , j) = ((P₀ × Q) + (P₁ × ¬ Q)) , k
   where
    k : is-prop ((P₀ × Q) + (P₁ × ¬ Q))
    k = +-is-prop
         (×-is-prop i₀ j)
         (×-is-prop i₁ (negations-are-props fe'))
         (λ (p₀ , q) (p₁ , ν) → ν q)

  I₀ : (q : Ω 𝓤) → q holds → f (g q) ＝ ₀
  I₀ q h = II
   where
    I : g q ＝ p₀
    I = to-subtype-＝
          (λ _ → being-prop-is-prop fe')
          (pe (pr₂ (g q)) i₀
            (cases pr₁ (λ (_ , n) → 𝟘-elim (n h)))
            (λ x → inl (x , h)))

    II = f (g q) ＝⟨ ap f I ⟩
         f p₀    ＝⟨ e₀ ⟩
         ₀       ∎

  I₁ : (q : Ω 𝓤) → ¬ (q holds) → f (g q) ＝ ₁
  I₁ q n = II
   where
    I : g q ＝ p₁
    I = to-subtype-＝
          (λ _ → being-prop-is-prop fe')
          (pe (pr₂ (g q)) i₁
          (cases (λ (_ , h) → 𝟘-elim (n h)) pr₁)
          (λ x → inr (x , n)))

    II = f (g q) ＝⟨ ap f I ⟩
         f p₁    ＝⟨ e₁ ⟩
         ₁       ∎

  III₀ : (q : Ω 𝓤) → f (g q) ＝ ₀ → ¬ (q holds) + ¬¬ (q holds)
  III₀ q e = inr (contrapositive (I₁ q) (equal-₀-different-from-₁ e))

  III₁ : (q : Ω 𝓤) → f (g q) ＝ ₁ → ¬ (q holds) + ¬¬ (q holds)
  III₁ q e = inl (contrapositive (I₀ q) (equal-₁-different-from-₀ e))

  IV : (Q : 𝓤 ̇ ) → is-prop Q → ¬ Q + ¬¬ Q
  IV Q j = 𝟚-equality-cases (III₀ (Q , j)) (III₁ (Q , j))

  V : (Q : 𝓤 ̇ ) → ¬ Q + ¬¬ Q
  V = WEM-gives-typal-WEM fe' IV

decomposition-of-type-with-Ω-paths-gives-WEM : propext 𝓥
                                             → {X : 𝓤 ̇ }
                                             → decomposition X
                                             → has-Ω-paths 𝓥 X
                                             → typal-WEM 𝓥
decomposition-of-type-with-Ω-paths-gives-WEM
  {𝓥} {𝓤} pe {X} (f , (x₀ , e₀) , (x₁ , e₁)) c = γ
 where
  g : Ω 𝓥 → X
  g = pr₁ (c x₀ x₁)

  gp : (g ⊥ ＝ x₀) × (g ⊤ ＝ x₁)
  gp = pr₂ (c x₀ x₁)

  I₀ = f (g ⊥) ＝⟨ ap f (pr₁ gp) ⟩
       f x₀    ＝⟨ e₀ ⟩
       ₀       ∎

  I₁ = f (g ⊤) ＝⟨ ap f (pr₂ gp) ⟩
       f x₁    ＝⟨ e₁ ⟩
       ₁       ∎

  γ : typal-WEM 𝓥
  γ = decomposition-of-Ω-gives-WEM pe (f ∘ g , (⊥ , I₀) , (⊤ , I₁))

decomposition-of-ordinals-type-gives-WEM : is-univalent 𝓤
                                         → decomposition (Ordinal 𝓤)
                                         → typal-WEM 𝓤
decomposition-of-ordinals-type-gives-WEM ua d =
 decomposition-of-type-with-Ω-paths-gives-WEM
  (univalence-gives-propext ua)
  d
  (type-of-ordinals-has-Ω-paths ua)

Ordinal-decomposition-iff-WEM : is-univalent 𝓤
                              → decomposition (Ordinal 𝓤) ↔ typal-WEM 𝓤
Ordinal-decomposition-iff-WEM ua =
 decomposition-of-ordinals-type-gives-WEM ua ,
 WEM-gives-decomposition-of-ordinals-type ua

\end{code}

We now assume that propositional truncations exist to define
decomposability as the truncation of the type of decompositions. It is
a corollary of the above development that the decomposability of the
type of ordinals gives a specific decomposition.

\begin{code}

module decomposability (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 decomposable : 𝓤 ̇ → 𝓤 ̇
 decomposable X = ∥ decomposition X ∥

 Ordinal-decomposable-iff-WEM : is-univalent 𝓤
                              → decomposable (Ordinal 𝓤) ↔ typal-WEM 𝓤
 Ordinal-decomposable-iff-WEM ua =
  ∥∥-rec (typal-WEM-is-prop fe) (decomposition-of-ordinals-type-gives-WEM ua) ,
  (λ wem → ∣ WEM-gives-decomposition-of-ordinals-type ua wem ∣)

 decomposability-gives-decomposition : is-univalent 𝓤
                                     → decomposable (Ordinal 𝓤)
                                     → decomposition (Ordinal 𝓤)
 decomposability-gives-decomposition ua δ =
  WEM-gives-decomposition-of-ordinals-type ua
   (lr-implication (Ordinal-decomposable-iff-WEM ua) δ)

\end{code}

Notice that the formulation of this fact doesn't refer to WEM, but its
proof uses WEM, which follows from the hypothesis. Even though the
types decomposable (Ordinal 𝓤) and WEM are property, we get data out
of them if we are given a proof of decomposability.


Added 9th September 2022 by Tom de Jong (which is subsumed by a remark
below added 25th July 2024).

After a discussion with Martín on 8th September 2022, we noticed that
the decomposability theorem can be generalised from Ord 𝓤 to any
locally small 𝓤-sup-lattice with two distinct points. (This is indeed
a generalisation because Ord 𝓤 is a locally small 𝓤-sup-lattice, at
least in the presence of small set quotients or set replacement, see
Ordinals.OrdinalOfOrdinalsSuprema.)

One direction is still given by the lemma above:
  WEM-gives-decomposition-of-two-pointed-types⁺ :
      WEM 𝓤
    → (X : 𝓤 ⁺ ̇ )
    → is-locally-small X
    → has-two-distinct-points X
    → decomposition X

[NB. Predicatively, nontrivial 𝓤-sup-lattices necessarily have large
     carriers [dJE21,dJE22], so that the simpler lemma

     WEM-gives-decomposition-of-two-pointed-types :
         WEM 𝓤
       → (X : 𝓤 ̇ )
       → has-two-distinct-points X
       → decomposition X

     is not sufficient.]

For the other we use

  decomposition-of-type-with-Ω-paths-gives-WEM :
      {X : 𝓤 ̇ }
    → decomposition X
    → has-Ω-paths 𝓥 X
    → WEM 𝓥

The point is that every 𝓤-sup-lattice X has Ω𝓤-paths, because given x
y : X, we can define f : Ω 𝓤 → X by mapping a proposition P to the
join of the family

  δ : 𝟙 + P → X
  δ(inl ⋆) = x;
  δ(inr p) = y.

The family δ also plays a key role in [dJE21,dJE22] although we have
the restriction that x ⊑ y in those papers, because we consider a
broader collection of posets there that includes the 𝓤-sup-lattices,
but also 𝓤-bounded-complete posets and 𝓤-directed complete posets.

References
----------

[dJE21] Tom de Jong and Martín Hötzel Escardó.
        ‘Predicative Aspects of Order Theory in Univalent Foundations’.
        In: 6th International Conference on Formal Structures for Computation and
        Deduction (FSCD 2021). Ed. by Naoki Kobayashi. Vol. 195.
        Leibniz International Proceedings in Informatics (LIPIcs).
        Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2021, 8:1–8:18.
        doi: 10.4230/LIPIcs.FSCD.2021.8.

[dJE22] Tom de Jong and Martín Hötzel Escardó.
        ‘On Small Types in Univalent Foundations’. Sept. 2022.
        arXiv: 2111.00482 [cs.LO]. Revised and expanded version of [dJE21b].
        Accepted pending minor revision to a special issue of Logical Methods in
        Computer Science on selected papers from FSCD 2021.

TODO. Implement the above thoughts.

Added 3rd August 2023 by Martin Escardo. Injective types are
decomposable iff WEM holds. This subsumes the above developement,
because the type of ordinals is injective.

\begin{code}

open import InjectiveTypes.Blackboard fe
open import InjectiveTypes.OverSmallMaps fe
open import Ordinals.Injectivity

open ordinals-injectivity fe

\end{code}

A naive application of injectivity gives the following:

\begin{code}

ainjective-types-have-Ω-paths-naive : propext 𝓦
                                    → (D : 𝓤 ̇ )
                                    → ainjective-type D 𝓤₀ (𝓦 ⁺)
                                    → has-Ω-paths 𝓦 D
ainjective-types-have-Ω-paths-naive {𝓦} {𝓤} pe D D-ainj x₀ x₁ = II I
 where
  f : 𝟚 → D
  f ₀ = x₀
  f ₁ = x₁

  I : Σ g ꞉ (Ω 𝓦 → D) , g ∘ 𝟚-to-Ω ∼ f
  I = D-ainj 𝟚-to-Ω (𝟚-to-Ω-is-embedding fe' pe) f

  II : type-of I → Ω-Path 𝓦 x₀ x₁
  II (g , h) = g , h ₀ , h ₁

\end{code}

But this is too weak for applications, as the universe 𝓦⁺ is higher
than we can obtain in practice.

This can be improved as follows, exploiting the fact that the map
𝟚-to-Ω : 𝟚 → Ω 𝓤 has 𝓤-small fibers and that algebraic flabbiness
gives injectivity over embeddings with small fibers for lower
universes. The key point is that this allows to replace 𝓦⁺ by 𝓦 in the
above, so that we can apply this to the injectivity of the universe
and to that of the type of ordinals, and more examples like these.

\begin{code}

ainjective-types-have-Ω-paths : propext 𝓥
                              → (D : 𝓤 ̇ )
                              → ainjective-type D 𝓥 𝓦
                              → has-Ω-paths 𝓥 D
ainjective-types-have-Ω-paths {𝓥} {𝓤} {𝓦} pe D D-ainj x₀ x₁ = II I
 where
  f : 𝟚 → D
  f ₀ = x₀
  f ₁ = x₁

  I : Σ g ꞉ (Ω 𝓥 → D) , g ∘ 𝟚-to-Ω ∼ f
  I = ainjectivity-over-small-maps 𝓥
       D
       D-ainj
       𝟚-to-Ω
       (𝟚-to-Ω-is-embedding fe' pe)
       (𝟚-to-Ω-is-small-map {𝓥} fe' pe)
       f

  II : type-of I → Ω-Path 𝓥 x₀ x₁
  II (g , h) = g , h ₀ , h ₁

decomposition-of-ainjective-type-gives-WEM : propext 𝓥
                                           → (D : 𝓤 ̇ )
                                           → ainjective-type D 𝓥 𝓦
                                           → decomposition D
                                           → typal-WEM 𝓥
decomposition-of-ainjective-type-gives-WEM
 {𝓥} {𝓤} {𝓦} pe D D-ainj D-decomp =
  decomposition-of-type-with-Ω-paths-gives-WEM
   pe
   D-decomp
   (ainjective-types-have-Ω-paths {𝓥} {𝓤} {𝓦} pe D D-ainj)

\end{code}

Examples:

\begin{code}

decomposition-of-universe-gives-WEM : is-univalent 𝓤
                                    → decomposition (𝓤 ̇ )
                                    → typal-WEM 𝓤
decomposition-of-universe-gives-WEM {𝓤} ua =
 decomposition-of-ainjective-type-gives-WEM {𝓤} {𝓤 ⁺} {𝓤}
  (univalence-gives-propext ua)
  (𝓤 ̇ )
  (universes-are-ainjective-Π ua)

decomposition-of-ordinals-type-gives-WEM-bis : is-univalent 𝓤
                                             → decomposition (Ordinal 𝓤)
                                             → typal-WEM 𝓤
decomposition-of-ordinals-type-gives-WEM-bis {𝓤} ua =
 decomposition-of-ainjective-type-gives-WEM {𝓤} {𝓤 ⁺} {𝓤}
  (univalence-gives-propext ua)
  (Ordinal 𝓤)
  (Ordinal-is-ainjective ua)

\end{code}

Added by Martin Escardo and Tom de Jong 18th July 2024. We generalize
a fact given above from ordinals to injective types.

\begin{code}

module decomposability-bis (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open decomposability pt

 ainjective-type-decomposable-iff-WEM
  : propext 𝓤
  → (D : 𝓤 ̇ )
  → ainjective-type D 𝓤 𝓥
  → has-two-distinct-points D
  → decomposable D ↔ typal-WEM 𝓤
 ainjective-type-decomposable-iff-WEM pe D D-ainj htdp =
  ∥∥-rec
   (typal-WEM-is-prop fe)
   (decomposition-of-ainjective-type-gives-WEM pe D D-ainj) ,
  (λ wem → ∣ WEM-gives-decomposition-of-two-pointed-types wem D htdp ∣)

\end{code}

Added 25th July 2024 by Tom de Jong and Martin Escardo.

The previous theorem, however, doesn't capture our examples of injective types. Indeed, the assumption that D : 𝓤 is injective with respect to 𝓤
and 𝓥 is a bit unnatural, as all known examples of injective types are
large, e.g. the universe 𝓤 is injective w.r.t 𝓤 and 𝓤, as are the
ordinals in 𝓤 and the propositions in 𝓤. In fact, in
InjectiveTypes.Resizing we showed that such injective types are
necessarily large unless Ω¬¬-resizing holds. Therefore, we now improve
and generalize the above theorem to a large, but locally small,
type, so that all known examples are captured.

\begin{code}

 ainjective-type-decomposable-iff-WEM⁺
  : propext 𝓤
  → (D : 𝓤 ⁺ ̇ )
  → is-locally-small D
  → ainjective-type D 𝓤 𝓥
  → has-two-distinct-points D
  → decomposable D ↔ typal-WEM 𝓤
 ainjective-type-decomposable-iff-WEM⁺ pe D D-ls D-ainj htdp =
  ∥∥-rec
   (typal-WEM-is-prop fe)
   (decomposition-of-ainjective-type-gives-WEM pe D D-ainj) ,
  (λ wem → ∣ WEM-gives-decomposition-of-two-pointed-types⁺ wem D D-ls htdp ∣)

\end{code}

End of addition.

Notice that the following doesn't mention WEM in its statement, but
its proof does. Although the proof is constructive, the assumption is
necessarily non-constructive.

\begin{code}

 ainjective-type-decomposability-gives-decomposition
  : propext 𝓤
  → (D : 𝓤 ̇ )
  → ainjective-type D 𝓤 𝓥
  → has-two-distinct-points D
  → decomposable D
  → decomposition D
 ainjective-type-decomposability-gives-decomposition pe D D-ainj htdp δ =
  WEM-gives-decomposition-of-two-pointed-types
   (lr-implication (ainjective-type-decomposable-iff-WEM pe D D-ainj htdp) δ)
   D
   htdp

\end{code}

Also added 25th July 2024 for the same reason given above:

\begin{code}

 ainjective-type-decomposability-gives-decomposition⁺
  : propext 𝓤
  → (D : 𝓤 ⁺ ̇ )
  → is-locally-small D
  → ainjective-type D 𝓤 𝓥
  → has-two-distinct-points D
  → decomposable D
  → decomposition D
 ainjective-type-decomposability-gives-decomposition⁺ pe D D-ls D-ainj htdp δ =
  WEM-gives-decomposition-of-two-pointed-types⁺
   (lr-implication (ainjective-type-decomposable-iff-WEM⁺ pe D D-ls D-ainj htdp) δ)
   D
   D-ls
   htdp

\end{code}

Added by Martin Escardo 10th June 2024. From any non-trivial,
totally separated, injective type we get the double negation of the
principle of weak excluded middle. Here by non-trivial we mean that
not all two elements are equal, which means that the type is not a
proposition.

(Of course, "Σ" in the hypothesis can be replaced by "∃" because the
type of the conclusion, being a negation, is a proposition, if we
assume function extensionality.)

\begin{code}

open import UF.Hedberg using (wconstant)
open import TypeTopology.TotallySeparated

non-trivial-totally-separated-ainjective-type-gives-¬¬-WEM
 : propext 𝓥
 → (Σ X ꞉ 𝓤 ̇ , ((¬ is-prop X) × is-totally-separated X × ainjective-type X 𝓥 𝓦))
 → ¬¬ typal-WEM 𝓥
non-trivial-totally-separated-ainjective-type-gives-¬¬-WEM
  {𝓥} {𝓤} {𝓦} pe (X , X-is-not-prop , X-is-totally-separated , X-ainj) = V
 where
  I : ¬ decomposition X → (p : X → 𝟚) → wconstant p
  I δ p x₀ x₁ = h (p x₀) (p x₁) refl refl
   where
    h : (b₀ b₁ : 𝟚) → p x₀ ＝ b₀ → p x₁ ＝ b₁ → p x₀ ＝ p x₁
    h ₀ ₀ e₀ e₁ = e₀ ∙ e₁ ⁻¹
    h ₀ ₁ e₀ e₁ = 𝟘-elim (δ (p , (x₀ , e₀) , (x₁ , e₁)))
    h ₁ ₀ e₀ e₁ = 𝟘-elim (δ (p , (x₁ , e₁) , (x₀ , e₀)))
    h ₁ ₁ e₀ e₁ = e₀ ∙ e₁ ⁻¹

  II : ((p : X → 𝟚) → wconstant p) → is-prop X
  II w x₀ x₁ = X-is-totally-separated (λ p → w p x₀ x₁)

  III : ¬ decomposition X → is-prop X
  III = II ∘ I

  IV : ¬¬ decomposition X
  IV = contrapositive III X-is-not-prop

  V : ¬¬ typal-WEM 𝓥
  V = ¬¬-functor
       (decomposition-of-ainjective-type-gives-WEM pe X X-ainj)
       IV

\end{code}

Notice that ¬ WEM 𝓤 is consistent and hence ¬¬ WEM 𝓤 is not
provable. But of course ¬¬ WEM 𝓤 is consistent as it follows from WEM 𝓤,
which in turn follows from EM 𝓤.

More examples are included in Iterative.Multisets-Addendum and
Iterative.Sets-Addendum.
