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

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness #-}

open import UF.Univalence

module Ordinals.Indecomposable (ua : Univalence) where

open import MLTT.Spartan
open import MLTT.Two-Properties

open import UF.Base
open import UF.Classifiers
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

⇁_ : Ω 𝓤 → Ω 𝓤
⇁_ = not fe'

open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

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

The above two decomposition types are equivalent:

\begin{code}

decomposition-lemma : (X : 𝓤 ̇ )
                    → (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X))
                    ≃ (X → 𝟚)
decomposition-lemma {𝓤} X =
 (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X))       ≃⟨ I ⟩
 (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , ((Σ n ꞉ 𝟚 , Y n) ≃ X)) ≃⟨ II ⟩
 (X → 𝟚)                                    ■
 where
  I  = Σ-cong (λ Y → ≃-cong-left fe (≃-sym alternative-+))
  II = Σ-fibers-≃ (ua 𝓤) fe'

decompositions-agree : (X : 𝓤 ̇ ) → decomposition X ≃ decomposition' X
decompositions-agree {𝓤} X =
 (Σ f ꞉ (X → 𝟚) , fiber f ₀ × fiber f ₁)                        ≃⟨ I ⟩
 (Σ (Y , _) ꞉ (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X)) , Y ₀ × Y ₁)  ≃⟨ II ⟩
 (Σ Y ꞉ (𝟚 → 𝓤 ̇ ) , (Y ₀ + Y ₁ ≃ X) × Y ₀ × Y ₁)                ■
 where
  I  = Σ-change-of-variable-≃ _ (≃-sym (decomposition-lemma X))
  II = Σ-assoc

WEM-gives-decomposition-of-two-pointed-types : WEM 𝓤
                                             → (X : 𝓤 ̇ )
                                             → has-two-distinct-points X
                                             → decomposition X
WEM-gives-decomposition-of-two-pointed-types wem X ((x₀ , x₁) , d) = γ
 where
  g : (x : X) → ¬ (x ≠ x₀) + ¬¬ (x ≠ x₀) → 𝟚
  g x (inl _) = ₀
  g x (inr _) = ₁

  h : (x : X) → ¬ (x ≠ x₀) + ¬¬ (x ≠ x₀)
  h x = wem (x ≠ x₀) (negations-are-props fe')

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

WEM-gives-decomposition-of-ordinals-type⁺ : WEM (𝓤 ⁺) → decomposition (Ordinal 𝓤)
WEM-gives-decomposition-of-ordinals-type⁺ {𝓤} wem =
 WEM-gives-decomposition-of-two-pointed-types wem (Ordinal 𝓤)
  ((𝟙ₒ , 𝟘ₒ) , (λ (e : 𝟙ₒ ＝ 𝟘ₒ) → 𝟘-elim (idtofun 𝟙 𝟘 (ap ⟨_⟩ e) ⋆)))

\end{code}

We can strengthen this to WEM 𝓤 → decomposition (Ordinal 𝓤) using
the fact that the type Ordinal 𝓤 ̇ is locally small.

\begin{code}

WEM-gives-decomposition-of-two-pointed-types⁺ : WEM 𝓤
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
  h x = wem (x ≠⟦ l ⟧ x₀) (negations-are-props fe')

  f : X → 𝟚
  f x = g x (h x)

  g₀ : (δ : ¬ (x₀ ≠⟦ l ⟧ x₀) + ¬¬ (x₀ ≠⟦ l ⟧ x₀)) → g x₀ δ ＝ ₀
  g₀ (inl _) = refl
  g₀ (inr u) = 𝟘-elim (three-negations-imply-one u ⟦ l ⟧-refl)

  e₀ : f x₀ ＝ ₀
  e₀ = g₀ (h x₀)

  g₁ : (δ : ¬ (x₁ ≠⟦ l ⟧ x₀) + ¬¬ (x₁ ≠⟦ l ⟧ x₀)) → g x₁ δ ＝ ₁
  g₁ (inl ϕ) = 𝟘-elim (ϕ (≠-gives-≠⟦ l ⟧ (≠-sym d)))
  g₁ (inr _) = refl

  e₁ : f x₁ ＝ ₁
  e₁ = g₁ (h x₁)

  γ : decomposition X
  γ = f , (x₀ , e₀) , (x₁ , e₁)

WEM-gives-decomposition-of-ordinals-type : WEM 𝓤 → decomposition (Ordinal 𝓤)
WEM-gives-decomposition-of-ordinals-type {𝓤} wem =
 WEM-gives-decomposition-of-two-pointed-types⁺ wem (Ordinal 𝓤)
  (the-type-of-ordinals-is-locally-small (ua 𝓤) fe')
  ((𝟙ₒ , 𝟘ₒ) , (λ (e : 𝟙ₒ ＝ 𝟘ₒ) → 𝟘-elim (idtofun 𝟙 𝟘 (ap ⟨_⟩ e) ⋆)))

\end{code}

For the converse, we use the following notion, where Ω 𝓤 is the type
of truth values, or propositions, in the universe 𝓤. An Ω-path from x
to y in a type X is a function f ꞉ Ω 𝓥 → X that maps false to x and
true to y. We collect all such functions in a type Ω-Path 𝓥 x y.

\begin{code}

Ω-Path : {X : 𝓤 ̇ } (𝓥 : Universe) → X → X → 𝓤 ⊔ (𝓥 ⁺) ̇
Ω-Path {𝓤} {X} 𝓥 x y = Σ f ꞉ (Ω 𝓥 → X) , (f ⊥Ω ＝ x) × (f ⊤Ω ＝ y)

\end{code}

The ordinals in any universe have Ω-paths between any two points.

\begin{code}

has-Ω-paths : (𝓥 : Universe) → 𝓤 ̇  → 𝓤 ⊔ (𝓥 ⁺) ̇
has-Ω-paths 𝓥 X = (x y : X) → Ω-Path 𝓥 x y

type-of-ordinals-has-Ω-paths : has-Ω-paths 𝓤 (Ordinal 𝓤)
type-of-ordinals-has-Ω-paths {𝓤} α β = f , γ⊥ , γ⊤
 where
  f : Ω 𝓤 → Ordinal 𝓤
  f p = (Ω-to-ordinal (⇁ p) ×ₒ α) +ₒ (Ω-to-ordinal p ×ₒ β)

  γ⊥ : f ⊥Ω ＝ α
  γ⊥ = eqtoidₒ (ua 𝓤) fe' (f ⊥Ω) α (u , o , e , p)
   where
    u : ⟨ f ⊥Ω ⟩ → ⟨ α ⟩
    u (inl (x , a)) = a

    o : is-order-preserving (f ⊥Ω) α u
    o (inl (x , a)) (inl (x , b)) (inr (refl , l)) = l

    v : ⟨ α ⟩ → ⟨ f ⊥Ω ⟩
    v a = inl (𝟘-elim , a)

    vu : v ∘ u ∼ id
    vu (inl (x , a)) = ap inl (to-×-＝ (dfunext fe' (λ z → 𝟘-elim z)) refl)

    uv : u ∘ v ∼ id
    uv a = refl

    e : is-equiv u
    e = qinvs-are-equivs u (v , vu , uv)

    p : is-order-preserving α (f ⊥Ω) v
    p a b l = inr (refl , l)

  γ⊤ : f ⊤Ω ＝ β
  γ⊤ = eqtoidₒ (ua 𝓤) fe' (f ⊤Ω) β (u , o , e , p)
   where
    u : ⟨ f ⊤Ω ⟩ → ⟨ β ⟩
    u (inl (f , _)) = 𝟘-elim (f ⋆)
    u (inr (⋆ , b)) = b

    o : is-order-preserving (f ⊤Ω) β u
    o (inl (f , _)) y l = 𝟘-elim (f ⋆)
    o (inr (⋆ , _)) (inr (⋆ , _)) (inr (_ , l)) = l

    v : ⟨ β ⟩ → ⟨ f ⊤Ω ⟩
    v b = inr (⋆ , b)

    vu : v ∘ u ∼ id
    vu (inl (f , _)) = 𝟘-elim (f ⋆)
    vu (inr (⋆ , b)) = refl

    uv : u ∘ v ∼ id
    uv b = refl

    e : is-equiv u
    e = qinvs-are-equivs u (v , vu , uv)

    p : is-order-preserving β (f ⊤Ω) v
    p b c l = inr (refl , l)

decomposition-of-Ω-gives-WEM : decomposition (Ω 𝓤) → WEM 𝓤
decomposition-of-Ω-gives-WEM {𝓤} (f , (p₀@(P₀ , i₀) , e₀) , (p₁@(P₁ , i₁) , e₁)) = IV
 where
  g : Ω 𝓤 → Ω 𝓤
  g (Q , j) = ((P₀ × Q) + (P₁ × ¬ Q)) , k
   where
    k : is-prop ((P₀ × Q) + (P₁ × ¬ Q))
    k (inl (a , b)) (inl (u , v)) = ap inl (to-×-＝ (i₀ a u) (j b v))
    k (inl (a , b)) (inr (u , v)) = 𝟘-elim (v b)
    k (inr (a , b)) (inl (u , v)) = 𝟘-elim (b v)
    k (inr (a , b)) (inr (u , v)) = ap inr (to-×-＝
                                             (i₁ a u)
                                             (negations-are-props fe' b v))

  I₀ : (q : Ω 𝓤) → q holds → f (g q) ＝ ₀
  I₀ q h = II
   where
    I : g q ＝ p₀
    I = to-subtype-＝
          (λ _ → being-prop-is-prop fe')
          (univalence-gives-propext (ua 𝓤) (pr₂ (g q)) i₀
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
          (univalence-gives-propext (ua 𝓤) (pr₂ (g q)) i₁
          (cases (λ (_ , h) → 𝟘-elim (n h)) pr₁)
          (λ x → inr (x , n)))

    II = f (g q) ＝⟨ ap f I ⟩
         f p₁    ＝⟨ e₁ ⟩
         ₁       ∎

  III₀ : (q : Ω 𝓤) → f (g q) ＝ ₀ → ¬ (q holds) + ¬¬ (q holds)
  III₀ q e = inr (contrapositive (I₁ q) (equal-₀-different-from-₁ e))

  III₁ : (q : Ω 𝓤) → f (g q) ＝ ₁ → ¬ (q holds) + ¬¬ (q holds)
  III₁ q e = inl (contrapositive (I₀ q) (equal-₁-different-from-₀ e))

  IV : (Q : 𝓤  ̇ )→ is-prop Q → ¬ Q + ¬¬ Q
  IV Q j = 𝟚-equality-cases (III₀ (Q , j)) (III₁ (Q , j))

decomposition-of-type-with-Ω-paths-gives-WEM : {X : 𝓤 ̇ }
                                             → decomposition X
                                             → has-Ω-paths 𝓥 X
                                             → WEM 𝓥
decomposition-of-type-with-Ω-paths-gives-WEM {𝓤} {𝓥} {X} (f , (x₀ , e₀) , (x₁ , e₁)) c = γ
 where
  g : Ω 𝓥 → X
  g = pr₁ (c x₀ x₁)

  gp : (g ⊥Ω ＝ x₀) × (g ⊤Ω ＝ x₁)
  gp = pr₂ (c x₀ x₁)

  I₀ = f (g ⊥Ω) ＝⟨ ap f (pr₁ gp) ⟩
       f x₀     ＝⟨ e₀ ⟩
       ₀        ∎

  I₁ = f (g ⊤Ω) ＝⟨ ap f (pr₂ gp) ⟩
       f x₁     ＝⟨ e₁ ⟩
       ₁        ∎

  γ : WEM 𝓥
  γ = decomposition-of-Ω-gives-WEM (f ∘ g , (⊥Ω , I₀) , (⊤Ω , I₁))

decomposition-of-ordinals-type-gives-WEM : decomposition (Ordinal 𝓤) → WEM 𝓤
decomposition-of-ordinals-type-gives-WEM d =
 decomposition-of-type-with-Ω-paths-gives-WEM d type-of-ordinals-has-Ω-paths

Ordinal-decomposition-iff-WEM : decomposition (Ordinal 𝓤) ⇔ WEM 𝓤
Ordinal-decomposition-iff-WEM = decomposition-of-ordinals-type-gives-WEM ,
                                WEM-gives-decomposition-of-ordinals-type

\end{code}

We now assume that propositional truncations exist to define
decomposability as the truncation of the type of decompositions. It is
a corollary of the above development that the decomposability of the
type of ordinals gives a specific decomposition.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt public

 decomposable : 𝓤 ̇ → 𝓤 ̇
 decomposable X = ∥ decomposition X ∥

 Ordinal-decomposable-iff-WEM : decomposable (Ordinal 𝓤) ⇔ WEM 𝓤
 Ordinal-decomposable-iff-WEM =
  ∥∥-rec (WEM-is-prop fe) decomposition-of-ordinals-type-gives-WEM ,
  (λ wem → ∣ WEM-gives-decomposition-of-ordinals-type wem ∣)

 decomposability-gives-decomposition : decomposable (Ordinal 𝓤) → decomposition (Ordinal 𝓤)
 decomposability-gives-decomposition {𝓤} δ = WEM-gives-decomposition-of-ordinals-type
                                               (lr-implication Ordinal-decomposable-iff-WEM δ)

\end{code}

Notice that the formulation of this doesn't refer to WEM, but its
proof uses WEM, which follows from the hypothesis. Even though
decomposable (Ordinal 𝓤) and WEM are property, we get data out of
them - if we are given a proof of decomposability.


Added 9th September 2022 by Tom de Jong.

After a discussion with Martín on 8th September 2022, we noticed that the
decomposability theorem can be generalised from Ord 𝓤 to any locally small
𝓤-sup-lattice with two distinct points. (This is indeed a generalisation because
Ord 𝓤 is a locally small 𝓤-sup-lattice, at least in the presence of small set
quotients or set replacement, see Ordinals.OrdinalOfOrdinalsSuprema.)

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

The point is that every 𝓤-sup-lattice X has Ω𝓤-paths, because given x y : X, we
can define f : Ω 𝓤 → X by mapping a proposition P to the join of the family

  δ : 𝟙 + P → X
  δ(inl ⋆) = x;
  δ(inr p) = y.

The family δ also plays a key role in [dJE21,dJE22] although we have the
restriction that x ⊑ y in those papers, because we consider a broader collection
of posets there that includes the 𝓤-sup-lattices, but also 𝓤-bounded-complete
posets and 𝓤-directed complete posets.

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
