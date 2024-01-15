Martin Escardo, December 2017 (but done much earlier on paper)

As discussed in the module CompactTypes, Bishop's "limited principle
of omniscience" amount to the compactness of the type ℕ, that is,

  Π p ꞉ ℕ → 𝟚 , (Σ n ꞉ ℕ , p n ＝ ₀) + (Π n ꞉ ℕ , p n ＝ ₁),

which fails in contructive mathematics (here in the sense that it is
independent - it is not provable, and its negation is also not
provable).

This is in general not a univalent proposition, because there may be
many n:ℕ with p n ＝ ₀. In univalent mathematics, we may get a
proposition by truncating the Σ to get the existential quantifier ∃
(see the Homotopy Type Theory book). Here instead we construct the
truncation directly, and call it LPO.

Using this and the module Prop-Tychonoff, we show that the function
type LPO→ℕ is compact, despite the fact that LPO is undecided in our
type theory.

(We needed to add new helper lemmas in the module
GenericConvergentSequence)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Taboos.LPO (fe : FunExt) where

open import CoNaturals.GenericConvergentSequence
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order
open import Notation.CanonicalMap
open import Notation.Order
open import TypeTopology.CompactTypes
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

private
 fe₀ = fe 𝓤₀ 𝓤₀

LPO : 𝓤₀ ̇
LPO = (x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , x ＝ ι n)

LPO-is-prop : is-prop LPO
LPO-is-prop = Π-is-prop fe₀ f
 where
  a : (x : ℕ∞) → is-prop (Σ n ꞉ ℕ , x ＝ ι n)
  a x (n , p) (m , q) = to-Σ-＝ (ℕ-to-ℕ∞-lc (p ⁻¹ ∙ q) , ℕ∞-is-set fe₀ _ _)

  f : (x : ℕ∞) → is-prop (is-decidable (Σ n ꞉ ℕ , x ＝ ι n))
  f x = decidability-of-prop-is-prop fe₀ (a x)

\end{code}

We now show that LPO is logically equivalent to its traditional
formulation by Bishop. However, the traditional formulation is not a
univalent proposition in general, and not type equivalent (in the
sense of UF) to our formulation.

\begin{code}

LPO-gives-compact-ℕ : LPO → is-compact ℕ
LPO-gives-compact-ℕ ℓ β = γ
  where
    A = (Σ n ꞉ ℕ , β n ＝ ₀) + (Π n ꞉ ℕ , β n ＝ ₁)

    α : ℕ → 𝟚
    α = force-decreasing β

    x : ℕ∞
    x = (α , force-decreasing-is-decreasing β)

    d : is-decidable (Σ n ꞉ ℕ , x ＝ ι n)
    d = ℓ x

    a : (Σ n ꞉ ℕ , x ＝ ι n) → A
    a (n , p) = inl (force-decreasing-is-not-much-smaller β n c)
      where
        c : α n ＝ ₀
        c = α n       ＝⟨ ap (λ - → ι - n) p ⟩
            ι (ι n) n ＝⟨ ℕ-to-ℕ∞-diagonal₀ n ⟩
            ₀         ∎

    b : (¬ (Σ n ꞉ ℕ , x ＝ ι n)) → A
    b u = inr g
      where
        v : (n : ℕ) → x ＝ ι n → 𝟘
        v = curry u

        g : (n : ℕ) → β n ＝ ₁
        g n = ≤₂-criterion-converse (force-decreasing-is-smaller β n) e
          where
            c : x ＝ ι n → 𝟘
            c = v n

            l : x ＝ ∞
            l = not-finite-is-∞ fe₀ v

            e : α n ＝ ₁
            e = ap (λ - → ι - n) l

    γ : A
    γ = cases a b d

compact-ℕ-gives-LPO : is-compact ℕ → LPO
compact-ℕ-gives-LPO κ x = γ
  where
    A = is-decidable (Σ n ꞉ ℕ , x ＝ ι n)

    β : ℕ → 𝟚
    β = ι x

    d : (Σ n ꞉ ℕ , β n ＝ ₀) + (Π n ꞉ ℕ , β n ＝ ₁)
    d = κ β

    a : (Σ n ꞉ ℕ , β n ＝ ₀) → A
    a (n , p) = inl (pr₁ g , pr₂(pr₂ g))
      where
        g : Σ m ꞉ ℕ , (m ≤ n) × (x ＝ ι m)
        g = ℕ-to-ℕ∞-lemma fe₀ x n p

    b : (Π n ꞉ ℕ , β n ＝ ₁) → A
    b φ = inr g
      where
        ψ : ¬ (Σ n ꞉ ℕ , β n ＝ ₀)
        ψ = uncurry (λ n → equal-₁-different-from-₀(φ n))

        f : (Σ n ꞉ ℕ , x ＝ ι n) → Σ n ꞉ ℕ , β n ＝ ₀
        f (n , p) = (n , (ap (λ - → ι - n) p ∙ ℕ-to-ℕ∞-diagonal₀ n))
          where
           l : ι x n ＝ ι (ι n) n
           l = ap (λ - → ι - n) p

        g : ¬ (Σ n ꞉ ℕ , x ＝ ι n)
        g = contrapositive f ψ

    γ : is-decidable (Σ n ꞉ ℕ , x ＝ ι n)
    γ = cases a b d

\end{code}

Now, if LPO is false, that is, an empty type, then the function type

  LPO → ℕ

is isomorphic to the unit type 𝟙, and hence is compact. If LPO holds,
that is, LPO is equivalent to 𝟙 because it is a univalent proposition,
then the function type LPO → ℕ is isomorphic to ℕ, and hence the type
LPO → ℕ is again compact by LPO. So in any case we have that the type
LPO → ℕ is compact. However, LPO is an undecided proposition in our
type theory, so that the nature of the function type LPO → ℕ is
undecided. Nevertheless, we can show that it is compact, without
knowing whether LPO holds or not!

\begin{code}

open import TypeTopology.PropTychonoff

[LPO→ℕ]-is-compact∙ : is-compact∙ (LPO → ℕ)
[LPO→ℕ]-is-compact∙ = prop-tychonoff-corollary' fe LPO-is-prop f
 where
   f : LPO → is-compact∙ ℕ
   f lpo = compact-pointed-types-are-compact∙ (LPO-gives-compact-ℕ lpo) 0

[LPO→ℕ]-is-compact : is-compact (LPO → ℕ)
[LPO→ℕ]-is-compact = compact∙-types-are-compact [LPO→ℕ]-is-compact∙

[LPO→ℕ]-is-Compact : is-Compact (LPO → ℕ) {𝓤}
[LPO→ℕ]-is-Compact = compact-types-are-Compact [LPO→ℕ]-is-compact

\end{code}

However, we cannot prove that the function type LPO→ℕ is discrete, as
otherwise we would be able to decide the negation of LPO (added 14th
Feb 2020):

\begin{code}

open import Naturals.Properties
open import UF.DiscreteAndSeparated

[LPO→ℕ]-discrete-gives-¬LPO-decidable : is-discrete (LPO → ℕ) → is-decidable (¬ LPO)
[LPO→ℕ]-discrete-gives-¬LPO-decidable =
  discrete-exponential-has-decidable-emptiness-of-exponent
   fe₀
   (1 , 0 , positive-not-zero 0)

\end{code}

Another condition equivalent to LPO is that the obvious
embedding ι𝟙 : ℕ + 𝟙 → ℕ∞ has a section:

\begin{code}

ι𝟙-has-section-gives-LPO : (Σ s ꞉ (ℕ∞ → ℕ + 𝟙) , ι𝟙 ∘ s ∼ id) → LPO
ι𝟙-has-section-gives-LPO (s , ε) u = ψ (s u) refl
 where
  ψ : (z : ℕ + 𝟙) → s u ＝ z → is-decidable (Σ n ꞉ ℕ , u ＝ ι n)
  ψ (inl n) p = inl (n , (u        ＝⟨ (ε u) ⁻¹ ⟩
                          ι𝟙 (s u) ＝⟨ ap ι𝟙 p ⟩
                          ι n      ∎))
  ψ (inr *) p = inr γ
   where
    γ : ¬ (Σ n ꞉ ℕ , u ＝ ι n)
    γ (n , q) = ∞-is-not-finite n (∞        ＝⟨ (ap ι𝟙 p)⁻¹ ⟩
                                   ι𝟙 (s u) ＝⟨ ε u ⟩
                                   u        ＝⟨ q ⟩
                                   ι n      ∎)

ι𝟙-is-equiv-gives-LPO : is-equiv ι𝟙 → LPO
ι𝟙-is-equiv-gives-LPO i = ι𝟙-has-section-gives-LPO (equivs-have-sections ι𝟙 i)

ι𝟙-inverse : (u : ℕ∞) → is-decidable (Σ n ꞉ ℕ , u ＝ ι n) → ℕ + 𝟙 {𝓤₀}
ι𝟙-inverse .(ι n) (inl (n , refl)) = inl n
ι𝟙-inverse u (inr g) = inr ⋆

LPO-gives-has-section-ι𝟙 : LPO → Σ s ꞉ (ℕ∞ → ℕ + 𝟙) , ι𝟙 ∘ s ∼ id
LPO-gives-has-section-ι𝟙 lpo = s , ε
 where
  s : ℕ∞ → ℕ + 𝟙
  s u = ι𝟙-inverse u (lpo u)

  φ : (u : ℕ∞) (d : is-decidable (Σ n ꞉ ℕ , u ＝ ι n)) → ι𝟙 (ι𝟙-inverse u d) ＝ u
  φ .(ι n) (inl (n , refl)) = refl
  φ u (inr g) = (not-finite-is-∞ fe₀ (curry g))⁻¹

  ε : ι𝟙 ∘ s ∼ id
  ε u = φ u (lpo u)

LPO-gives-ι𝟙-is-equiv : LPO → is-equiv ι𝟙
LPO-gives-ι𝟙-is-equiv lpo = embeddings-with-sections-are-equivs ι𝟙
                             (ι𝟙-is-embedding fe₀)
                             (LPO-gives-has-section-ι𝟙 lpo)
\end{code}
