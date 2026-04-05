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

module Taboos.LPO where

open import CoNaturals.Type
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

LPO : 𝓤₀ ̇
LPO = (x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , x ＝ ι n)

\end{code}

Added 10th September 2024. In retrospect, it would have been better if
we had equivalently defined

  LPO = (x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , ι n ＝ x)

because we have

  fiber ι x = Σ n ꞉ ℕ , ι n ＝ x

by definition and ι is an embedding, so that e.g. the following
wouldn't require a proof given our definition of embedding.

End of addition.

\begin{code}

LPO-is-prop : funext₀ → is-prop LPO
LPO-is-prop fe = Π-is-prop fe f
 where
  a : (x : ℕ∞) → is-prop (Σ n ꞉ ℕ , x ＝ ι n)
  a x (n , p) (m , q) = to-Σ-＝ (ℕ-to-ℕ∞-lc (p ⁻¹ ∙ q) , ℕ∞-is-set fe _ _)

  f : (x : ℕ∞) → is-prop (is-decidable (Σ n ꞉ ℕ , x ＝ ι n))
  f x = decidability-of-prop-is-prop fe (a x)

\end{code}

We now show that LPO is logically equivalent to its traditional
formulation by Bishop, which here amounts the compactness of ℕ.
However, the traditional formulation is not a univalent proposition in
general, and not type equivalent (in the sense of UF) to our
formulation.

\begin{code}

LPO-gives-compact-ℕ : funext₀ → LPO → is-compact ℕ
LPO-gives-compact-ℕ fe ℓ β = γ
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

  b : ¬ (Σ n ꞉ ℕ , x ＝ ι n) → A
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
      l = not-finite-is-∞ fe v

      e : α n ＝ ₁
      e = ap (λ - → ι - n) l

  γ : A
  γ = cases a b d

compact-ℕ-gives-LPO : funext₀ → is-compact ℕ → LPO
compact-ℕ-gives-LPO fe κ x = γ
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
    g = ℕ-to-ℕ∞-lemma fe x n p

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

[LPO→ℕ]-is-compact∙ : funext₀ → is-compact∙ (LPO → ℕ)
[LPO→ℕ]-is-compact∙ fe = prop-tychonoff-corollary' fe (LPO-is-prop fe) f
 where
   f : LPO → is-compact∙ ℕ
   f lpo = compact-pointed-types-are-compact∙ (LPO-gives-compact-ℕ fe lpo) 0

[LPO→ℕ]-is-compact : funext₀ → is-compact (LPO → ℕ)
[LPO→ℕ]-is-compact fe = compact∙-types-are-compact ([LPO→ℕ]-is-compact∙ fe)

[LPO→ℕ]-is-Compact : funext₀ → is-Compact (LPO → ℕ) {𝓤}
[LPO→ℕ]-is-Compact fe = compact-types-are-Compact ([LPO→ℕ]-is-compact fe)

\end{code}

However, we cannot prove that the function type LPO→ℕ is discrete, as
otherwise we would be able to decide the negation of LPO (added 14th
Feb 2020):

\begin{code}

open import Naturals.Properties
open import UF.DiscreteAndSeparated

[LPO→ℕ]-discrete-gives-¬LPO-decidable
 : funext₀
 → is-discrete (LPO → ℕ)
 → is-decidable (¬ LPO)
[LPO→ℕ]-discrete-gives-¬LPO-decidable fe =
  discrete-exponential-has-decidable-emptiness-of-exponent
   fe
   ((1 , 0) , positive-not-zero 0)

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

LPO-gives-has-section-ι𝟙 : funext₀ → LPO → Σ s ꞉ (ℕ∞ → ℕ + 𝟙) , ι𝟙 ∘ s ∼ id
LPO-gives-has-section-ι𝟙 fe lpo = s , ε
 where
  s : ℕ∞ → ℕ + 𝟙
  s u = ι𝟙-inverse u (lpo u)

  φ : (u : ℕ∞) (d : is-decidable (Σ n ꞉ ℕ , u ＝ ι n)) → ι𝟙 (ι𝟙-inverse u d) ＝ u
  φ .(ι n) (inl (n , refl)) = refl
  φ u (inr g) = (not-finite-is-∞ fe (curry g))⁻¹

  ε : ι𝟙 ∘ s ∼ id
  ε u = φ u (lpo u)

LPO-gives-ι𝟙-is-equiv : funext₀ → LPO → is-equiv ι𝟙
LPO-gives-ι𝟙-is-equiv fe lpo = embeddings-with-sections-are-equivs ι𝟙
                               (ι𝟙-is-embedding fe)
                               (LPO-gives-has-section-ι𝟙 fe lpo)
\end{code}

Added 3rd September 2024.

\begin{code}

open import Taboos.WLPO

LPO-gives-WLPO : funext₀ → LPO → WLPO
LPO-gives-WLPO fe lpo u =
 Cases (lpo u)
  (λ (n , p) → inr (λ {refl → ∞-is-not-finite n p}))
  (λ ν → inl (not-finite-is-∞ fe (λ n p → ν (n , p))))

¬WLPO-gives-¬LPO : funext₀ → ¬ WLPO → ¬ LPO
¬WLPO-gives-¬LPO fe = contrapositive (LPO-gives-WLPO fe)

\end{code}

Added 1 February 2025 by Tom de Jong.
The following type is logically equivalent to LPO but it should be noted that it
is not a proposition.

\begin{code}

LPO-variation : 𝓤₀ ̇
LPO-variation = (α : ℕ → 𝟚) → is-decidable (Σ n ꞉ ℕ , α n ＝ ₀)

LPO-variation-implies-LPO : funext₀ → LPO-variation → LPO
LPO-variation-implies-LPO fe lpovar = compact-ℕ-gives-LPO fe I
 where
  I : is-compact ℕ
  I α = κ (lpovar α)
   where
    κ : is-decidable (Σ n ꞉ ℕ , α n ＝ ₀)
      → (Σ n ꞉ ℕ , α n ＝ ₀) + (Π n ꞉ ℕ , α n ＝ ₁)
    κ (inl r) = inl r
    κ (inr ν) = inr (λ n → 𝟚-equality-cases
                            (λ (e : α n ＝ ₀) → 𝟘-elim (ν (n , e)))
                            id)

LPO-implies-LPO-variation : funext₀ → LPO → LPO-variation
LPO-implies-LPO-variation fe lpo α = I (LPO-gives-compact-ℕ fe lpo α)
 where
  I : (Σ n ꞉ ℕ , α n ＝ ₀) + (Π n ꞉ ℕ , α n ＝ ₁)
    → is-decidable (Σ n ꞉ ℕ , α n ＝ ₀)
  I (inl r) = inl r
  I (inr ν) = inr (Π-not-implies-not-Σ
                    (λ n (e : α n ＝ ₀) → 𝟘-elim
                                           (zero-is-not-one (e ⁻¹ ∙ ν n))))

\end{code}

Added 3rd December by Martin Escardo.

\begin{code}

ℕ-compact-criterion : funext₀
                    → ((x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , x ⊑ n))
                    → is-compact ℕ
ℕ-compact-criterion fe ℓ β = γ
 where
  A = (Σ n ꞉ ℕ , β n ＝ ₀) + (Π n ꞉ ℕ , β n ＝ ₁)

  α : ℕ → 𝟚
  α = force-decreasing β

  x : ℕ∞
  x = (α , force-decreasing-is-decreasing β)

  d : is-decidable (Σ n ꞉ ℕ , x ⊑ n)
  d = ℓ x

  a : (Σ n ꞉ ℕ , x ⊑ n) → A
  a (n , p) = inl (force-decreasing-is-not-much-smaller β n p)

  b : ¬ (Σ n ꞉ ℕ , ι x n ＝ ₀) → A
  b ν = inr f
   where
    f : (n : ℕ) → β n ＝ ₁
    f n = different-from-₀-equal-₁
           (λ (e : β n ＝ ₀)
                 → ν (n , ₀-smallest (force-decreasing-is-smaller β n) e))

  γ : A
  γ = cases a b d

LPO-criterion : funext₀
              → ((x : ℕ∞) → is-decidable (Σ n ꞉ ℕ , x ⊑ n))
              → LPO
LPO-criterion fe ℓ = compact-ℕ-gives-LPO fe (ℕ-compact-criterion fe ℓ)

\end{code}

TODO. Add the converse of LPO-criterion.
