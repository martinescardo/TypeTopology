Martin Escardo, August 2026

Discrete and compact interpretations of the Brouwer ordinal codes, and
a dense embedding of the former into the latter.

This is the analogue, for the Brouwer codes B of the module
Ordinals.BrouwerCodes, of what the module
Ordinals.BrouwerCodesVariationInterpretations does for the ordinal
expressions OE considered there.

The compact interpretation Κ is the interpretation called ⟦_⟧₁ in the
module Ordinals.BrouwerCodesInterpretations, repeated here to avoid
the unnecessary assumptions of univalence, propositional truncation
and set replacement.

The discrete interpretation Δ agrees with Κ at Z and at S, and differs
from it only at L, where the successor sum ∑₁ stands in place of the
squashed sum ∑¹. This difference makes the map ∑↑ into a dense
embedding.

The other discrete interpretation of the Brouwer codes, called ⟦_⟧₃ in
the module Ordinals.BrouwerCodesInterpretations, cannot play the role
of Δ here because it fails to give rise to a dense embedding.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module Ordinals.BrouwerCodesDiscreteAndCompactInterpretations
        (fe : FunExt)
       where

open import MLTT.Two-Properties
open import Notation.CanonicalMap hiding (ι)
open import Ordinals.Arithmetic fe
open import Ordinals.BrouwerCodes
open import Ordinals.ChurchEncoding using (B-ε₀)
open import Ordinals.Closure fe
open import Ordinals.Equivalence
open import Ordinals.InfProperty
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import Taboos.LPO
open import Taboos.WLPO
open import TypeTopology.CompactTypes
open import TypeTopology.Density
open import TypeTopology.LimitPoints
open import TypeTopology.SigmaDiscrete
open import TypeTopology.SquashedCantor fe hiding (Κ)
open import TypeTopology.SquashedSum fe
open import TypeTopology.TotallySeparated
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.PairFun
open import UF.Retracts
open import UF.Subsingletons

private
 fe₀ : funext 𝓤₀ 𝓤₀
 fe₀ = fe 𝓤₀ 𝓤₀

\end{code}

In the following, ⟨ τ ⟩ denotes the underlying set of an ordinal τ, and
_≺⟨ τ ⟩_ denotes its underlying order.

We define and prove the following in this file, mimicking the file
Ordinals.BrouwerCodesVariationInterpretations.

\begin{code}

Κ                            : B → Ordᵀ
Κ-compact∙                   : (b : B) → is-compact∙ ⟨ Κ b ⟩
Κ-Cantor-retract             : (b : B) → retract ⟨ Κ b ⟩ of (ℕ → 𝟚)
Κ-is-totally-separated       : (b : B) → is-totally-separated ⟨ Κ b ⟩

Δ                            : B → Ordᵀ
Δ-retract-of-ℕ               : (b : B) → retract ⟨ Δ b ⟩ of ℕ
Δ-is-discrete                : (b : B) → is-discrete ⟨ Δ b ⟩
Δ-is-trichotomous            : (b : B) → is-trichotomous [ Δ b ]

ι                            : {b : B} → ⟨ Δ b ⟩ → ⟨ Κ b ⟩
ι-is-dense                   : (b : B) → is-dense (ι {b})
ι-is-embedding               : (b : B) → is-embedding (ι {b})

ι-is-order-preserving        : (b : B) (x y : ⟨ Δ b ⟩)
                             →   x ≺⟨ Δ b ⟩   y
                             → ι x ≺⟨ Κ b ⟩ ι y

ι-is-order-reflecting        : (b : B) (x y : ⟨ Δ b ⟩)
                             → ι x ≺⟨ Κ b ⟩ ι y
                             →   x ≺⟨ Δ b ⟩   y

Κ-has-infs-of-complemented-subsets
                             : propext 𝓤₀
                             → (b : B) → has-infs-of-complemented-subsets (Κ b)

Κ-has-least-roots-of-complemented-subsets
                             : propext 𝓤₀
                             → (b : B)
                             → has-least-roots-of-complemented-subsets (Κ b)

ℓ                            : (b : B) → ⟨ Δ b ⟩ → 𝟚
ℓ-isolated                   : (b : B) (x : ⟨ Δ b ⟩)
                             → ℓ b x ＝ ₀ → is-isolated (ι {b} x)
ℓ-limit                      : (b : B) (x : ⟨ Δ b ⟩)
                             → ℓ b x ＝ ₁ → is-limit-point (ι {b} x)
ℓ-limit⁺                     : (b : B) (x : ⟨ Δ b ⟩)
                             → ℓ b x ＝ ₁ → is-limit-point⁺ (ι {b} x)

isolatedness-decision        : (b : B) (x : ⟨ Δ b ⟩)
                             → is-isolated (ι {b} x)
                             + is-limit-point (ι {b} x)

isolatedness-decision'       : ¬ WLPO
                             → (b : B) (x : ⟨ Δ b ⟩)
                             → is-decidable (is-isolated (ι {b} x))

ι-is-equiv-gives-LPO         : ((b : B) → is-equiv (ι {b})) → LPO
LPO-gives-ι-is-equiv         : LPO → (b : B) → is-equiv (ι {b})
ι-is-equiv-iff-LPO           : ((b : B) → is-equiv (ι {b})) ↔ LPO

ι-has-section-gives-Κ-discrete
                             : (b : B)
                             → has-section (ι {b})
                             → is-discrete ⟨ Κ b ⟩

ι-is-equiv-gives-Κ-discrete  : (b : B)
                             → is-equiv (ι {b})
                             → is-discrete ⟨ Κ b ⟩

LPO-gives-Κ-discrete         : LPO → (b : B) → is-discrete ⟨ Κ b ⟩
Κ-discrete-gives-WLPO        : ((b : B) → is-discrete ⟨ Κ b ⟩) → WLPO
Δ-compact-gives-LPO          : ((b : B) → is-compact ⟨ Δ b ⟩) → LPO
LPO-gives-Δ-compact          : LPO → (b : B) → is-compact ⟨ Δ b ⟩
Δ-compact-iff-LPO            : ((b : B) → is-compact ⟨ Δ b ⟩) ↔ LPO

Δ-least-roots-gives-LPO      : ((b : B)
                              → has-least-roots-of-complemented-subsets (Δ b))
                             → LPO

LPO-gives-Δ-least-roots      : propext 𝓤₀
                             → LPO
                             → (b : B)
                             → has-least-roots-of-complemented-subsets (Δ b)

Δ-least-roots-iff-LPO        : propext 𝓤₀
                             → ((b : B)
                              → has-least-roots-of-complemented-subsets (Δ b))
                             ↔ LPO

Κ-of-ε₀-code                 : Ordᵀ
Κ-of-ε₀-code-is-compact∙     : is-compact∙ ⟨ Κ-of-ε₀-code ⟩

\end{code}

We first define the compact interpretation. The pointedness of the
compactness is crucial in the proof by induction, via the indirect use
of micro-tychonoff in Σ¹, because a version of micro-tychonoff without
pointedness implies excluded middle. This is why the base case is 𝟙ᵒ
rather than 𝟘ᵒ.

\begin{code}

Κ Z     = 𝟙ᵒ
Κ (S b) = Κ b +ᵒ 𝟙ᵒ
Κ (L b) = ∑¹ (Κ ∘ b)

Κ-compact∙ Z     = 𝟙-is-compact∙
Κ-compact∙ (S b) = Σ-is-compact∙
                    𝟙+𝟙-is-compact∙
                    (dep-cases (λ _ → Κ-compact∙ b) (λ _ → 𝟙-is-compact∙))
Κ-compact∙ (L b) = Σ¹-compact∙ (λ n → ⟨ Κ (b n) ⟩) (λ n → Κ-compact∙ (b n))

\end{code}

They are moreover retracts of the Cantor type, and hence totally
separated.

\begin{code}

Κ-Cantor-retract Z     = 𝟙-retract-of-Cantor
Κ-Cantor-retract (S b) = +-retract-of-Cantor (Κ b) 𝟙ᵒ
                          (Κ-Cantor-retract b) 𝟙-retract-of-Cantor
Κ-Cantor-retract (L b) = Σ¹-Cantor-retract
                          (λ n → ⟨ Κ (b n) ⟩) (λ i → Κ-Cantor-retract (b i))

Κ-is-totally-separated b = retract-of-totally-separated
                            (Κ-Cantor-retract b)
                            (Cantor-is-totally-separated fe₀)

\end{code}

We now define the discrete interpretation, which differs from the
compact one only at the limit constructor.

\begin{code}

Δ Z     = 𝟙ᵒ
Δ (S b) = Δ b +ᵒ 𝟙ᵒ
Δ (L b) = ∑₁ (Δ ∘ b)

Δ-retract-of-ℕ Z     = 𝟙-retract-of-ℕ
Δ-retract-of-ℕ (S b) = Σ-retract-of-ℕ
                        retract-𝟙+𝟙-of-ℕ
                        (dep-cases (λ _ → Δ-retract-of-ℕ b)
                                   (λ _ → 𝟙-retract-of-ℕ))
Δ-retract-of-ℕ (L b) = Σ₁-ℕ-retract (λ i → Δ-retract-of-ℕ (b i))

Δ-is-discrete Z     = 𝟙-is-discrete
Δ-is-discrete (S b) = Σ-is-discrete
                       (+-is-discrete 𝟙-is-discrete 𝟙-is-discrete)
                       (dep-cases (λ _ → Δ-is-discrete b) (λ _ → 𝟙-is-discrete))
Δ-is-discrete (L b) = Σ₁-is-discrete
                       (λ n → ⟨ Δ (b n) ⟩) (λ i → Δ-is-discrete (b i))

\end{code}

Notice that we could have proved that the Δ-ordinals are discrete using
the retraction above, as discrete types are closed under retracts.

Hence the compactness of any infinite discrete ordinal is a
constructive taboo, logically equivalent to Bishop's LPO.

The discrete ordinals are moreover trichotomous, by ∑₁-is-trichotomous
at the limit constructor, which is available for ∑₁ but not for ∑¹, as
discussed in the module Ordinals.ToppedArithmetic.

\begin{code}

Δ-is-trichotomous Z     = 𝟙ₒ-is-trichotomous
Δ-is-trichotomous (S b) = +ᵒ-is-trichotomous (Δ b) 𝟙ᵒ
                           (Δ-is-trichotomous b)
                           𝟙ₒ-is-trichotomous
Δ-is-trichotomous (L b) = ∑₁-is-trichotomous (Δ ∘ b)
                           (λ i → Δ-is-trichotomous (b i))

\end{code}

There is a dense embedding ι of the discrete ordinals into the compact
ones, where density means that the complement of the image of the
embedding is empty. Moreover, it is order preserving and reflecting.

\begin{code}

ι {Z}   = id
ι {S b} = pair-fun id (dep-cases (λ _ → ι {b}) (λ _ → id))
ι {L b} = ∑↑ (λ n → Δ (b n)) (λ n → Κ (b n)) (λ n → ι {b n})

ι-is-dense Z     = id-is-dense
ι-is-dense (S b) = pair-fun-dense
                    id
                    (dep-cases (λ _ → ι {b}) (λ _ → id))
                    id-is-dense
                    (dep-cases (λ _ → ι-is-dense b) (λ _ → id-is-dense))
ι-is-dense (L b) = ∑↑-dense
                    (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                    (λ i → ι-is-dense (b i))

ι-is-embedding Z     = id-is-embedding
ι-is-embedding (S b) = pair-fun-is-embedding
                        id
                        (dep-cases (λ _ → ι {b}) (λ _ → id))
                        id-is-embedding
                        (dep-cases (λ _ → ι-is-embedding b)
                                   (λ _ → id-is-embedding))
ι-is-embedding (L b) = ∑↑-embedding
                        (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                        (λ i → ι-is-embedding (b i))

ι-is-order-preserving Z     = λ x y → id
ι-is-order-preserving (S b) = pair-fun-is-order-preserving
                               𝟚ᵒ
                               𝟚ᵒ
                               (cases (λ _ → Δ b) (λ _ → 𝟙ᵒ))
                               (cases (λ _ → Κ b) (λ _ → 𝟙ᵒ))
                               id
                               (dep-cases (λ _ → ι {b}) (λ _ → id))
                               (λ x y l → l)
                               (dep-cases (λ _ → ι-is-order-preserving b)
                                          (λ _ x y l → l))
ι-is-order-preserving (L b) = ∑↑-is-order-preserving
                               (Δ ∘ b)
                               (Κ ∘ b)
                               (λ n → ι {b n})
                               (λ i → ι-is-order-preserving (b i))

ι-is-order-reflecting Z     = λ x y → id
ι-is-order-reflecting (S b) = pair-fun-is-order-reflecting
                               𝟚ᵒ
                               𝟚ᵒ
                               (cases (λ _ → Δ b) (λ _ → 𝟙ᵒ))
                               (cases (λ _ → Κ b) (λ _ → 𝟙ᵒ))
                               id
                               (dep-cases (λ _ → ι {b}) (λ _ → id))
                               (λ x y l → l)
                               id-is-embedding
                               (dep-cases (λ _ → ι-is-order-reflecting b)
                                          (λ _ x y l → l))
ι-is-order-reflecting (L b) = ∑↑-is-order-reflecting
                               (Δ ∘ b)
                               (Κ ∘ b)
                               (λ n → ι {b n})
                               (λ i → ι-is-order-reflecting (b i))

\end{code}

A boolean valued function on the discrete ordinal decides which points
of the image of ι are isolated and which are limit points. The added
top point of ∑₁ is the only source of limit points, because it is the
one that sits over ∞.

The two limit-point results have three clauses rather than five,
because the cases in which ℓ takes the value ₀ are refuted by their
hypothesis, which asks for the value ₁.

\begin{code}

ℓ Z     ⋆           = ₀
ℓ (S b) (inl ⋆ , x) = ℓ b x
ℓ (S b) (inr ⋆ , ⋆) = ₀
ℓ (L b) (inl n , u) = ℓ (b n) (u (n , refl))
ℓ (L b) (inr ⋆ , u) = ₁

ℓ-isolated Z     ⋆           p = 𝟙-is-discrete ⋆
ℓ-isolated (S b) (inl ⋆ , x) p = Σ-isolated
                                  (inl-is-isolated ⋆ (𝟙-is-discrete ⋆))
                                  (ℓ-isolated b x p)
ℓ-isolated (S b) (inr ⋆ , ⋆) p = Σ-isolated
                                  (inr-is-isolated ⋆ (𝟙-is-discrete ⋆))
                                  (𝟙-is-discrete ⋆)
ℓ-isolated (L b) (inl n , u) p = ∑↑-preserves-isolatedness
                                  (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                                  n
                                  u
                                  (ℓ-isolated (b n) (u (n , refl)) p)

ℓ-limit (S b) (inl ⋆ , x) p i = ℓ-limit b x p
                                 (Σ-isolated-right
                                   (underlying-type-is-setᵀ fe 𝟚ᵒ) i)
ℓ-limit (L b) (inl n , u) p i = ℓ-limit (b n) (u (n , refl)) p
                                 (∑↑-reflects-isolatedness
                                   (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                                   n
                                   u
                                   i)
ℓ-limit (L b) (inr ⋆ , u) p   = ∑↑-limit-point
                                 (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                                 (λ i → Κ-compact∙ (b i))
                                 u

ℓ-limit⁺ (S b) (inl ⋆ , x) p i = ℓ-limit⁺ b x p
                                  (Σ-weakly-isolated-right
                                    (underlying-type-is-setᵀ fe 𝟚ᵒ) i)
ℓ-limit⁺ (L b) (inl n , u) p i = ℓ-limit⁺ (b n) (u (n , refl)) p
                                  (∑↑-reflects-weak-isolatedness
                                    (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                                    n
                                    u
                                    i)
ℓ-limit⁺ (L b) (inr ⋆ , u) p   = ∑↑-limit-point⁺
                                  (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                                  (λ i → Κ-compact∙ (b i))
                                  u

\end{code}

Every point of the image of ι is isolated or a limit point, and if we
assume that WLPO fails, isolatedness of such a point is decidable. The
assumption is a weak continuity principle, being equivalent to one, as
shown in the module TypeTopology.DecidabilityOfNonContinuity.

\begin{code}

isolatedness-decision b x = 𝟚-equality-cases
                             (λ (p : ℓ b x ＝ ₀) → inl (ℓ-isolated b x p))
                             (λ (p : ℓ b x ＝ ₁) → inr (ℓ-limit b x p))

isolatedness-decision' f b x =
 Cases (isolatedness-decision b x)
  inl
  (λ (g : is-isolated (ι {b} x) → WLPO) → inr (contrapositive g f))

\end{code}

The code L (λ n → Z) plays the role that a primitive code for ω + 1
plays in other ordinal notations, its discrete interpretation being
ℕ + 𝟙 and its compact one ℕ∞.

\begin{code}

ι-is-equiv-gives-LPO f = ι𝟙-is-equiv-gives-LPO
                          (Σ↑-𝟙-is-equiv-gives-ι𝟙-is-equiv (f (L (λ _ → Z))))

LPO-gives-ι-is-equiv lpo Z     = id-is-equiv 𝟙
LPO-gives-ι-is-equiv lpo (S b) = pair-fun-is-equiv
                                  id
                                  (dep-cases (λ _ → ι {b}) (λ _ → id))
                                  (id-is-equiv (𝟙 + 𝟙))
                                  (dep-cases
                                    (λ _ → LPO-gives-ι-is-equiv lpo b)
                                    (λ _ → id-is-equiv 𝟙))
LPO-gives-ι-is-equiv lpo (L b) = ∑↑-is-equiv
                                  (LPO-gives-ι𝟙-is-equiv fe₀ lpo)
                                  (Δ ∘ b) (Κ ∘ b) (λ n → ι {b n})
                                  (λ i → LPO-gives-ι-is-equiv lpo (b i))

ι-is-equiv-iff-LPO = ι-is-equiv-gives-LPO , LPO-gives-ι-is-equiv

\end{code}

Discreteness of the compact interpretation sits between LPO and WLPO.
Whether the gap between LPO-gives-Κ-discrete and Κ-discrete-gives-WLPO
can be closed is open, and it is the same question as the one left
open at the end of the module Ordinals.InductiveRecursiveCodesInterpretations.

In the other direction there is no gap. Compactness of the discrete
interpretation is exactly LPO, and the code L (λ _ → Z) alone
witnesses this in one direction.

\begin{code}

ι-has-section-gives-Κ-discrete b (θ , ιθ) = lc-maps-reflect-discreteness θ
                                             (sections-are-lc θ (ι {b} , ιθ))
                                             (Δ-is-discrete b)

ι-is-equiv-gives-Κ-discrete b e = ι-has-section-gives-Κ-discrete b
                                   (equivs-have-sections (ι {b}) e)

LPO-gives-Κ-discrete lpo b = ι-is-equiv-gives-Κ-discrete b
                              (LPO-gives-ι-is-equiv lpo b)

Κ-discrete-gives-WLPO f = ℕ∞-discrete-gives-WLPO
                           (retract-is-discrete
                             ℕ∞-retract-of-Σ¹-𝟙
                             (f (L (λ _ → Z))))

Δ-compact-gives-LPO κ = compact-ℕ-gives-LPO fe₀
                         (retract-is-compact
                           (retracts-compose
                             ℕ+𝟙-retract-of-Σ₁-𝟙
                             (cases id (λ _ → 0) , inl , (λ n → refl)))
                           (κ (L (λ _ → Z))))

LPO-gives-Δ-compact lpo b = retract-is-compact
                             (Δ-retract-of-ℕ b)
                             (LPO-gives-compact-ℕ fe₀ lpo)

Δ-compact-iff-LPO = Δ-compact-gives-LPO , LPO-gives-Δ-compact

\end{code}

As discussed in the module Ordinals.Closure, propositional
extensionality in the following construction is not strictly needed
but makes our life much easier.

\begin{code}

Κ-has-infs-of-complemented-subsets pe Z     =
 𝟙ᵒ-has-infs-of-complemented-subsets
Κ-has-infs-of-complemented-subsets pe (S b) =
 ∑-has-infs-of-complemented-subsets pe
  𝟚ᵒ
  (cases (λ _ → Κ b) (λ _ → 𝟙ᵒ))
  𝟚ᵒ-has-infs-of-complemented-subsets
  (dep-cases
    (λ _ → Κ-has-infs-of-complemented-subsets pe b)
    (λ _ → 𝟙ᵒ-has-infs-of-complemented-subsets))
Κ-has-infs-of-complemented-subsets pe (L b) =
 ∑¹-has-infs-of-complemented-subsets
  pe
  (Κ ∘ b)
  (λ i → Κ-has-infs-of-complemented-subsets pe (b i))

\end{code}

Added 2nd September 2026.

Hence every non-empty complemented subset of the compact
interpretation has a least element. For the discrete interpretation
this is exactly LPO, and the code L (λ _ → Z) alone witnesses one
direction, its discrete interpretation being ω + 1.

\begin{code}

Κ-has-least-roots-of-complemented-subsets pe b =
 has-inf-gives-least-roots
  (underlying-weak-order (Κ b))
  (Κ-has-infs-of-complemented-subsets pe b)

Δ𝟙-least-roots-gives-LPO
 : has-least-roots-of-complemented-subsets (Δ (L (λ _ → Z))) → LPO
Δ𝟙-least-roots-gives-LPO h
 = succₒ-ω-least-roots-gives-LPO
    (≃ₒ-gives-has-least-roots
      [ ∑₁ (λ _ → 𝟙ᵒ) ]
      [ succₒ ω ]
      ∑₁-of-𝟙ᵒ
      h)

Δ-least-roots-gives-LPO h = Δ𝟙-least-roots-gives-LPO (h (L (λ _ → Z)))

LPO-gives-Δ-least-roots pe lpo b = ≃ₒ-gives-has-least-roots
                                    [ Κ b ]
                                    [ Δ b ]
                                    (≃ₒ-sym [ Δ b ] [ Κ b ] 𝕚)
                                    (Κ-has-least-roots-of-complemented-subsets
                                      pe b)
 where
  𝕚 : [ Δ b ] ≃ₒ [ Κ b ]
  𝕚 = ι {b} ,
      order-preserving-reflecting-equivs-are-order-equivs
       [ Δ b ] [ Κ b ] (ι {b})
       (LPO-gives-ι-is-equiv lpo b)
       (ι-is-order-preserving b)
       (ι-is-order-reflecting b)

Δ-least-roots-iff-LPO pe = Δ-least-roots-gives-LPO ,
                           LPO-gives-Δ-least-roots pe

\end{code}

End of addition.

As an example, the compact interpretation can be applied directly to a
Brouwer code for ε₀.

\begin{code}

Κ-of-ε₀-code = Κ B-ε₀

Κ-of-ε₀-code-is-compact∙ = Κ-compact∙ B-ε₀

\end{code}

We can go much higher using the work of Setzer, Hancock and others.
