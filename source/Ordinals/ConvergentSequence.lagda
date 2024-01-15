Martin Escardo 2018.

Classically, the ordinals ω +ₒ 𝟙ₒ and ℕ∞ₒ are equal.  Constructively,
we have (ω +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ, but the inequality in the other direction is
equivalent to LPO.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence
open import UF.FunExt
open import UF.UA-FunExt

module Ordinals.ConvergentSequence (ua : Univalence) where

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} =  fe 𝓤 𝓥

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Taboos.LPO fe
open import Naturals.Order
open import Ordinals.Arithmetic fe
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Equivalence
open import Ordinals.Underlying
open import CoNaturals.GenericConvergentSequence
open import UF.Equiv

ω+𝟙-is-⊴-ℕ∞ : (ω +ₒ 𝟙ₒ) ⊴ ℕ∞ₒ
ω+𝟙-is-⊴-ℕ∞ = ι𝟙 , i , p
 where
  i : (x : ⟨ ω +ₒ 𝟙ₒ ⟩) (y : ⟨ ℕ∞ₒ ⟩)
    → y ≺⟨ ℕ∞ₒ ⟩ ι𝟙 x
    → Σ x' ꞉ ⟨ ω +ₒ 𝟙ₒ ⟩ , (x' ≺⟨ ω +ₒ 𝟙ₒ ⟩ x) × (ι𝟙 x' ＝ y)
  i (inl m) y (n , r , l) = inl n , ⊏-gives-< n m l , (r ⁻¹)
  i (inr *) y (n , r , l) = inl n , * , (r ⁻¹)

  p : (x y : ⟨ ω +ₒ 𝟙ₒ ⟩)
    → x ≺⟨ ω +ₒ 𝟙ₒ ⟩ y
    → ι𝟙 x ≺⟨ ℕ∞ₒ ⟩ ι𝟙 y
  p (inl n) (inl m) l = ℕ-to-ℕ∞-order-preserving n m l
  p (inl n) (inr *) * = ∞-≺-largest n
  p (inr *) (inl m) l = 𝟘-elim l
  p (inr *) (inr *) l = 𝟘-elim l

ℕ∞-⊴-ω+𝟙-gives-LPO : ℕ∞ₒ ⊴ (ω +ₒ 𝟙ₒ) → LPO
ℕ∞-⊴-ω+𝟙-gives-LPO l = γ
 where
  b : (ω +ₒ 𝟙ₒ) ≃ₒ ℕ∞ₒ
  b = bisimilarity-gives-ordinal-equiv (ω +ₒ 𝟙ₒ) ℕ∞ₒ ω+𝟙-is-⊴-ℕ∞ l

  e : is-equiv ι𝟙
  e = pr₂ (≃ₒ-gives-≃ (ω +ₒ 𝟙ₒ) ℕ∞ₒ b)

  γ : LPO
  γ = ι𝟙-has-section-gives-LPO (equivs-have-sections ι𝟙 e)

LPO-gives-ℕ∞-⊴-ω+𝟙-gives : LPO → ℕ∞ₒ ⊴ (ω +ₒ 𝟙ₒ)
LPO-gives-ℕ∞-⊴-ω+𝟙-gives lpo = (λ x → ι𝟙-inverse x (lpo x)) ,
                                       (λ x → i x (lpo x)) ,
                                       (λ x y → p x y (lpo x) (lpo y))
 where
  ι𝟙-inverse-inl : (u : ℕ∞) (d : is-decidable (Σ n ꞉ ℕ , u ＝ ι n))
                     → (m : ℕ) → u ＝ ι m → ι𝟙-inverse u d ＝ inl m
  ι𝟙-inverse-inl . (ι n) (inl (n , refl)) m q = ap inl (ℕ-to-ℕ∞-lc q)
  ι𝟙-inverse-inl u          (inr g)          m q = 𝟘-elim (g (m , q))

  i : (x : ℕ∞) (d : is-decidable (Σ n ꞉ ℕ , x ＝ ι n)) (y : ℕ + 𝟙)
    → y ≺⟨ ω +ₒ 𝟙ₒ ⟩ ι𝟙-inverse x d
    → Σ x' ꞉ ℕ∞ , (x' ≺⟨ ℕ∞ₒ ⟩ x) × (ι𝟙-inverse x' (lpo x') ＝ y)
  i .(ι n) (inl (n , refl)) (inl m) l =
    ι m ,
    ℕ-to-ℕ∞-order-preserving m n l ,
    ι𝟙-inverse-inl (ι m) (lpo (ι m)) m refl
  i .(ι n) (inl (n , refl)) (inr *) l = 𝟘-elim l
  i x (inr g) (inl n) * =
    ι n ,
    transport (underlying-order ℕ∞ₒ (ι n))
              ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry g)) ⁻¹)
              (∞-≺-largest n) ,
    ι𝟙-inverse-inl (ι n) (lpo (ι n)) n refl
  i x (inr g) (inr *) l = 𝟘-elim l

  p : (x y : ℕ∞)  (d : is-decidable (Σ n ꞉ ℕ , x ＝ ι n))
      (e : is-decidable (Σ m ꞉ ℕ , y ＝ ι m))
    →  x ≺⟨ ℕ∞ₒ ⟩ y
    → ι𝟙-inverse x d ≺⟨ ω +ₒ 𝟙ₒ ⟩ ι𝟙-inverse y e
  p .(ι n) .(ι m) (inl (n , refl)) (inl (m , refl)) (k , r , l) =
   transport⁻¹ (λ - → - <ℕ m) (ℕ-to-ℕ∞-lc r) (⊏-gives-< k m l)
  p .(ι n) y (inl (n , refl)) (inr f) l = ⋆
  p x y (inr f) e (k , r , l) =
   𝟘-elim (∞-is-not-finite k ((not-finite-is-∞ (fe 𝓤₀ 𝓤₀) (curry f))⁻¹ ∙ r))

ℕ∞-is-successor₁ : LPO → ℕ∞ₒ ≃ₒ (ω +ₒ 𝟙ₒ)
ℕ∞-is-successor₁ lpo = bisimilarity-gives-ordinal-equiv
                        ℕ∞ₒ
                        (ω +ₒ 𝟙ₒ)
                        (LPO-gives-ℕ∞-⊴-ω+𝟙-gives lpo)
                        ω+𝟙-is-⊴-ℕ∞

ℕ∞-is-successor₂ : LPO → ℕ∞ ≃ (ℕ + 𝟙)
ℕ∞-is-successor₂ lpo = ≃ₒ-gives-≃ ℕ∞ₒ (ω +ₒ 𝟙ₒ) (ℕ∞-is-successor₁ lpo)

ℕ∞-is-successor₃ : LPO → ℕ∞ₒ ＝ (ω +ₒ 𝟙ₒ)
ℕ∞-is-successor₃ lpo = eqtoidₒ (ua 𝓤₀) fe' ℕ∞ₒ (ω +ₒ 𝟙ₒ) (ℕ∞-is-successor₁ lpo)

ℕ∞-is-successor₄ : LPO → ℕ∞ ＝ (ℕ + 𝟙)
ℕ∞-is-successor₄ lpo = eqtoid (ua 𝓤₀) ℕ∞ (ℕ + 𝟙) (ℕ∞-is-successor₂ lpo)

\end{code}
