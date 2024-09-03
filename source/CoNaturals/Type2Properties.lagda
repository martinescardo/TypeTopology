Martin Escardo, November 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CoNaturals.Type2Properties where

open import CoNaturals.Type hiding (is-finite')
open import CoNaturals.GenericConvergentSequence2
open import CoNaturals.Equivalence
open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Order hiding (max)
open import Naturals.Properties
open import Notation.CanonicalMap
open import Notation.Order
open import TypeTopology.Cantor
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.NotNotStablePropositions
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

private
 T = T-cantor
 ϕ = ϕ-cantor
 γ = γ-cantor

 instance
  Canonical-Map-ℕ-ℕ∞' : Canonical-Map ℕ ℕ∞'
  ι {{Canonical-Map-ℕ-ℕ∞'}} = ℕ-to-ℕ∞'

  canonical-map-ℕ∞'-ℕ→𝟚 : Canonical-Map ℕ∞' (ℕ → 𝟚)
  ι {{canonical-map-ℕ∞'-ℕ→𝟚}} = ℕ∞'-to-ℕ→𝟚


module _ (fe : funext₀) where

 open ℕ∞-equivalence fe

 trivial-fact : (i : ℕ) → ϕ (ℕ∞-to-ℕ→𝟚 ∞) i ＝ ₀
 trivial-fact 0        = refl
 trivial-fact (succ i) = refl

 Zero-preservation : ℕ∞-to-ℕ∞' Zero ＝ Zero'
 Zero-preservation = to-subtype-＝ (has-at-most-one-₁-is-prop fe) (dfunext fe I)
  where
   I : ϕ (ι Zero) ∼ ι Zero'
   I 0        = refl
   I (succ i) = trivial-fact 0

 Succ-preservation : (u : ℕ∞) → ℕ∞-to-ℕ∞' (Succ u) ＝ Succ' (ℕ∞-to-ℕ∞' u)
 Succ-preservation u@(α , d) = to-subtype-＝ (has-at-most-one-₁-is-prop fe) II
  where
   I : ϕ (ℕ∞-to-ℕ→𝟚 (Succ u)) ∼ cons ₀ (ι (ℕ∞-to-ℕ∞' u))
   I 0        = refl
   I (succ _) = refl

   II : ϕ (ℕ∞-to-ℕ→𝟚 (Succ u)) ＝ cons ₀ (ι (ℕ∞-to-ℕ∞' u))
   II = dfunext fe I

 ∞-preservation : ℕ∞-to-ℕ∞' ∞ ＝ ∞'
 ∞-preservation = to-subtype-＝ (has-at-most-one-₁-is-prop fe)
                   (dfunext fe trivial-fact)

 ∞-gives-∞' : (u : ℕ∞') → ℕ∞'-to-ℕ∞ u ＝ ∞ → u ＝ ∞'
 ∞-gives-∞' u e =
  u                       ＝⟨ II₀ ⟩
  ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ u) ＝⟨ II₁ ⟩
  ℕ∞-to-ℕ∞' ∞             ＝⟨ II₂ ⟩
  ∞'                      ∎
  where
   II₀ = (inverses-are-sections' ℕ∞-to-ℕ∞'-≃ u)⁻¹
   II₁ = ap ℕ∞-to-ℕ∞' e
   II₂ = ∞-preservation

 ∞'-gives-∞ : (u : ℕ∞) → ℕ∞-to-ℕ∞' u ＝ ∞' → u ＝ ∞
 ∞'-gives-∞ u e =
  u                       ＝⟨ (inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ u)⁻¹ ⟩
  ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' u) ＝⟨ ap ℕ∞'-to-ℕ∞ e ⟩
  ℕ∞'-to-ℕ∞ ∞'            ＝⟨ ap ℕ∞'-to-ℕ∞ (∞-preservation ⁻¹) ⟩
  ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' ∞) ＝⟨ inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ ∞ ⟩
  ∞                       ∎

 finite-preservation : (n : ℕ) → ℕ∞-to-ℕ∞' (ι n) ＝ ι n
 finite-preservation 0        = Zero-preservation
 finite-preservation (succ n) =
  ℕ∞-to-ℕ∞' (ι (succ n))  ＝⟨ refl ⟩
  ℕ∞-to-ℕ∞' (Succ (ι n))  ＝⟨ Succ-preservation (ι n) ⟩
  Succ' (ℕ∞-to-ℕ∞' (ι n)) ＝⟨ ap Succ' (finite-preservation n) ⟩
  Succ' (ι n)             ＝⟨ refl ⟩
  ι (succ n)              ∎

 finite-gives-finite' : (u : ℕ∞') → is-finite (ℕ∞'-to-ℕ∞ u) → is-finite' u
 finite-gives-finite' u (n , e) = III
  where
   I : is-finite' (ι n)
   I = ℕ-to-ℕ∞'-is-finite' n

   II = ι n                     ＝⟨ (finite-preservation n)⁻¹ ⟩
        ℕ∞-to-ℕ∞' (ι n)         ＝⟨ ap ℕ∞-to-ℕ∞' e ⟩
        ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ u) ＝⟨ inverses-are-sections' ℕ∞-to-ℕ∞'-≃ u ⟩
        u                       ∎

   III : is-finite' u
   III = transport is-finite' II I

 finite'-preservation : (n : ℕ) → ℕ∞'-to-ℕ∞ (ι n) ＝ ι n
 finite'-preservation n =
  ℕ∞'-to-ℕ∞ (ι n)             ＝⟨ I ⟩
  ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' (ι n)) ＝⟨ II ⟩
  ι n                         ∎
   where
    I  = (ap ℕ∞'-to-ℕ∞ (finite-preservation n))⁻¹
    II = inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ (ι n)

 ℕ-to-ℕ∞'-lc : left-cancellable ℕ-to-ℕ∞'
 ℕ-to-ℕ∞'-lc {n} {n'} e =
  ℕ-to-ℕ∞-lc (
   ι n              ＝⟨ (finite'-preservation n)⁻¹ ⟩
   ℕ∞'-to-ℕ∞ (ι n)  ＝⟨ ap ℕ∞'-to-ℕ∞ e ⟩
   ℕ∞'-to-ℕ∞ (ι n') ＝⟨ finite'-preservation n' ⟩
   ι n'             ∎)

 ℕ-to-ℕ∞'-diagonal : (n : ℕ) → ℕ∞'-to-ℕ→𝟚 (ι n) n ＝ ₁
 ℕ-to-ℕ∞'-diagonal 0        = refl
 ℕ-to-ℕ∞'-diagonal (succ n) = ℕ-to-ℕ∞'-diagonal n

 diagonal-lemma : (n : ℕ) (u : ℕ∞') → ℕ∞'-to-ℕ→𝟚 u n ＝ ₁ → u ＝ ι n
 diagonal-lemma n u p = ℕ∞'-to-ℕ→𝟚-lc fe (dfunext fe f)
  where
   I : ℕ∞'-to-ℕ→𝟚 u n ＝ ℕ∞'-to-ℕ→𝟚 (ι n) n
   I = ℕ∞'-to-ℕ→𝟚 u n     ＝⟨ p ⟩
       ₁                  ＝⟨ (ℕ-to-ℕ∞'-diagonal n)⁻¹ ⟩
       ℕ∞'-to-ℕ→𝟚 (ι n) n ∎

   II : (i : ℕ) → n ≠ i → ℕ∞'-to-ℕ→𝟚 u i ＝ ℕ∞'-to-ℕ→𝟚 (ι n) i
   II i ν =
    ℕ∞'-to-ℕ→𝟚 u i      ＝⟨ II₀ ⟩
    ₀                   ＝⟨ II₁ ⁻¹ ⟩
    ℕ∞'-to-ℕ→𝟚 (ι n) i  ∎
     where
      II₀ = different-from-₁-equal-₀
             (λ (e : ℕ∞'-to-ℕ→𝟚 u i ＝ ₁)
                   → ν (ℕ∞'-index-uniqueness u p e))

      II₁ = different-from-₁-equal-₀
             (λ (e : ℕ∞'-to-ℕ→𝟚 (ι n) i ＝ ₁)
                   → ν (ℕ∞'-index-uniqueness (ι n) (ℕ-to-ℕ∞'-diagonal n) e))

   f : (i : ℕ) → ℕ∞'-to-ℕ→𝟚 u i ＝ ℕ∞'-to-ℕ→𝟚 (ι n) i
   f i = Cases (ℕ-is-discrete n i)
          (λ (q : n ＝ i)
                → transport (λ - → ℕ∞'-to-ℕ→𝟚 u - ＝ ℕ∞'-to-ℕ→𝟚 (ι n) -) q I)
          (λ (ν : n ≠ i)
                → II i ν)

 size'-property' : {u : ℕ∞'} (φ : is-finite' u) → ι (size' {u} φ) ＝ u
 size'-property' {u} φ = II ⁻¹
  where
   I : ℕ∞'-to-ℕ→𝟚 u (size' {u} φ) ＝ ₁
   I = size'-property {u} φ

   II : u ＝ ι (size' {u} φ)
   II = diagonal-lemma (size' {u} φ) u I

 finite'-is-natural : (u : ℕ∞') → is-finite' u → Σ n ꞉ ℕ , u ＝ ι n
 finite'-is-natural u (n , p) = (n , diagonal-lemma n u p)

 finite'-gives-finite : (u : ℕ∞) → is-finite' (ℕ∞-to-ℕ∞' u) → is-finite u
 finite'-gives-finite u (n , e) = III
  where
   I : is-finite (ι n)
   I = ℕ-to-ℕ∞-is-finite n

   II = ι n                     ＝⟨ II₀ ⟩
        ℕ∞'-to-ℕ∞ (ι n)         ＝⟨ II₁ ⟩
        ℕ∞'-to-ℕ∞ (ℕ∞-to-ℕ∞' u) ＝⟨ II₂ ⟩
        u                       ∎
         where
          II₀ = (finite'-preservation n)⁻¹
          II₁ = ap ℕ∞'-to-ℕ∞ ((diagonal-lemma n (ℕ∞-to-ℕ∞' u) e)⁻¹)
          II₂ = inverses-are-retractions' ℕ∞-to-ℕ∞'-≃ u

   III : is-finite u
   III = transport is-finite II I

 finite'-isolated : (n : ℕ) → is-isolated (ℕ-to-ℕ∞' n)
 finite'-isolated n u = I (finite-isolated fe n (ℕ∞'-to-ℕ∞ u))
  where
   I : is-decidable (ι n ＝ ℕ∞'-to-ℕ∞ u) → is-decidable (ι n ＝ u)
   I (inl e) = inl (ι n                     ＝⟨ (finite-preservation n)⁻¹ ⟩
                    ℕ∞-to-ℕ∞' (ι n)         ＝⟨ ap ℕ∞-to-ℕ∞' e ⟩
                    ℕ∞-to-ℕ∞' (ℕ∞'-to-ℕ∞ u) ＝⟨ ℕ∞-ε u ⟩
                    u                       ∎)
   I (inr ν) = inr (λ (e : ι n ＝ u)
                         → ν (ι n             ＝⟨ (finite'-preservation n)⁻¹ ⟩
                              ℕ∞'-to-ℕ∞ (ι n) ＝⟨ ap ℕ∞'-to-ℕ∞ e ⟩
                              ℕ∞'-to-ℕ∞ u     ∎))

 ℕ∞'-equality-criterion : (x y : ℕ∞')
                        → ((n : ℕ) → ι n ＝ x → ι n ＝ y)
                        → ((n : ℕ) → ι n ＝ y → ι n ＝ x)
                        → x ＝ y
 ℕ∞'-equality-criterion x y f g = ℕ∞'-to-ℕ→𝟚-lc fe V
  where
   I : (n : ℕ) (x y : ℕ∞')
     → (ι n ＝ x → ι n ＝ y)
     → ℕ∞'-to-ℕ→𝟚 x n ≤₂ ℕ∞'-to-ℕ→𝟚 y n
   I n x y h = ≤₂-criterion a
    where
     a : ℕ∞'-to-ℕ→𝟚 x n ＝ ₁ → ℕ∞'-to-ℕ→𝟚 y n ＝ ₁
     a e = ℕ∞'-to-ℕ→𝟚 y n     ＝⟨ (ap (λ - → - n) IV)⁻¹ ⟩
           ℕ∞'-to-ℕ→𝟚 (ι n) n ＝⟨ ℕ-to-ℕ∞'-diagonal n ⟩
           ₁                  ∎
      where
       II : ι n ＝ x
       II = (diagonal-lemma n x e)⁻¹

       III : ι n ＝ y
       III = h II

       IV : ℕ∞'-to-ℕ→𝟚 (ι n) ＝ ℕ∞'-to-ℕ→𝟚 y
       IV = ap ℕ∞'-to-ℕ→𝟚 III

   V : ℕ∞'-to-ℕ→𝟚 x ＝ ℕ∞'-to-ℕ→𝟚 y
   V = dfunext fe (λ n → ≤₂-anti (I n x y (f n)) (I n y x (g n)))


 open import TypeTopology.TotallySeparated

 ℕ∞'-is-totally-separated : is-totally-separated ℕ∞'
 ℕ∞'-is-totally-separated = equiv-to-totally-separated
                             ℕ∞-to-ℕ∞'-≃
                             (ℕ∞-is-totally-separated fe)

\end{code}
