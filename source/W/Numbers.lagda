Martin Escardo, July 2023

A type of number used to measure lengths of paths in trees in W-types.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan

module W.Numbers where

open import W.Properties
open import W.Type
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Embeddings

module _ (𝓥 : Universe) where

 𝓝 : 𝓥 ⁺ ̇
 𝓝 = W (Ω 𝓥) _holds

 𝓝-induction : (P : 𝓝 → 𝓦 ̇ )
             → ((p : Ω 𝓥) (φ : p holds → 𝓝)
                   → ((a : p holds) → P (φ a)) → P (ssup p φ))
             → (n : 𝓝) → P n
 𝓝-induction = W-induction

 Zero : 𝓝
 Zero = ssup ⊥Ω 𝟘-elim

 Succ : 𝓝 → 𝓝
 Succ n = ssup ⊤Ω (λ ⋆ → n)

 is-positive : 𝓝 → 𝓥 ̇
 is-positive (ssup p φ) = p holds

 being-positive-is-prop : (n : 𝓝) → is-prop (is-positive n)
 being-positive-is-prop (ssup p φ) = holds-is-prop p

 Succ-is-positive : (n : 𝓝) → is-positive (Succ n)
 Succ-is-positive n = ⋆

 Zero-is-not-positive : ¬ is-positive Zero
 Zero-is-not-positive = 𝟘-elim

 Succ-is-not-Zero : (n : 𝓝) → Succ n ≠ Zero
 Succ-is-not-Zero n e = Zero-is-not-positive
                         (transport
                           is-positive
                           e
                           (Succ-is-positive n))

 Zero-is-not-Succ : (n : 𝓝) → Zero ≠ Succ n
 Zero-is-not-Succ n = ≠-sym (Succ-is-not-Zero n)

 𝓝⁺ : 𝓥 ⁺ ̇
 𝓝⁺ = Σ n ꞉ 𝓝 , is-positive n

 Pred : 𝓝⁺ → 𝓝
 Pred (ssup p φ , pos) = φ pos

 Succ-lc : left-cancellable Succ
 Succ-lc {m} {n} e = ap Pred I
  where
   I : (Succ m , ⋆) ＝[ 𝓝⁺ ] (Succ n , ⋆)
   I = to-subtype-＝ being-positive-is-prop e

 ℕ-to-𝓝 : ℕ → 𝓝
 ℕ-to-𝓝 zero = Zero
 ℕ-to-𝓝 (succ n) = Succ (ℕ-to-𝓝 n)

 ℕ-to-𝓝-lc : left-cancellable ℕ-to-𝓝
 ℕ-to-𝓝-lc {zero} {zero}     e = refl
 ℕ-to-𝓝-lc {zero} {succ n}   e = 𝟘-elim (Zero-is-not-Succ (ℕ-to-𝓝 n) e)
 ℕ-to-𝓝-lc {succ m} {zero}   e = 𝟘-elim (Succ-is-not-Zero (ℕ-to-𝓝 m) e)
 ℕ-to-𝓝-lc {succ m} {succ n} e = ap succ (ℕ-to-𝓝-lc (Succ-lc e))


 𝓝-to-Universe : 𝓝 → 𝓥 ̇
 𝓝-to-Universe (ssup p φ) = p holds + (Σ h ꞉ p holds , 𝓝-to-Universe (φ h))

 open import Fin.Type

 open import UF.PropIndexedPiSigma

 triangle : (n : ℕ) → 𝓝-to-Universe (ℕ-to-𝓝 n) ≃ Fin n
 triangle zero = 𝟘 + (Σ h ꞉ 𝟘 , 𝓝-to-Universe (𝟘-elim h)) ≃⟨ 𝟘-lneutral ⟩
                 (Σ h ꞉ 𝟘 , 𝓝-to-Universe (𝟘-elim h)) ≃⟨ prop-indexed-sum-zero id ⟩                 𝟘 ■

 triangle (succ n) = I
  where
   IH : 𝓝-to-Universe (ℕ-to-𝓝 n) ≃ Fin n
   IH = triangle n
   I : 𝓝-to-Universe (ℕ-to-𝓝 (succ n)) ≃ Fin (succ n)
   I = 𝟙 + (Σ h ꞉ 𝟙 , 𝓝-to-Universe (ℕ-to-𝓝 n)) ≃⟨ +-cong (≃-refl 𝟙) 𝟙-lneutral ⟩
       𝟙 + 𝓝-to-Universe (ℕ-to-𝓝 n)  ≃⟨ +-cong (≃-refl 𝟙) IH ⟩
       𝟙 + Fin n ≃⟨ +comm ⟩
       Fin n + 𝟙 {𝓥} ≃⟨ +-cong (≃-refl _) (one-𝟙-only 𝓥 𝓤₀) ⟩
       Fin n + 𝟙 {𝓤₀} ≃⟨ ≃-refl _ ⟩
       Fin (succ n) ■

 module _ (fe : Fun-Ext) (pe : Prop-Ext) where

  𝓝-is-set : is-set 𝓝
  𝓝-is-set = W-is-set (Ω 𝓥) _holds fe (Ω-is-set fe pe)

  Succ-is-embedding : is-embedding Succ
  Succ-is-embedding = lc-maps-into-sets-are-embeddings Succ Succ-lc 𝓝-is-set

  ℕ-to-𝓝-is-embedding : is-embedding ℕ-to-𝓝
  ℕ-to-𝓝-is-embedding = lc-maps-into-sets-are-embeddings ℕ-to-𝓝 ℕ-to-𝓝-lc 𝓝-is-set



\end{code}
