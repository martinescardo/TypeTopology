Martin Escardo, July 2023

A type of numbers used to measure lengths of paths in trees in W-types.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (_^_)

module W.Numbers where

open import Fin.Type
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons renaming (⊥Ω to ⊥ ; ⊤Ω to ⊤)
open import UF.Subsingletons-FunExt
open import W.Properties
open import W.Type

module _ (𝓥 : Universe) where

 𝓝 : 𝓥 ⁺ ̇
 𝓝 = W (Ω 𝓥) _holds

 positive : 𝓝 → Ω 𝓥
 positive = W-root

 is-positive : 𝓝 → 𝓥 ̇
 is-positive n = positive n holds

\end{code}

The predecessor function is defined on positive numbers.

\begin{code}

 Pred : (n : 𝓝) → is-positive n → 𝓝
 Pred = W-forest

\end{code}

For every proposition p, there is a p-ary successor function. Notice
that we can regard an element of 𝓝 ^ p as a p-indexed tuple of
elements of 𝓝, or, equivalently, as a partial element of 𝓝.

\begin{code}

 _^_ : 𝓤 ̇  → Ω 𝓥 → 𝓥 ⊔ 𝓤 ̇
 X ^ p = p holds → X

 Suc : (p : Ω 𝓥) → 𝓝 ^ p → 𝓝
 Suc = ssup

 Suc-positivity : (p : Ω 𝓥) (ns : 𝓝 ^ p) → positive (Suc p ns) ＝ p
 Suc-positivity = W-ssup-root

 Pred-Suc : (p : Ω 𝓥) (ns : 𝓝 ^ p) → Pred (Suc p ns) ＝ ns
 Pred-Suc = W-ssup-forest

 Suc-Pred : (n : 𝓝) → Suc (positive n) (Pred n) ＝ n
 Suc-Pred = W-η

 𝓝-induction : (P : 𝓝 → 𝓦 ̇ )
             → ((p : Ω 𝓥) (ns : 𝓝 ^ p)
                   → ((h : p holds) → P (ns h))
                   → P (Suc p ns))
             → (n : 𝓝) → P n
 𝓝-induction = W-induction

 𝓝-induction' : (P : 𝓝 → 𝓦 ̇ )
              → ((n : 𝓝)
                    → ((p : is-positive n) → P (Pred n p))
                    → P n)
              → (n : 𝓝) → P n
 𝓝-induction' = W-induction'

\end{code}

The ⊥-ary successor function amounts to the number zero, and the ⊤-ary
successor function amounts to the ordinary successor function.

\begin{code}

 private
  Zero' : (𝟘 → 𝓝) → 𝓝
  Zero' = Suc ⊥

  Succ' : (𝟙 → 𝓝) → 𝓝
  Succ' = Suc ⊤

 Zero : 𝓝
 Zero = Zero' unique-from-𝟘

 Succ : 𝓝 → 𝓝
 Succ n = Succ' (λ _ → n)

 being-positive-is-prop : (n : 𝓝) → is-prop (is-positive n)
 being-positive-is-prop n = holds-is-prop (positive n)

 Succ-is-positive : (n : 𝓝) → is-positive (Succ n)
 Succ-is-positive n = ⊤Ω-holds

 Zero-is-not-positive : ¬ is-positive Zero
 Zero-is-not-positive = ⊥Ω-doesnt-hold

 Succ-is-not-Zero : (n : 𝓝) → Succ n ≠ Zero
 Succ-is-not-Zero n e = Zero-is-not-positive
                         (transport
                           is-positive
                           e
                           (Succ-is-positive n))

 Zero-is-not-Succ : (n : 𝓝) → Zero ≠ Succ n
 Zero-is-not-Succ n = ≠-sym (Succ-is-not-Zero n)

\end{code}

The type of positive numbers.

\begin{code}

 𝓝⁺ : 𝓥 ⁺ ̇
 𝓝⁺ = Σ n ꞉ 𝓝 , is-positive n

 forget-is-positive : 𝓝⁺ → 𝓝
 forget-is-positive = pr₁

 forget-is-positive-is-embedding : is-embedding forget-is-positive
 forget-is-positive-is-embedding = pr₁-is-embedding being-positive-is-prop

 Pred⁺ : 𝓝⁺ → 𝓝
 Pred⁺ = uncurry Pred

 Succ⁺ : 𝓝 → 𝓝⁺
 Succ⁺ n = Succ n , Succ-is-positive n

 Pred⁺-Succ⁺ : (n : 𝓝) → Pred⁺ (Succ⁺ n) ＝ n
 Pred⁺-Succ⁺ n = refl

 Succ-lc : left-cancellable Succ
 Succ-lc {m} {n} e = ap Pred⁺ I
  where
   I : Succ⁺ m ＝ Succ⁺ n
   I = embeddings-are-lc forget-is-positive forget-is-positive-is-embedding e

\end{code}

The type of natural numbers is embedded into our type of numbers.

\begin{code}

 ℕ-to-𝓝 : ℕ → 𝓝
 ℕ-to-𝓝 zero     = Zero
 ℕ-to-𝓝 (succ n) = Succ (ℕ-to-𝓝 n)

 ℕ-to-𝓝-lc : left-cancellable ℕ-to-𝓝
 ℕ-to-𝓝-lc {zero}   {zero}   e = refl
 ℕ-to-𝓝-lc {zero}   {succ n} e = 𝟘-elim (Zero-is-not-Succ (ℕ-to-𝓝 n) e)
 ℕ-to-𝓝-lc {succ m} {zero}   e = 𝟘-elim (Succ-is-not-Zero (ℕ-to-𝓝 m) e)
 ℕ-to-𝓝-lc {succ m} {succ n} e = ap succ (ℕ-to-𝓝-lc (Succ-lc e))

 module _ (fe : Fun-Ext) (pe : Prop-Ext) where

  𝓝-is-set : is-set 𝓝
  𝓝-is-set = W-is-set (Ω 𝓥) _holds fe (Ω-is-set fe pe)

  Succ-is-embedding : is-embedding Succ
  Succ-is-embedding = lc-maps-into-sets-are-embeddings Succ Succ-lc 𝓝-is-set

  ℕ-to-𝓝-is-embedding : is-embedding ℕ-to-𝓝
  ℕ-to-𝓝-is-embedding = lc-maps-into-sets-are-embeddings ℕ-to-𝓝 ℕ-to-𝓝-lc 𝓝-is-set

\end{code}

A criterion for equality on 𝓝.

\begin{code}

 to-𝓝-＝ : {p q : Ω 𝓥} {ms : 𝓝 ^ p} {ns : 𝓝 ^ q}
         → (Σ e ꞉ p ＝ q , (ms ＝ ns ∘ transport _holds e))
         → Suc p ms ＝ Suc q ns
 to-𝓝-＝ = to-W-＝ (Ω 𝓥) _holds

 Succ⁺-Pred⁺ : Fun-Ext
             → Prop-Ext
             → (n⁺ : 𝓝⁺) → Succ⁺ (Pred⁺ n⁺) ＝ n⁺
 Succ⁺-Pred⁺ fe pe (n , pos) = to-subtype-＝ being-positive-is-prop I
  where
   I = Succ (Pred n pos)         ＝⟨ refl ⟩
       Suc ⊤ (λ _ → Pred n pos)  ＝⟨ II ⟩
       Suc (positive n) (Pred n) ＝⟨ Suc-Pred n ⟩
       n                         ∎
    where
     II = to-𝓝-＝
           (((true-is-equal-⊤ pe fe
               (is-positive n)
               (being-positive-is-prop n)
               pos)⁻¹) ,
           dfunext fe (λ h → ap (Pred n) (being-positive-is-prop n _ _)))

\end{code}

Hence 𝓝⁺ and 𝓝 are equivalent.

\begin{code}

 𝓝⁺-≃-𝓝 : Fun-Ext → Prop-Ext → 𝓝⁺ ≃ 𝓝
 𝓝⁺-≃-𝓝 fe pe = qinveq Pred⁺ (Succ⁺ , Succ⁺-Pred⁺ fe pe , Pred⁺-Succ⁺)

\end{code}

Our numbers "count" the number of elements of certain types.

\begin{code}

 𝓕𝓲𝓷 : 𝓝 → 𝓥 ̇
 𝓕𝓲𝓷 (ssup p ns) = p holds + (Σ h ꞉ p holds , 𝓕𝓲𝓷 (ns h))

\end{code}

The map Fin : ℕ → 𝓤₀ factors as ℕ-to-𝓝 : ℕ → 𝓝 followed
by 𝓕𝓲𝓷 : 𝓝 → 𝓥.

\begin{code}

 Fin-factor : (n : ℕ) → 𝓕𝓲𝓷 (ℕ-to-𝓝 n) ≃ Fin n
 Fin-factor zero =
  𝟘 + (Σ h ꞉ 𝟘 , 𝓕𝓲𝓷 (𝟘-elim h)) ≃⟨ 𝟘-lneutral ⟩
  (Σ h ꞉ 𝟘 , 𝓕𝓲𝓷 (𝟘-elim h))     ≃⟨ prop-indexed-sum-zero id ⟩
  𝟘                              ■

 Fin-factor (succ n) = I
  where
   IH : 𝓕𝓲𝓷 (ℕ-to-𝓝 n) ≃ Fin n
   IH = Fin-factor n

   I = 𝓕𝓲𝓷 (ℕ-to-𝓝 (succ n))          ≃⟨ ≃-refl _ ⟩
       𝟙 + (Σ h ꞉ 𝟙 , 𝓕𝓲𝓷 (ℕ-to-𝓝 n)) ≃⟨ II  ⟩
       𝟙 + 𝓕𝓲𝓷 (ℕ-to-𝓝 n)             ≃⟨ III ⟩
       𝟙 + Fin n                       ≃⟨ +comm ⟩
       Fin n + 𝟙 {𝓥}                   ≃⟨ IV ⟩
       Fin n + 𝟙 {𝓤₀}                  ≃⟨ ≃-refl _ ⟩
       Fin (succ n)                    ■
    where
     II  = +-cong (≃-refl 𝟙) 𝟙-lneutral
     III = +-cong (≃-refl 𝟙) IH
     IV  = +-cong (≃-refl _) (one-𝟙-only 𝓥 𝓤₀)

\end{code}
