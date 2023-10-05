Alice Laroche, 26th September 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Univalence

module Various.File2
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import MLTT.NaturalNumbers
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Sets
open import UF.Subsingletons
open import W.Type
open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import Iterative.Sets ua 𝓤
open import Iterative.Sets-Addendum ua 𝓤
open import Iterative.Ordinals ua 𝓤
open import Various.File1 ua 𝓤

𝕄-dont-contain-themselves : (M : 𝕄) → ¬ (M ⁅ M)
𝕄-dont-contain-themselves (ssup X φ) (x , eq) =
 𝕄-dont-contain-themselves (φ x) (y , eq')
 where
  y : 𝕄-root (φ x)
  y = transport⁻¹ 𝕄-root eq x

  eq' : 𝕄-forest (φ x) y ＝ φ x
  eq' = transportd 𝕄-root (λ -₁ -₂ → 𝕄-forest -₁ -₂ ＝ -₁) x (eq ⁻¹) eq

succᴹ : 𝕄 → 𝕄
succᴹ M = ssup (𝕄-root M + 𝟙 {𝓤}) (cases (𝕄-forest M) (λ ⋆ → M))

ℕ-to-𝕄 : ℕ → 𝕄
ℕ-to-𝕄 0 = 𝟘ᴹ
ℕ-to-𝕄 (succ n) = succᴹ (ℕ-to-𝕄 n)

succᴹ-preserves-iset : (M : 𝕄)
                     → is-iterative-set M
                     → is-iterative-set (succᴹ M)
succᴹ-preserves-iset M is-iset = III , IV
 where
  I : is-h-isolated M
  I = isets-are-h-isolated M is-iset

  II : is-embedding (λ _ → M)
  II = global-point-is-embedding (λ _ → M) I

  III : is-embedding (𝕄-forest (succᴹ M))
  III = disjoint-cases-embedding _ _
         (𝕄-forest-is-embedding M is-iset)
         II
         (λ x ⋆ eq → 𝕄-dont-contain-themselves M (x , eq))

  IV : (x : 𝕄-root (succᴹ M)) → is-iterative-set (𝕄-forest (succᴹ M) x)
  IV = dep-cases (𝕄-subtrees-are-iterative M is-iset) (λ ⋆ → is-iset)

ℕ-to-𝕄-gives-iset : (n : ℕ) → is-iterative-set (ℕ-to-𝕄 n)
ℕ-to-𝕄-gives-iset zero     = 𝟘ᴹ-is-iset
ℕ-to-𝕄-gives-iset (succ n) = succᴹ-preserves-iset
                              (ℕ-to-𝕄 n)
                              (ℕ-to-𝕄-gives-iset n)

succⱽ : 𝕍 → 𝕍
succⱽ (M , M-is-iset) = succᴹ M , succᴹ-preserves-iset M M-is-iset

ℕ-to-𝕍 : ℕ → 𝕍
ℕ-to-𝕍 n = ℕ-to-𝕄 n , ℕ-to-𝕄-gives-iset n

succⱽ-preserves-∈ : (A B : 𝕍) → A ∈ B → A ∈ succⱽ B
succⱽ-preserves-∈ A B (x , p) = inl x , p

succⱽ-preserves-transitivity : (A : 𝕍)
                             → is-transitive-iset A
                             → is-transitive-iset (succⱽ A)
succⱽ-preserves-transitivity A is-tiset B C B∈succA C∈B = II
 where
  I : B ∈ succⱽ A → C ∈ A
  I (inr ⋆ , p) = transport⁻¹ _ p C∈B
  I (inl x , p) = is-tiset B C (x , p) C∈B

  II : C ∈ succⱽ A
  II =  succⱽ-preserves-∈ C A (I B∈succA)

succⱽ-preserves-members-transitivity : (A : 𝕍)
                                     → is-iterative-ordinal A
                                     → has-transitive-members (succⱽ A)
succⱽ-preserves-members-transitivity A is-iord B t = II t
 where
  I : underlying-mset A ＝ underlying-mset B → A ＝ B
  I p = to-subtype-＝ being-iset-is-prop p

  II : B ∈ succⱽ A → is-transitive-iset B
  II (inr ⋆ , p) =
   transport is-transitive-iset (I p) (iordinals-are-transitive A is-iord)
  II (inl x , p) =
   members-of-iordinals-are-transitive A is-iord B (x , p)

succⱽ-preserves-iordinal : (A : 𝕍)
                         → is-iterative-ordinal A
                         → is-iterative-ordinal (succⱽ A)
succⱽ-preserves-iordinal A is-iord = I , II
 where
  I : is-transitive-iset (succⱽ A)
  I = succⱽ-preserves-transitivity A (iordinals-are-transitive A is-iord)

  II : has-transitive-members (succⱽ A)
  II = succⱽ-preserves-members-transitivity A is-iord

ℕ-to-𝕍-gives-iordinal : (n : ℕ) → is-iterative-ordinal (ℕ-to-𝕍 n)
ℕ-to-𝕍-gives-iordinal zero     = 𝟘ⱽ-is-iordinal
ℕ-to-𝕍-gives-iordinal (succ n) =
 succⱽ-preserves-iordinal (ℕ-to-𝕍 n) (ℕ-to-𝕍-gives-iordinal n)

ℕ-to-𝕆 : ℕ → 𝕆
ℕ-to-𝕆 n = ℕ-to-𝕍 n , ℕ-to-𝕍-gives-iordinal n

\end{code}
