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

φ≠ssupφ : (m : 𝕄) (x : 𝕄-root m) → 𝕄-forest m x ≠ m
φ≠ssupφ (ssup X φ) x eq = φ≠ssupφ (φ x) y eq'
 where
  y : 𝕄-root (φ x)
  y = transport⁻¹ 𝕄-root eq x

  eq' : 𝕄-forest (φ x) y ＝ φ x
  eq' = transportd 𝕄-root (λ -₁ -₂ → 𝕄-forest -₁ -₂ ＝ -₁) x (eq ⁻¹) eq

succᴹ : 𝕄 → 𝕄
succᴹ m = ssup (𝕄-root m + 𝟙 {𝓤}) (cases (𝕄-forest m) (λ ⋆ → m))

𝕟ᴹ : ℕ → 𝕄
𝕟ᴹ 0 = 𝟘ᴹ
𝕟ᴹ (succ n) = succᴹ (𝕟ᴹ n)

succᴹ-preserve-iset : (m : 𝕄)
                    → is-iterative-set m
                    → is-iterative-set (succᴹ m)
succᴹ-preserve-iset m is-iset = III , IV
 where
  I : is-h-isolated m
  I = isets-are-h-isolated m is-iset

  II : is-embedding (λ _ → m)
  II = global-point-is-embedding (λ _ → m) I

  III : is-embedding (𝕄-forest (succᴹ m))
  III = disjoint-cases-embedding _ _ (𝕄-forest-is-embedding m is-iset) II (λ x ⋆ → φ≠ssupφ m x)

  IV : (x : 𝕄-root (succᴹ m)) → is-iterative-set (𝕄-forest (succᴹ m) x)
  IV = dep-cases (𝕄-subtrees-are-iterative m is-iset) (λ ⋆ → is-iset)

𝕟ᴹ-is-iset : (n : ℕ) → is-iterative-set (𝕟ᴹ n)
𝕟ᴹ-is-iset zero     = 𝟘ᴹ-is-iset
𝕟ᴹ-is-iset (succ n) = succᴹ-preserve-iset (𝕟ᴹ n) (𝕟ᴹ-is-iset n)

succⱽ : 𝕍 → 𝕍
succⱽ (m , m-is-iset) = succᴹ m , succᴹ-preserve-iset m m-is-iset

𝕟ⱽ : ℕ → 𝕍
𝕟ⱽ n = 𝕟ᴹ n , 𝕟ᴹ-is-iset n

succⱽ-preserve-∈ : (v v' : 𝕍) → v ∈ v' → v ∈ succⱽ v'
succⱽ-preserve-∈ v v' (x , p) = inl x , p

succⱽ-preserve-transitivity : (v : 𝕍)
                            → is-transitive-iset v
                            → is-transitive-iset (succⱽ v)
succⱽ-preserve-transitivity v is-tiset v₁ v₂ v₁∈succv v₂∈v₁ = II
 where
  I : v₁ ∈ succⱽ v → v₂ ∈ v
  I (inr ⋆ , p) = transport⁻¹ _ p v₂∈v₁
  I (inl x , p) = is-tiset v₁ v₂ (x , p) v₂∈v₁

  II : v₂ ∈ succⱽ v
  II =  succⱽ-preserve-∈ v₂ v (I v₁∈succv)

succⱽ-preserve-members-transitivity : (v : 𝕍)
                                    → is-iterative-ordinal v
                                    → has-transitive-members (succⱽ v)
succⱽ-preserve-members-transitivity v is-iord v₁ t = II t
 where
  I : underlying-mset v ＝ underlying-mset v₁ → v ＝ v₁
  I p = to-subtype-＝ being-iset-is-prop p

  II : v₁ ∈ succⱽ v → is-transitive-iset v₁
  II (inr ⋆ , p) =
   transport is-transitive-iset (I p) (iordinals-are-transitive v is-iord)
  II (inl x , p) =
   members-of-iordinals-are-transitive v is-iord v₁ (x , p)

succⱽ-preserve-iordinal : (v : 𝕍)
                        → is-iterative-ordinal v
                        → is-iterative-ordinal (succⱽ v)
succⱽ-preserve-iordinal v is-iord = I , II
 where
 I : is-transitive-iset (succⱽ v)
 I = succⱽ-preserve-transitivity v (iordinals-are-transitive v is-iord)

 II : has-transitive-members (succⱽ v)
 II = succⱽ-preserve-members-transitivity v is-iord

𝕟ⱽ-is-iordinal : (n : ℕ) → is-iterative-ordinal (𝕟ⱽ n)
𝕟ⱽ-is-iordinal zero     = 𝟘ⱽ-is-iordinal
𝕟ⱽ-is-iordinal (succ n) = succⱽ-preserve-iordinal (𝕟ⱽ n) (𝕟ⱽ-is-iordinal n)

𝕟ᴼ : ℕ → 𝕆
𝕟ᴼ n = 𝕟ⱽ n , 𝕟ⱽ-is-iordinal n

\end{code}
