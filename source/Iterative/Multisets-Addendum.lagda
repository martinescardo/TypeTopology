Martin Escardo July 2023.

Some constructions with iterative multisets.

 * The universe is a retract of the type 𝕄 of iterative multisets.
 * 𝕄 is algebraicly injective.


\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Univalence

module Iterative.Multisets-Addendum
        (𝓤 : Universe)
        (ua : Univalence)
       where

open import Iterative.Multisets 𝓤
open import Iterative.Sets 𝓤 ua
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Miscelanea
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import W.Type
open import W.Properties (𝓤 ̇) id

private
 𝓤⁺ : Universe
 𝓤⁺ = 𝓤 ⁺

 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import InjectiveTypes.Blackboard fe'

\end{code}

The universe 𝓤 is embedded as a retract of 𝕄.

\begin{code}

𝟘ᴹ : 𝕄
𝟘ᴹ = ssup 𝟘 unique-from-𝟘

𝟘ᴹ-is-iset : is-iterative-set 𝟘ᴹ
𝟘ᴹ-is-iset = unique-from-𝟘-is-embedding , (λ (x : 𝟘) → 𝟘-elim x)

𝟘ᴹ-is-h-isolated : is-h-isolated 𝟘ᴹ
𝟘ᴹ-is-h-isolated {ssup X φ} = isets-are-h-isolated 𝟘ᴹ 𝟘ᴹ-is-iset

𝓤-to-𝕄 : 𝓤 ̇ → 𝕄
𝓤-to-𝕄 X = ssup X (λ x → 𝟘ᴹ)

𝓤-to-𝕄-is-section : 𝕄-root ∘ 𝓤-to-𝕄 ∼ id
𝓤-to-𝕄-is-section X = refl

𝓤-is-retract-of-𝕄 : retract (𝓤 ̇ ) of 𝕄
𝓤-is-retract-of-𝕄 = 𝕄-root , 𝓤-to-𝕄 , 𝓤-to-𝕄-is-section

𝓤-to-𝕄-is-embedding : is-embedding 𝓤-to-𝕄
𝓤-to-𝕄-is-embedding M@(ssup Y φ) = II
 where
  I = fiber 𝓤-to-𝕄 M ≃⟨ ≃-refl _ ⟩
      (Σ X ꞉ 𝓤 ̇ , ssup X (λ x → 𝟘ᴹ) ＝ (ssup Y φ))                     ≃⟨ I₀ ⟩
      (Σ X ꞉ 𝓤 ̇ , Σ p ꞉ X ＝ Y , (λ x → 𝟘ᴹ) ＝ φ ∘ Idtofun p)          ≃⟨ I₁ ⟩
      (Σ (X , p) ꞉ (Σ X ꞉ 𝓤 ̇ , X ＝ Y) , (λ x → 𝟘ᴹ) ＝ φ ∘ Idtofun p)  ■
   where
    I₀ = Σ-cong (λ X → 𝕄-＝)
    I₁ = ≃-sym Σ-assoc

  II : is-prop (fiber 𝓤-to-𝕄 M)
  II = equiv-to-prop I
        (subsets-of-props-are-props _ _
          (singleton-types'-are-props Y)
          (constant-maps-are-h-isolated fe 𝟘ᴹ 𝟘ᴹ-is-h-isolated))

\end{code}

The type of multisets is algebraicly injective.

\begin{code}

Σᴹ : {X : 𝓤 ̇ } → (X → 𝕄) → 𝕄
Σᴹ {X} A = ssup
            (Σ x ꞉ X , 𝕄-root (A x))
            (λ (x , y) → 𝕄-forest (A x) y)

prop-indexed-sumᴹ : {X : 𝓤 ̇ } {A : X → 𝕄}
                  → is-prop X
                  → (x₀ : X) → Σᴹ A ＝ A x₀
prop-indexed-sumᴹ {X} {A} i x₀ = V
 where
  𝕗 = (Σ x ꞉ X , 𝕄-root (A x)) ≃⟨ prop-indexed-sum i x₀ ⟩
      𝕄-root (A x₀)            ■

  remark : ⌜ 𝕗 ⌝ ＝ (λ (x , y) → transport (λ - → W-root (A -)) (i x x₀) y)
  remark = refl

  I : ((x , y) : Σ x ꞉ X , 𝕄-root (A x))
      (p : x ＝ x₀)
    → 𝕄-forest (A x) y ＝ 𝕄-forest (A x₀) (transport (λ - → W-root (A -)) p y)
  I _ refl = refl

  II : ((x , y) : Σ x ꞉ X , 𝕄-root (A x))
     → 𝕄-forest (A x) y ＝ 𝕄-forest (A x₀) (⌜ 𝕗 ⌝ (x , y))
  II (x , y) = I (x , y) (i x x₀)

  III : ((x , y) : Σ x ꞉ X , 𝕄-root (A x))
     → 𝕄-forest (A x) y ≃ᴹ 𝕄-forest (A x₀) (⌜ 𝕗 ⌝ (x , y))
  III σ = idtoeqᴹ _ _ (II σ)

  IV : Σᴹ A ≃ᴹ ssup (𝕄-root (A x₀)) (𝕄-forest (A x₀))
  IV = 𝕗 , III

  V = Σᴹ A                                    ＝⟨ ⌜ 𝕄-=-≃ ua _ _ ⌝⁻¹ IV ⟩
      ssup (𝕄-root (A x₀)) (𝕄-forest (A x₀)) ＝⟨ 𝕄-η (A x₀) ⟩
      A x₀                                    ∎

𝕄-is-ainjective : ainjective-type 𝕄 𝓤 𝓤
𝕄-is-ainjective {X} {Y} j j-emb f = f\j , f\j-ext
 where
  A : (y : Y) → fiber j y → 𝕄
  A y (x , _) = f x

  f\j : Y → 𝕄
  f\j y = Σᴹ (A y)

  f\j-ext : f\j ∘ j ∼ f
  f\j-ext x = prop-indexed-sumᴹ {fiber j (j x)} {A (j x)} (j-emb (j x)) (x , refl)

\end{code}
