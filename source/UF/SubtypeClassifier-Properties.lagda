Martin Escardo

Properties of the type of truth values.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module UF.SubtypeClassifier-Properties where

open import MLTT.Spartan
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Hedberg
open import UF.Lower-FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

𝟚-to-Ω : 𝟚 → Ω 𝓤
𝟚-to-Ω ₀ = ⊥
𝟚-to-Ω ₁ = ⊤

Ω-is-set : funext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-set {𝓤} fe pe = Id-collapsibles-are-sets pc
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)

  A-is-prop : (p q : Ω 𝓤) → is-prop (A p q)
  A-is-prop p q = Σ-is-prop (Π-is-prop fe
                              (λ _ → holds-is-prop q))
                              (λ _ → Π-is-prop fe (λ _ → holds-is-prop p))

  g : (p q : Ω 𝓤) → p ＝ q → A p q
  g p q e = (b , c)
   where
    a : p holds ＝ q holds
    a = ap _holds e

    b : p holds → q holds
    b = transport id a

    c : q holds → p holds
    c = transport id (a ⁻¹)

  h  : (p q : Ω 𝓤) → A p q → p ＝ q
  h p q (u , v) = Ω-extensionality fe pe u v

  f  : (p q : Ω 𝓤) → p ＝ q → p ＝ q
  f p q e = h p q (g p q e)

  wconstant-f : (p q : Ω 𝓤) (d e : p ＝ q) → f p q d ＝ f p q e
  wconstant-f p q d e = ap (h p q) (A-is-prop p q (g p q d) (g p q e))

  pc : {p q : Ω 𝓤} → Σ f ꞉ (p ＝ q → p ＝ q) , wconstant f
  pc {p} {q} = (f p q , wconstant-f p q)

equal-⊤-≃ : propext 𝓤
          → funext 𝓤 𝓤
          → (p : Ω 𝓤) → (p ＝ ⊤) ≃ (p holds)
equal-⊤-≃ {𝓤} pe fe p = logically-equivalent-props-are-equivalent
                         (Ω-is-set fe pe)
                         (holds-is-prop p)
                         (equal-⊤-gives-holds p)
                         (holds-gives-equal-⊤ pe fe p)

equal-⊥-≃ : propext 𝓤
          → funext 𝓤 𝓤
          → (p : Ω 𝓤) → (p ＝ ⊥) ≃ ¬ (p holds)
equal-⊥-≃ {𝓤} pe fe p = logically-equivalent-props-are-equivalent
                         (Ω-is-set fe pe)
                         (negations-are-props (lower-funext 𝓤 𝓤 fe))
                         (equal-⊥-gives-fails p)
                         (fails-gives-equal-⊥ pe fe p)

module _ (fe : funext 𝓤 𝓤) (pe : propext 𝓤) where

 𝟚-to-Ω-is-embedding : is-embedding (𝟚-to-Ω {𝓤})
 𝟚-to-Ω-is-embedding _ (₀ , p) (₀ , q) = to-Σ-＝ (refl , Ω-is-set fe pe p q)
 𝟚-to-Ω-is-embedding _ (₀ , p) (₁ , q) = 𝟘-elim (⊥-is-not-⊤ (p ∙ q ⁻¹))
 𝟚-to-Ω-is-embedding _ (₁ , p) (₀ , q) = 𝟘-elim (⊥-is-not-⊤ (q ∙ p ⁻¹))
 𝟚-to-Ω-is-embedding _ (₁ , p) (₁ , q) = to-Σ-＝ (refl , Ω-is-set fe pe p q)

 𝟚-to-Ω-fiber : (p : Ω 𝓤) → fiber 𝟚-to-Ω p ≃ (¬ (p holds) + p holds)
 𝟚-to-Ω-fiber p =
  fiber (𝟚-to-Ω {𝓤}) p           ≃⟨ ≃-refl _ ⟩
  (Σ n ꞉ 𝟚 , 𝟚-to-Ω {𝓤} n ＝ p ) ≃⟨ I₀ ⟩
  (⊥ ＝ p) + (⊤ ＝ p)            ≃⟨ I₁ ⟩
  (¬ (p holds) + p holds)        ■
    where
     I₀ = alternative-+
     I₁ = +-cong
           (＝-flip ● equal-⊥-≃ pe fe p)
           (＝-flip ● equal-⊤-≃ pe fe p)

\end{code}

Added 24th August 2023.

\begin{code}

open import UF.Embeddings
open import UF.ExcludedMiddle

module _ {𝓤 : Universe} (fe : Fun-Ext) (pe : propext 𝓤) where

 open import Various.HiggsInvolutionTheorem {𝓤} fe pe

 Ω-autoembedding-that-maps-⊥-to-⊤-gives-EM : (Σ 𝕗 ꞉ Ω 𝓤 ↪ Ω 𝓤 , ⌊ 𝕗 ⌋ ⊤ ＝ ⊥)
                                           → EM 𝓤
 Ω-autoembedding-that-maps-⊥-to-⊤-gives-EM ((f , f-is-emb) , e) = II
  where
   f-is-involutive : involutive f
   f-is-involutive = higgs f (embeddings-are-lc f f-is-emb)

   I : ((P : 𝓤 ̇ ) → is-prop P → Σ Q ꞉ 𝓤 ̇ , (P ⇔ ¬ Q))
   I P P-is-prop = f p holds , g , h
    where
     p : Ω 𝓤
     p = (P , P-is-prop)

     g : P → ¬ (f p holds)
     g p-holds = equal-⊥-gives-fails (f p)
                  (f p ＝⟨ ap f (holds-gives-equal-⊤ pe fe p p-holds) ⟩
                   f ⊤ ＝⟨ e ⟩
                   ⊥   ∎)

     h : ¬ (f p holds) → P
     h ν = equal-⊤-gives-holds p
            (p       ＝⟨ (f-is-involutive p)⁻¹ ⟩
             f (f p) ＝⟨ ap f (fails-gives-equal-⊥ pe fe (f p) ν) ⟩
             f ⊥     ＝⟨ ap f (e ⁻¹) ⟩
             f (f ⊤) ＝⟨ f-is-involutive ⊤ ⟩
             ⊤       ∎)

   II : EM 𝓤
   II = all-props-negative-gives-EM fe I

 Ω-autoembedding-apart-from-id-gives-EM : (Σ 𝕗 ꞉ Ω 𝓤 ↪ Ω 𝓤 , Σ p₀ ꞉ Ω 𝓤 , ⌊ 𝕗 ⌋ p₀ ≠ p₀) → EM 𝓤
 Ω-autoembedding-apart-from-id-gives-EM (𝕗@(f , f-is-emb) , p₀ , ν) =
  Ω-autoembedding-that-maps-⊥-to-⊤-gives-EM (𝕗 , VII)
  where
   f-is-involutive : involutive f
   f-is-involutive = higgs f (embeddings-are-lc f f-is-emb)

   I : ¬ (f ⊤ ＝ ⊤)
   I e = VI
    where
     II : p₀ ≠ ⊤
     II e₀ = ν (transport⁻¹ (λ - → f - ＝ -) e₀ e)
     III : p₀ ＝ ⊥
     III = false-gives-equal-⊥ pe fe (p₀ holds) (holds-is-prop p₀)
            (contrapositive (holds-gives-equal-⊤ pe fe p₀) II)
     IV : f ⊥ ≠ ⊥
     IV e₁ = ν (transport⁻¹ (λ - → f - ＝ -) III e₁)
     V : f ⊥ ≠ ⊤
     V e₂ = ⊥-is-not-⊤
              (⊥ ＝⟨ (f-is-involutive ⊥)⁻¹ ⟩
              f (f ⊥) ＝⟨ ap f e₂ ⟩
              f ⊤ ＝⟨ e ⟩
              ⊤ ∎)
     VI : 𝟘
     VI = no-truth-values-other-than-⊥-or-⊤ fe pe
           (f ⊥ , IV , V)

   VII : f ⊤ ＝ ⊥
   VII = false-gives-equal-⊥ pe fe (f ⊤ holds) (holds-is-prop (f ⊤))
        (contrapositive (holds-gives-equal-⊤ pe fe (f ⊤)) I)

 Ω-automorphism-that-maps-⊥-to-⊤-gives-EM : (Σ 𝕗 ꞉ Ω 𝓤 ≃ Ω 𝓤 , ⌜ 𝕗 ⌝ ⊤ ＝ ⊥) → EM 𝓤
 Ω-automorphism-that-maps-⊥-to-⊤-gives-EM (𝕗 , e) =
  Ω-autoembedding-that-maps-⊥-to-⊤-gives-EM (≃-gives-↪ 𝕗 , e)

 Ω-automorphism-apart-from-id-gives-EM : (Σ 𝕗 ꞉ Ω 𝓤 ≃ Ω 𝓤 , Σ p₀ ꞉ Ω 𝓤 , ⌜ 𝕗 ⌝ p₀ ≠ p₀) → EM 𝓤
 Ω-automorphism-apart-from-id-gives-EM (𝕗 , p₀ , ν) =
  Ω-autoembedding-apart-from-id-gives-EM (≃-gives-↪ 𝕗 , p₀ , ν)

\end{code}
