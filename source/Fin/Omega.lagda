Martin Escardo, 19th March 2021.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Omega where

open import UF.Subsingletons

open import Fin.Topology
open import Fin.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Order
open import Naturals.Properties
open import Notation.Order
open import NotionsOfDecidability.Decidable
open import UF.Embeddings
open import UF.Equiv
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

having-three-distinct-points-covariant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                       → X ↪ Y
                                       → has-three-distinct-points X
                                       → has-three-distinct-points Y
having-three-distinct-points-covariant (f , f-is-emb) ((x , y , z) , u , v , w) = γ
 where
  l : left-cancellable f
  l = embeddings-are-lc f f-is-emb

  γ : has-three-distinct-points (codomain f)
  γ = ((f x , f y , f z) , (λ p → u (l p)) , (λ q → v (l q)) , (λ r → w (l r)))

finite-type-with-three-distict-points : (k : ℕ)
                                      → k ≥ 3
                                      → has-three-distinct-points (Fin k)
finite-type-with-three-distict-points (succ (succ (succ k))) * =
 ((𝟎 , 𝟏 , 𝟐) , +disjoint' , (λ a → +disjoint' (inl-lc a)) , +disjoint)

finite-subsets-of-Ω-have-at-most-2-elements : funext 𝓤 𝓤
                                            → propext 𝓤
                                            → (k : ℕ)
                                            → Fin k ↪ Ω 𝓤
                                            → k ≤ 2
finite-subsets-of-Ω-have-at-most-2-elements {𝓤} fe pe k e = γ
 where
  α : k ≥ 3 → has-three-distinct-points (Ω 𝓤)
  α g = having-three-distinct-points-covariant e
         (finite-type-with-three-distict-points k g)

  β : ¬ (k ≥ 3)
  β = contrapositive α (no-three-distinct-propositions fe pe)

  γ : k ≤ 2
  γ = not-less-bigger-or-equal k 2 β

\end{code}

Added 3rd September 2023.

\begin{code}

Fin-to-Ω-embedding-is-equiv-iff-2-and-EM : funext 𝓤 𝓤
                                         → propext 𝓤
                                         → (k : ℕ)
                                         → (𝕖 : Fin k ↪ Ω 𝓤)
                                         → is-equiv ⌊ 𝕖 ⌋ ↔ ((k ＝ 2) × EM 𝓤)
Fin-to-Ω-embedding-is-equiv-iff-2-and-EM {𝓤} fe pe 0 (e , _) = I , II
 where
  I : is-equiv e → (0 ＝ 2) × EM 𝓤
  I e-is-equiv = 𝟘-elim (inverse e e-is-equiv ⊥)

  II : (0 ＝ 2) × EM 𝓤 → is-equiv e
  II (p , _) = 𝟘-elim (zero-not-positive 1 p)

Fin-to-Ω-embedding-is-equiv-iff-2-and-EM {𝓤} fe pe 1 (e , _) = I , II
 where
  I : is-equiv e → (1 ＝ 2) × EM 𝓤
  I e-is-equiv = 𝟘-elim (⊥-is-not-⊤ I₁)
   where
    𝕗 : Fin 1 ≃ Ω 𝓤
    𝕗 = (e , e-is-equiv)

    I₀ : is-prop (Fin 1)
    I₀ (inr _) (inr _) = ap inr refl

    I₁ = ⊥                 ＝⟨ (inverses-are-sections ⌜ 𝕗 ⌝ ⌜ 𝕗 ⌝-is-equiv ⊥)⁻¹ ⟩
         ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ ⊥) ＝⟨ ap ⌜ 𝕗 ⌝ (I₀ (⌜ 𝕗 ⌝⁻¹ ⊥) (⌜ 𝕗 ⌝⁻¹ ⊤)) ⟩
         ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ ⊤) ＝⟨ inverses-are-sections ⌜ 𝕗 ⌝ ⌜ 𝕗 ⌝-is-equiv ⊤ ⟩
         ⊤                 ∎

  II : (1 ＝ 2) × EM 𝓤 → is-equiv e
  II (r , _) = 𝟘-elim (zero-not-positive 0 (succ-lc r))

Fin-to-Ω-embedding-is-equiv-iff-2-and-EM {𝓤} fe pe 2 (e , e-is-embedding) =
 I , II
 where
  I : is-equiv e → (2 ＝ 2) × EM 𝓤
  I e-is-equiv = refl , I₀
   where
    e⁻¹ : Ω 𝓤 → Fin 2
    e⁻¹ = inverse e e-is-equiv

    η : e ∘ e⁻¹ ∼ id
    η = inverses-are-sections e e-is-equiv

    ε : e⁻¹ ∘ e ∼ id
    ε = inverses-are-retractions e e-is-equiv

    I₀ : EM 𝓤
    I₀ P P-is-prop = I₂ I₁
     where
      p : Ω 𝓤
      p = (P , P-is-prop)

      I₁ : is-decidable (e⁻¹ p ＝ e⁻¹ ⊤)
      I₁ = Fin-is-discrete (e⁻¹ p) (e⁻¹ ⊤)

      I₂ : is-decidable (e⁻¹ p ＝ e⁻¹ ⊤) → is-decidable (p holds)
      I₂ = map-is-decidable
           (λ (r : e⁻¹ p ＝ e⁻¹ ⊤)
                 → equal-⊤-gives-holds p
                    (equivs-are-lc e⁻¹ (inverses-are-equivs e e-is-equiv) r))
           (λ (h : p holds)
                 → ap e⁻¹ (holds-gives-equal-⊤ pe fe p h))

  II : (2 ＝ 2) × EM 𝓤 → is-equiv e
  II (_ , em) = embeddings-with-sections-are-equivs e e-is-embedding (e⁻¹ , η)
   where
    II₀ : e 𝟎 holds → ¬ (e 𝟏 holds)
    II₀ h₀ h₁ =
      +disjoint
       (embeddings-are-lc e e-is-embedding
        (e 𝟏 ＝⟨ holds-gives-equal-⊤ pe fe (e 𝟏) h₁ ⟩
         ⊤   ＝⟨ (holds-gives-equal-⊤ pe fe (e 𝟎) h₀)⁻¹ ⟩
         e 𝟎 ∎))

    II₁ : ¬ (e 𝟎 holds) → e 𝟏 holds
    II₁ ν₀ = ¬¬-elim (em (e 𝟏 holds) (holds-is-prop (e 𝟏))) II₂
     where
      II₂ : ¬¬ (e 𝟏 holds)
      II₂ ν₁ =
       +disjoint
        (embeddings-are-lc e e-is-embedding
         (e 𝟏 ＝⟨ fails-gives-equal-⊥ pe fe (e 𝟏) ν₁ ⟩
          ⊥   ＝⟨ (fails-gives-equal-⊥ pe fe (e 𝟎) ν₀)⁻¹ ⟩
          e 𝟎 ∎))

    s : (p : Ω 𝓤) → is-decidable (p holds) → is-decidable (e 𝟎 holds) → Fin 2
    s p (inl h) (inl h₀) = 𝟎
    s p (inl h) (inr ν₀) = 𝟏
    s p (inr ν) (inl h₀) = 𝟏
    s p (inr ν) (inr ν₀) = 𝟎

    e⁻¹ : Ω 𝓤 → Fin 2
    e⁻¹ p = s p (em (p holds) (holds-is-prop p))
                (em (e 𝟎 holds) (holds-is-prop (e 𝟎)))

    η' : (p : Ω 𝓤) (d : is-decidable (p holds)) (d' : is-decidable (e 𝟎 holds))
       → e (s p d d') ＝ p
    η' p (inl h) (inl h₀) = to-Ω-＝ fe
                             (pe (holds-is-prop (e 𝟎))
                                 (holds-is-prop p)
                                 (λ _ → h)
                                 (λ _ → h₀))
    η' p (inl h) (inr ν₀) = to-Ω-＝ fe
                             (pe (holds-is-prop (e 𝟏))
                                 (holds-is-prop p)
                                 (λ _ → h)
                                 (λ _ → II₁ ν₀))
    η' p (inr ν) (inl h₀) = to-Ω-＝ fe
                             (pe (holds-is-prop (e 𝟏))
                                 (holds-is-prop p)
                                 (λ (h₁ : e 𝟏 holds) → 𝟘-elim (II₀ h₀ h₁))
                                 λ (h : p holds) → 𝟘-elim (ν h))
    η' p (inr ν) (inr ν₀) = to-Ω-＝ fe
                             (pe (holds-is-prop (e 𝟎))
                                 (holds-is-prop p)
                                 (λ (h₀ : e 𝟎 holds) → 𝟘-elim (ν₀ h₀))
                                 (λ (h : p holds) → 𝟘-elim (ν h)))
    η : e ∘ e⁻¹ ∼ id
    η p = η' p (em (p holds) (holds-is-prop p))
               (em (e 𝟎 holds) (holds-is-prop (e 𝟎)))

  γ : is-equiv e ↔ (2 ＝ 2) × EM 𝓤
  γ = I , II

Fin-to-Ω-embedding-is-equiv-iff-2-and-EM {𝓤} fe pe (succ (succ (succ k))) 𝕖 =
 𝟘-elim I
 where
  I : 3 ≤ 2
  I = finite-subsets-of-Ω-have-at-most-2-elements fe pe (succ (succ (succ k))) 𝕖

\end{code}

TODO. Refactor the above proof in smaller meaningful components.
