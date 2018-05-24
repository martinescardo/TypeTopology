Excluded middle related things.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Two-Prop-Density where

open import UF-Base
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Embedding
open import UF-PropTrunc

\end{code}

Excluded middle (EM) is not provable or disprovable. However, we do
have that there is no truth value other than false (⊥) or true (⊤),
which we refer to as the density of the decidable truth values.

\begin{code}

EM : ∀ U → U ′ ̇
EM U = (P : U ̇) → is-prop P → P + ¬ P

WEM : ∀ U → U ′ ̇
WEM U = (P : U ̇) → is-prop P → ¬ P + ¬¬ P

DNE : ∀ U → U ′ ̇
DNE U = (P : U ̇) → is-prop P → ¬¬ P → P

EM-DNE : ∀ {U} → EM U → DNE U
EM-DNE em P isp φ = cases (λ p → p) (λ u → 𝟘-elim (φ u)) (em P isp)

DNE-EM : ∀ {U} → funext U U₀ → DNE U → EM U
DNE-EM fe dne P isp = dne (P + ¬ P)
                          (decidable-is-prop fe isp)
                          (λ u → u (inr (λ p → u (inl p))))

module _ (pt : PropTrunc) where

 open PropositionalTruncation pt

 double-negation-is-truncation-gives-DNE : ∀ {U} → ((X : U ̇) → ¬¬ X → ∥ X ∥) → DNE U
 double-negation-is-truncation-gives-DNE {U} f P isp u = ptrec isp id (f P u)
 
fem-proptrunc : ∀ {U} → funext U U₀ → EM U → propositional-truncations-exist U U
fem-proptrunc fe em X = ¬¬ X ,
                    (is-prop-exponential-ideal fe (λ _ → 𝟘-is-prop) ,
                     (λ x u → u x) ,
                     λ P isp u φ → EM-DNE em P isp (¬¬-functor u φ))

no-props-other-than-𝟘-or-𝟙 : propext U₀ → ¬ Σ \(P : U₀ ̇) → is-prop P × (P ≢ 𝟘) × (P ≢ 𝟙)  
no-props-other-than-𝟘-or-𝟙 pe (P , (isp , f , g)) = φ u
 where
   u : ¬ P
   u p = g l
     where
       l : P ≡ 𝟙
       l = pe isp 𝟙-is-prop unique-to-𝟙 (λ _ → p)
   φ : ¬¬ P
   φ u = f l
     where
       l : P ≡ 𝟘
       l = pe isp 𝟘-is-prop u 𝟘-elim

𝟘-is-not-𝟙 : 𝟘 ≢ 𝟙
𝟘-is-not-𝟙 p = idtofun' 𝟙 𝟘 (p ⁻¹) *

⊥≠⊤ : ⊥ ≢ ⊤
⊥≠⊤ p = 𝟘-is-not-𝟙 (ap pr₁ p)

no-truth-values-other-than-⊥-or-⊤ : funext U₀ U₀ → propext U₀
                                   → ¬ Σ \(p : Ω) → (p ≢ ⊥) × (p ≢ ⊤)  
no-truth-values-other-than-⊥-or-⊤ fe pe ((P , isp) , (f , g)) = φ u
 where
   u : ¬ P
   u p = g l
     where
       l : (P , isp) ≡ ⊤
       l = PropExt fe pe unique-to-𝟙 (λ _ → p)
   φ : ¬¬ P
   φ u = f l
     where
       l : (P , isp) ≡ ⊥
       l = PropExt fe pe u unique-from-𝟘

⊥-⊤-density : funext U₀ U₀ → propext U₀ → (f : Ω → 𝟚)
            → f ⊥ ≡ ₁ → f ⊤ ≡ ₁ → (p : Ω) → f p ≡ ₁
⊥-⊤-density fe pe f r s p = Lemma[b≢₀→b≡₁] a
 where
    a : f p ≢ ₀
    a t = no-truth-values-other-than-⊥-or-⊤ fe pe (p , (b , c))
      where
        b : p ≢ ⊥
        b u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ r)
        c : p ≢ ⊤
        c u = zero-is-not-one (t ⁻¹ ∙ ap f u ∙ s)

𝟚inΩ : 𝟚 → Ω
𝟚inΩ ₀ = ⊥
𝟚inΩ ₁ = ⊤

𝟚inΩ-embedding : funext U₀ U₀ → propext U₀ → is-embedding 𝟚inΩ
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₀ , q) = to-Σ-≡ ₀ ₀ p q refl (Ω-is-set fe pe p q)
𝟚inΩ-embedding fe pe (P , isp) (₀ , p) (₁ , q) = 𝟘-elim (⊥≠⊤ (p ∙ q ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₀ , q) = 𝟘-elim (⊥≠⊤ (q ∙ p ⁻¹))
𝟚inΩ-embedding fe pe (P , isp) (₁ , p) (₁ , q) = to-Σ-≡ ₁ ₁ p q refl (Ω-is-set fe pe p q)

\end{code}
