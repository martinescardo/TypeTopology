Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
6 November 2024
Refactored between November 2024 and January 2025.

We define types expressing what ordinal exponentiation should be for zero,
successor and supremum exponents, and we record a few properties that follow
immediately follow from those specifications.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.Size
open import UF.Univalence

module Ordinals.Exponentiation.Specification
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.UniverseEmbedding

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' = Univalence-gives-Fun-Ext ua

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

\end{code}

In what follows F should be thought of as implementing ordinal exponentiation
with base α, i.e. F β produces the ordinal α^β.

The three requirements below, together with 𝟘ₒ^β ＝ 𝟘₀ for β ≠ 𝟘₀, classically
*define* ordinal exponentiation.

\begin{code}

module _
        {𝓤 𝓥 : Universe}
        (α : Ordinal 𝓤)
        (F : Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥))
       where

 exp-specification-zero : (𝓤 ⊔ 𝓥) ⁺ ̇
 exp-specification-zero = F (𝟘ₒ {𝓥}) ＝ 𝟙ₒ

 exp-specification-succ : (𝓤 ⊔ 𝓥) ⁺ ̇
 exp-specification-succ = (β : Ordinal 𝓥) → F (β +ₒ 𝟙ₒ) ＝ (F β ×ₒ α)

 exp-specification-sup-generalized : (𝓤 ⊔ 𝓥) ⁺ ̇
 exp-specification-sup-generalized =
  α ≠ 𝟘ₒ → {I : 𝓥 ̇  } → ∥ I ∥ → (β : I → Ordinal 𝓥)
         → F (sup β) ＝ sup (λ (i : Lift 𝓤 I) → F (β (lower i)))

module _
        (α : Ordinal 𝓤)
        (F : Ordinal 𝓤 → Ordinal 𝓤)
       where

 exp-specification-sup : 𝓤 ⁺ ̇
 exp-specification-sup =
  α ≠ 𝟘ₒ → {I : 𝓤 ̇  } → ∥ I ∥ → (β : I → Ordinal 𝓤)
         → F (sup β) ＝ sup (F ∘ β)

 exp-specification-sup-from-generalized : exp-specification-sup-generalized α F
                                        → exp-specification-sup
 exp-specification-sup-from-generalized σ l {I} I-inh β = σ l I-inh β ∙ e
  where
   e : sup (F ∘ β ∘ lower) ＝ sup (F ∘ β)
   e = ⊴-antisym _ _
        (sup-composition-⊴ lower (F ∘ β))
        (sup-composition-⊴ (lift 𝓤) (F ∘ β ∘ lower))

\end{code}

Added 29 January 2025 by Tom de Jong.
Minor changes 15 May 2025 by Fredrik Nordvall Forsberg
\begin{code}

 exp-specification-sup-strong : 𝓤 ⁺ ̇
 exp-specification-sup-strong =
  (I : 𝓤 ̇  ) → (β : I → Ordinal 𝓤)
             → F (sup β) ＝ sup (cases {X = 𝟙{𝓤}} (λ _ → 𝟙ₒ) (F ∘ β))

 exp-specification-sup-strong-implies-monotonicity
  : exp-specification-sup-strong
  → is-monotone (OO 𝓤) (OO 𝓤) F
 exp-specification-sup-strong-implies-monotonicity σ β γ l =
  transport (F β ≼_) (ap F (e ⁻¹)) k
   where
    Δ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
    Δ = cases (λ _ → β) (λ _ → γ)
    e : γ ＝ sup Δ
    e = ⊴-antisym γ (sup Δ)
         (sup-is-upper-bound Δ (inr ⋆))
         (sup-is-lower-bound-of-upper-bounds Δ γ
           (dep-cases (λ _ → ≼-gives-⊴ β γ l) (λ _ → ⊴-refl γ)))
    k : F β ≼ F (sup Δ)
    k = transport⁻¹ (F β ≼_)
                    (σ (𝟙 + 𝟙) Δ)
                    (⊴-gives-≼ (F β)
                      (sup (cases (λ _ → 𝟙ₒ) (F ∘ Δ)))
                      (sup-is-upper-bound _ (inr (inl ⋆))))

 exp-specification-zero-from-strong-sup-specification
  : exp-specification-sup-strong
  → exp-specification-zero α F
 exp-specification-zero-from-strong-sup-specification σ =
  F 𝟘ₒ      ＝⟨ ap F I ⟩
  F (sup ε) ＝⟨ σ 𝟘 ε ⟩
  sup ε'    ＝⟨ II ⟩
  𝟙ₒ        ∎
   where
    ε : 𝟘 → Ordinal 𝓤
    ε = 𝟘-elim
    ε' : 𝟙 + 𝟘 → Ordinal 𝓤
    ε' = cases (λ _ → 𝟙ₒ) (F ∘ ε)
    I : 𝟘ₒ ＝ sup ε
    I = ⊴-antisym 𝟘ₒ (sup ε)
         (𝟘ₒ-least-⊴ (sup ε))
         (sup-is-lower-bound-of-upper-bounds ε 𝟘ₒ 𝟘-induction)
    II : sup ε' ＝ 𝟙ₒ
    II = ⊴-antisym (sup ε') 𝟙ₒ
          (sup-is-lower-bound-of-upper-bounds ε' 𝟙ₒ
            (dep-cases (λ _ → ⊴-refl 𝟙ₒ) 𝟘-induction))
          (sup-is-upper-bound ε' (inl ⋆))

 exp-specification-sup-from-strong : exp-specification-sup-strong
                                   → exp-specification-sup
 exp-specification-sup-from-strong specₛ α-nonzero {I} I-inh β =
  F (sup β)                      ＝⟨ specₛ I β ⟩
  sup (cases (λ _ → 𝟙ₒ) (F ∘ β)) ＝⟨ e ⟩
  sup (F ∘ β)                    ∎
   where
    spec₀ : exp-specification-zero α F
    spec₀ = exp-specification-zero-from-strong-sup-specification specₛ
    F-monotone : is-monotone (OO 𝓤) (OO 𝓤) F
    F-monotone = exp-specification-sup-strong-implies-monotonicity specₛ
    e = ⊴-antisym _ _
         (sup-is-lower-bound-of-upper-bounds
           (cases (λ _ → 𝟙ₒ) (F ∘ β))
           (sup (F ∘ β)) ub)
         (sup-composition-⊴ inr (cases (λ _ → 𝟙ₒ) (λ x → F (β x))))
     where
      ub : (x : 𝟙 + I) → cases (λ _ → 𝟙ₒ) (F ∘ β) x ⊴ sup (F ∘ β)
      ub (inr i) = sup-is-upper-bound (F ∘ β) i
      ub (inl ⋆) = ∥∥-rec (⊴-is-prop-valued 𝟙ₒ (sup (F ∘ β))) ub' I-inh
       where
        ub' : I → 𝟙ₒ ⊴ sup (F ∘ β)
        ub' i = ⊴-trans 𝟙ₒ (F (β i)) (sup (F ∘ β))
                 (≼-gives-⊴ 𝟙ₒ (F (β i))
                   (transport (_≼ F (β i))
                              spec₀
                              (F-monotone 𝟘ₒ (β i) (𝟘ₒ-least (β i)))))
                 (sup-is-upper-bound (F ∘ β) i)

 exp-specification-sup-strong-if-EM : EM 𝓤
                                    → α ≠ 𝟘ₒ
                                    → exp-specification-zero α F
                                    → exp-specification-sup
                                    → exp-specification-sup-strong
 exp-specification-sup-strong-if-EM em α-nonzero spec₀ specₛ I β =
  κ (em ∥ I ∥ ∥∥-is-prop)
  where
    G : 𝟙 + I → Ordinal 𝓤
    G = cases (λ _ → 𝟙ₒ) (F ∘ β)
    κ : is-decidable ∥ I ∥ → F (sup β) ＝ sup G
    κ (inl I-inh) = ∥∥-rec (underlying-type-is-set fe (OO 𝓤)) h I-inh
     where
      h : I → F (sup β) ＝ sup G
      h i = F (sup β) ＝⟨ specₛ α-nonzero I-inh β ⟩
            sup (F ∘ β) ＝⟨ ⊴-antisym (sup (F ∘ β)) (sup G) h₁ h₂ ⟩
            sup G ∎
       where
        h₁ : sup (F ∘ β) ⊴ sup G
        h₁ = sup-composition-⊴ inr G
        h₂ : sup G ⊴ sup (F ∘ β)
        h₂ = sup-is-lower-bound-of-upper-bounds G (sup (F ∘ β)) h₃
         where
          h₃ : (x : 𝟙 + I) → G x ⊴ sup (F ∘ β)
          h₃ (inr i) = sup-is-upper-bound (F ∘ β) i
          h₃ (inl ⋆) =
           ⊴-trans 𝟙ₒ (F (β i)) (sup (F ∘ β))
            (≼-gives-⊴ 𝟙ₒ (F (β i))
              (transport (_≼ F (β i))
                         spec₀
                         (is-monotone-if-continuous F
                           (specₛ α-nonzero)
                           𝟘ₒ
                           (β i)
                           (𝟘ₒ-least (β i)))))
            (sup-is-upper-bound (F ∘ β) i)
    κ (inr I-empty) =
     F (sup β) ＝⟨ ap F e₁ ⟩
     F 𝟘ₒ      ＝⟨ spec₀ ⟩
     𝟙ₒ        ＝⟨ e₂ ⁻¹ ⟩
     sup G     ∎
      where
       e₁ : sup β ＝ 𝟘ₒ
       e₁ = ⊴-antisym (sup β) 𝟘ₒ
             (sup-is-lower-bound-of-upper-bounds β 𝟘ₒ
               (λ i → 𝟘-elim (I-empty ∣ i ∣)))
             (𝟘ₒ-least-⊴ (sup β))
       e₂ : sup G ＝ 𝟙ₒ
       e₂ = ⊴-antisym (sup G) 𝟙ₒ
             (sup-is-lower-bound-of-upper-bounds G 𝟙ₒ
               (dep-cases (λ _ → ⊴-refl 𝟙ₒ) (λ i → 𝟘-elim (I-empty ∣ i ∣))))
             (sup-is-upper-bound G (inl ⋆))

\end{code}

The appealing thing about the strong supremum specification is that, together
with the successor specification, it uniquely specifies exponentiation with a
nonzero base.

\begin{code}

exp-strong-specification-uniquely-specifies-exp'
 : (α : Ordinal 𝓤)
 → (F G : Ordinal 𝓤 → Ordinal 𝓤)
 → exp-specification-sup-strong α F
 → exp-specification-succ α F
 → exp-specification-sup-strong α G
 → exp-specification-succ α G
 → F ∼ G
exp-strong-specification-uniquely-specifies-exp' {𝓤} α F G F-eq₁ F-eq₂ G-eq₁ G-eq₂ =
 transfinite-induction-on-OO _ e
  where
   e : (β : Ordinal 𝓤)
     → ((b : ⟨ β ⟩) → F (β ↓ b) ＝ G (β ↓ b))
     → F β ＝ G β
   e β IH =
     F β                                              ＝⟨ I   ⟩
     F (sup λ b → (β ↓ b) +ₒ 𝟙ₒ)                      ＝⟨ II  ⟩
     sup (cases (λ _ → 𝟙ₒ) (λ b → F ((β ↓ b) +ₒ 𝟙ₒ))) ＝⟨ III ⟩
     sup (cases (λ _ → 𝟙ₒ) (λ b → F (β ↓ b) ×ₒ α))    ＝⟨ IV  ⟩
     sup (cases (λ _ → 𝟙ₒ) (λ b → G (β ↓ b) ×ₒ α))    ＝⟨ V   ⟩
     sup (cases (λ _ → 𝟙ₒ) (λ b → G ((β ↓ b) +ₒ 𝟙ₒ))) ＝⟨ VI  ⟩
     G (sup (λ b → (β ↓ b) +ₒ 𝟙ₒ))                    ＝⟨ VII ⟩
     G β                                              ∎
      where
       I   = ap F (supremum-of-successors-of-initial-segments pt sr β)
       II  = F-eq₁ ⟨ β ⟩ (λ b → (β ↓ b) +ₒ 𝟙ₒ)
       III = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → 𝟙ₒ) -))
                (dfunext fe' (λ b → F-eq₂ (β ↓ b)))
       IV  = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → 𝟙ₒ) -))
                (dfunext fe' (λ b → ap (_×ₒ α) (IH b)))
       V   = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → 𝟙ₒ) -))
                (dfunext fe' (λ b → (G-eq₂ (β ↓ b)) ⁻¹))
       VI  = (G-eq₁ ⟨ β ⟩ (λ b → (β ↓ b) +ₒ 𝟙ₒ)) ⁻¹
       VII = ap G ((supremum-of-successors-of-initial-segments pt sr β) ⁻¹)

exp-strong-specification-uniquely-specifies-exp
 : (α : Ordinal 𝓤)
 → α ≠ 𝟘ₒ
 → is-prop (Σ F ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , exp-specification-sup-strong α F
                                          × exp-specification-succ α F)
exp-strong-specification-uniquely-specifies-exp {𝓤} α α-nonzero =
 (λ (F , F-eq₁ , F-eq₂) (G , G-eq₁ , G-eq₂)
   → to-subtype-＝
      (λ H → ×-is-prop
              (Π₂-is-prop fe' (λ _ _ → underlying-type-is-set fe (OO 𝓤)))
              (Π-is-prop fe' (λ _ → underlying-type-is-set fe (OO 𝓤))))
              (dfunext fe'
                (exp-strong-specification-uniquely-specifies-exp' α
                  F G F-eq₁ F-eq₂ G-eq₁ G-eq₂)))

\end{code}

The following special cases follow directly from the specification.

\begin{code}

module _
        (α : Ordinal 𝓤)
        (exp-α : Ordinal 𝓤 → Ordinal 𝓤)
        (exp-zero : exp-specification-zero α exp-α)
        (exp-succ : exp-specification-succ α exp-α)
 where

 𝟙ₒ-neutral-exp : exp-α 𝟙ₒ ＝ α
 𝟙ₒ-neutral-exp =
  exp-α 𝟙ₒ             ＝⟨ ap (exp-α) (𝟘ₒ-left-neutral 𝟙ₒ ⁻¹)  ⟩
  exp-α (𝟘ₒ {𝓤} +ₒ 𝟙ₒ) ＝⟨ exp-succ 𝟘ₒ ⟩
  exp-α (𝟘ₒ) ×ₒ α      ＝⟨ ap (_×ₒ α) exp-zero ⟩
  𝟙ₒ ×ₒ α              ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
  α                    ∎

 exp-𝟚ₒ-is-×ₒ : exp-α 𝟚ₒ ＝ α ×ₒ α
 exp-𝟚ₒ-is-×ₒ =
  exp-α (𝟙ₒ +ₒ 𝟙ₒ) ＝⟨ exp-succ 𝟙ₒ ⟩
  exp-α 𝟙ₒ ×ₒ α    ＝⟨ ap (_×ₒ α) 𝟙ₒ-neutral-exp ⟩
  α ×ₒ α           ∎

\end{code}

The specification for suprema implies monotonicity.

\begin{code}

exp-is-monotone-in-exponent : (α : Ordinal 𝓤)
                              (exp-α : Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥))
                            → (α ≠ 𝟘ₒ)
                            → exp-specification-sup-generalized α exp-α
                            → is-monotone (OO 𝓥) (OO (𝓤 ⊔ 𝓥)) exp-α
exp-is-monotone-in-exponent α exp-α ν exp-sup =
 is-monotone-if-continuous-generalized exp-α (exp-sup ν)

\end{code}
