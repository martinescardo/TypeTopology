Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
6 November 2024
Refactored between November 2024 and January 2025.
Revised October 2026.

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

-- TODO
open import Ordinals.SupremaPreservation ua pt sr

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
Minor changes 15 May 2025 by Fredrik Nordvall Forsberg.
Revised 14 October 2026 by Tom de Jong, following an observation by Nicolai Kraus.

TODO: COMMENT AND REVISE.

\begin{code}

 exp-specification-sup' : 𝓤 ⁺ ̇
 exp-specification-sup' = preserves-suprema-up-to-join 𝟙ₒ F

 exp-specification-sup-from-sup' : exp-specification-sup'
                                 → exp-specification-sup
 exp-specification-sup-from-sup' σ _ =
  pr₂ (rl-implication (preservation-of-suprema-equivalence 𝟙ₒ F) σ)

 exp-specification-sup'-from--sup-and-zero
  : α ≠ 𝟘ₒ
  → exp-specification-zero α F × exp-specification-sup
  → exp-specification-sup'
 exp-specification-sup'-from--sup-and-zero α-nonzero (σ₀ , σₛ) =
  lr-implication (preservation-of-suprema-equivalence 𝟙ₒ F)
                 (σ₀ , (σₛ α-nonzero))

 open import Notation.General
 exp-specification-sup-strong = exp-specification-sup'

\end{code}

The appealing thing about the strong supremum specification is that, together
with the successor specification, it uniquely specifies exponentiation with a
nonzero base.

\begin{code}

exp-strong-specification-uniquely-specifies-exp'
 : (α : Ordinal 𝓤)
 → (F G : Ordinal 𝓤 → Ordinal 𝓤)
 → exp-specification-sup' α F
 → exp-specification-succ α F
 → exp-specification-sup' α G
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
       II  = F-eq₁ {⟨ β ⟩} (λ b → (β ↓ b) +ₒ 𝟙ₒ)
       III = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → 𝟙ₒ) -))
                (dfunext fe' (λ b → F-eq₂ (β ↓ b)))
       IV  = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → 𝟙ₒ) -))
                (dfunext fe' (λ b → ap (_×ₒ α) (IH b)))
       V   = ap (λ - → sup (cases (λ (_ : 𝟙{𝓤}) → 𝟙ₒ) -))
                (dfunext fe' (λ b → (G-eq₂ (β ↓ b)) ⁻¹))
       VI  = (G-eq₁ {⟨ β ⟩} (λ b → (β ↓ b) +ₒ 𝟙ₒ)) ⁻¹
       VII = ap G ((supremum-of-successors-of-initial-segments pt sr β) ⁻¹)

exp-specification-uniquely-specifies-exp
 : (α : Ordinal 𝓤)
 → α ≠ 𝟘ₒ
 → is-prop (Σ F ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , exp-specification-sup' α F
                                          × exp-specification-succ α F)
exp-specification-uniquely-specifies-exp {𝓤} α α-nonzero =
 (λ (F , F-eq₁ , F-eq₂) (G , G-eq₁ , G-eq₂)
   → to-subtype-＝
      (λ H → ×-is-prop
              (implicit-Π-is-prop fe'
                (λ _ → Π-is-prop fe' (λ _ → underlying-type-is-set fe (OO 𝓤))))
              (Π-is-prop fe' (λ _ → underlying-type-is-set fe (OO 𝓤))))
      (dfunext fe'
        (exp-strong-specification-uniquely-specifies-exp'
          α F G F-eq₁ F-eq₂ G-eq₁ G-eq₂)))

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
 is-monotone-if-preserves-inhabited-suprema-generalized exp-α (exp-sup ν)

\end{code}
