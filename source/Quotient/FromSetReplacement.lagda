Tom de Jong, 5 April 2022, after discussion with Martín Escardó.
(Refactoring an earlier addition dated 15 March 2022.)

The construction of set quotients in Quotient.Large takes a type X : 𝓤
and a 𝓥-valued equivalence relation and constructs the quotient as a
type in 𝓥 ⁺ ⊔ 𝓤.

If we assume Set Replacement, as defined and explained in UF.Size.lagda, then we
get a quotient in 𝓥 ⊔ 𝓤. In particular, for a 𝓤-valued equivalence relation on a
type X : 𝓤, the quotient will live in the same universe 𝓤. This particular case
was first proved in [Corollary 5.1, Rijke2017], but under a different
replacement assumption (again, see UF.Size.lagda for details).

[Rijke2017]  Egbert Rijke. The join construction.
             https://arxiv.org/abs/1701.07538, January 2017.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Quotient.FromSetReplacement
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import MLTT.Spartan

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Powerset
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open import Quotient.Large pt fe pe
open import Quotient.Type -- using (set-quotients-exist ; is-effective ; EqRel)

open general-set-quotients-exist large-set-quotients

module _
        (R : Set-Replacement pt)
        {X : 𝓤 ̇ }
        (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
       where

 abstract
  resize-set-quotient : (X / ≋) is (𝓤 ⊔ 𝓥) small
  resize-set-quotient = R equiv-rel (X , (≃-refl X)) γ
                          (powersets-are-sets'' fe fe pe)
   where
    open large-quotient X ≋ using (equiv-rel)
    γ : (X → Ω 𝓥) is-locally 𝓤 ⊔ 𝓥 small
    γ f g = S , ≃-sym e
     where
      S : 𝓤 ⊔ 𝓥 ̇
      S = (x : X) → f x holds ↔ g x holds
      e : (f ＝ g) ≃ S
      e = (f ＝ g) ≃⟨ ≃-funext fe f g ⟩
          f ∼ g   ≃⟨ I ⟩
          S       ■
       where
        I : (f ∼ g) ≃ S
        I = Π-cong fe fe II
         where
          II : (x : X) → (f x ＝ g x) ≃ (f x holds ↔ g x holds)
          II x = logically-equivalent-props-are-equivalent
                  (Ω-is-set fe pe)
                  (×-is-prop (Π-is-prop fe (λ _ → holds-is-prop (g x)))
                             (Π-is-prop fe (λ _ → holds-is-prop (f x))))
                  (λ p → transport _holds p , transport⁻¹ _holds p)
                  (λ (u , v) → Ω-extensionality pe fe u v)

\end{code}

We now use the above resizing to construct a quotient that strictly
lives in the universe 𝓤 ⊔ 𝓥, yielding set quotients as defined in
Quotient.Type.

\begin{code}

 X/ₛ≈ : 𝓤 ⊔ 𝓥 ̇
 X/ₛ≈ = pr₁ resize-set-quotient
 φ : X/ₛ≈ ≃ X / ≋
 φ = pr₂ resize-set-quotient
 η/ₛ : X → X/ₛ≈
 η/ₛ = ⌜ φ ⌝⁻¹  ∘ η/ ≋
 η/ₛ-identifies-related-points : identifies-related-points ≋ η/ₛ
 η/ₛ-identifies-related-points e = ap ⌜ φ ⌝⁻¹ (η/-identifies-related-points ≋ e)
 /ₛ-is-set : is-set (X/ₛ≈)
 /ₛ-is-set = equiv-to-set φ (/-is-set ≋)
 /ₛ-induction : ∀ {𝓦} {P : X/ₛ≈ → 𝓦 ̇ }
              → ((x' : X/ₛ≈) → is-prop (P x'))
              → ((x : X) → P (η/ₛ x))
              → (x' : X/ₛ≈) → P x'
 /ₛ-induction {𝓦} {P} i h x' = transport P e (γ (⌜ φ ⌝ x'))
  where
   P' : X / ≋ → 𝓦 ̇
   P' = P ∘ ⌜ φ ⌝⁻¹
   γ : (y : X / ≋) → P' y
   γ = /-induction ≋ (λ y → i (⌜ φ ⌝⁻¹ y)) h
   e : ⌜ φ ⌝⁻¹ (⌜ φ ⌝ x') ＝ x'
   e = ≃-sym-is-linv φ x'
 /ₛ-universality : {A : 𝓦 ̇ } → is-set A
                 → (f : X → A)
                 → identifies-related-points ≋ f
                 → ∃! f' ꞉ (X/ₛ≈ → A), f' ∘ η/ₛ ∼ f
 /ₛ-universality {𝓦} {A} i f p =
  equiv-to-singleton (≃-sym e) (/-universality ≋ i f p)
   where
    e = (Σ f' ꞉ (X / ≋ → A)  , f' ∘ η/ ≋ ∼ f)        ≃⟨ ⦅1⦆ ⟩
        (Σ f' ꞉ (X / ≋ → A)  , f' ∘ ⌜ φ ⌝ ∘ η/ₛ ∼ f) ≃⟨ ⦅2⦆ ⟩
        (Σ f' ꞉ (X/ₛ≈ → A) , f' ∘ η/ₛ ∼ f)         ■
     where
      ⦅1⦆ = Σ-cong
            (λ f' → Π-cong fe fe (λ x → ＝-cong-l (f' (η/ ≋ x)) (f x)
                                    (ap f' ((≃-sym-is-rinv φ (η/ ≋ x)) ⁻¹))))
      ⦅2⦆ = Σ-change-of-variable _ (_∘ ⌜ φ ⌝)
            (qinvs-are-equivs (_∘ ⌜ φ ⌝)
              (qinv-pre (λ _ _ → dfunext fe) ⌜ φ ⌝
               (equivs-are-qinvs ⌜ φ ⌝ (⌜⌝-is-equiv φ))))
       where
        open import UF.Equiv-FunExt using (qinv-pre)

 η/ₛ-relates-identified-points : {x y : X} → η/ₛ x ＝ η/ₛ y → x ≈ y
 η/ₛ-relates-identified-points {x} {y} eₛ = large-effective-set-quotients ≋ e
  where
   note : ⌜ φ ⌝⁻¹ (η/ ≋ x) ＝ ⌜ φ ⌝⁻¹ (η/ ≋ y)
   note = eₛ
   e = η/ ≋ x                   ＝⟨ (≃-sym-is-rinv φ (η/ ≋ x)) ⁻¹ ⟩
       ⌜ φ ⌝ (⌜ φ ⌝⁻¹ (η/ ≋ x)) ＝⟨ ap ⌜ φ ⌝ note ⟩
       ⌜ φ ⌝ (⌜ φ ⌝⁻¹ (η/ ≋ y)) ＝⟨ ≃-sym-is-rinv φ (η/ ≋ y) ⟩
       η/ ≋ y                   ∎

set-quotients-from-set-replacement : Set-Replacement pt → set-quotients-exist
set-quotients-from-set-replacement R = record
 { _/_                          = λ X → X/ₛ≈ R
 ; η/                           = η/ₛ R
 ; η/-identifies-related-points = η/ₛ-identifies-related-points R
 ; /-is-set                     = /ₛ-is-set R
 ; /-universality               = /ₛ-universality R
 }

set-replacement-gives-effective-set-quotients
 : (sr : Set-Replacement pt)
 → are-effective (set-quotients-from-set-replacement sr)
set-replacement-gives-effective-set-quotients sr {𝓤} {𝓥} R {x} {y} =
 η/ₛ-relates-identified-points sr R

\end{code}
