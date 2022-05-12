Tom de Jong, 5 April 2022, after discussion with Martín.
(Refactoring an earlier addition dated 15 March 2022.)

The construction of set quotients in UF-Large-Quotients.lagda takes a type X : 𝓤
and a 𝓥-valued equivalence relation and constructs the quotient as a type in 𝓥 ⁺
⊔ 𝓤.

If we assume Set Replacement, as defined and explained in UF-Size.lagda, then we
get a quotient in 𝓥 ⊔ 𝓤. In particular, for a 𝓤-valued equivalence relation on a
type X : 𝓤, the quotient will live in the same universe 𝓤. This particular case
was first proved in [Corollary 5.1, Rijke2017], but under a different
replacement assumption (again, see UF-Size.lagda for details).

[Rijke2017]  Egbert Rijke. The join construction.
             https://arxiv.org/abs/1701.07538, January 2017.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module UF-Quotient-Replacement
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import SpartanMLTT

open import UF-Base hiding (_≈_)
open import UF-Subsingletons-FunExt
open import UF-ImageAndSurjection
open import UF-Equiv

open import UF-Large-Quotient pt fe pe
open import UF-Quotient using (set-quotients-exist)
open import UF-Size

module _
        (R : Set-Replacement pt)
        {X : 𝓤 ̇  }
        (≋@(_≈_ , ≈p , ≈r , ≈s , ≈t) : EqRel {𝓤} {𝓥} X)
       where

 open import UF-Equiv
 open import UF-EquivalenceExamples

 abstract
  resize-set-quotient : (X / ≋) is (𝓤 ⊔ 𝓥) small
  resize-set-quotient = R equiv-rel (X , (≃-refl X)) γ
                          (powersets-are-sets'' fe fe pe)
   where
    open quotient X _≈_ ≈p ≈r ≈s ≈t using (equiv-rel)
    γ : (X → Ω 𝓥) is-locally 𝓤 ⊔ 𝓥 small
    γ f g = S , ≃-sym e
     where
      S : 𝓤 ⊔ 𝓥 ̇
      S = (x : X) → f x holds ⇔ g x holds
      e : (f ≡ g) ≃ S
      e = (f ≡ g) ≃⟨ ≃-funext fe f g ⟩
          f ∼ g   ≃⟨ I ⟩
          S       ■
       where
        I : (f ∼ g) ≃ S
        I = Π-cong fe fe X (λ x → f x ≡ g x) (λ x → f x holds ⇔ g x holds) II
         where
          II : (x : X) → (f x ≡ g x) ≃ (f x holds ⇔ g x holds)
          II x = logically-equivalent-props-are-equivalent
                  (Ω-is-set fe pe)
                  (×-is-prop (Π-is-prop fe (λ _ → holds-is-prop (g x)))
                             (Π-is-prop fe (λ _ → holds-is-prop (f x))))
                  (λ p → transport _holds p , transport⁻¹ _holds p)
                  (λ (u , v) → Ω-extensionality fe pe u v)

\end{code}

We now use the above resizing to construct a quotient that strictly lives in the
universe 𝓤 ⊔ 𝓥, yielding set quotients as defined in
UF-Quotient.lagda.

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
 /ₛ-is-set = equiv-to-set φ (quotient-is-set ≋)
 /ₛ-induction : ∀ {𝓦} {P : X/ₛ≈ → 𝓦 ̇ }
              → ((x' : X/ₛ≈) → is-prop (P x'))
              → ((x : X) → P (η/ₛ x))
              → (x' : X/ₛ≈) → P x'
 /ₛ-induction {𝓦} {P} i h x' = transport P e (γ (⌜ φ ⌝ x'))
  where
   P' : X / ≋ → 𝓦 ̇
   P' = P ∘ ⌜ φ ⌝⁻¹
   γ : (y : X / ≋) → P' y
   γ = /-induction' ≋ (λ y → i (⌜ φ ⌝⁻¹ y)) h
   e : ⌜ φ ⌝⁻¹ (⌜ φ ⌝ x') ≡ x'
   e = ≃-sym-is-linv φ x'
 /ₛ-universality : {A : 𝓦 ̇  } → is-set A
                 → (f : X → A)
                 → identifies-related-points ≋ f
                 → ∃! f' ꞉ (X/ₛ≈ → A), f' ∘ η/ₛ ∼ f
 /ₛ-universality {𝓦} {A} i f p =
  equiv-to-singleton (≃-sym e) (universal-property/ ≋ i f p)
   where
    e = (Σ f' ꞉ (X / ≋ → A)  , f' ∘ η/ ≋ ≡ f)        ≃⟨ ⦅1⦆ ⟩
        (Σ f' ꞉ (X / ≋ → A)  , f' ∘ η/ ≋ ∼ f)        ≃⟨ ⦅2⦆ ⟩
        (Σ f' ꞉ (X / ≋ → A)  , f' ∘ ⌜ φ ⌝ ∘ η/ₛ ∼ f) ≃⟨ ⦅3⦆ ⟩
        (Σ f' ꞉ (X/ₛ≈ → A) , f' ∘ η/ₛ ∼ f)         ■
     where
      ⦅1⦆ = Σ-cong (λ f' → ≃-funext fe (f' ∘ η/ ≋) f)
      ⦅2⦆ = Σ-cong
            (λ f' → Π-cong fe fe X _ _
                    (λ x → ≡-cong-l (f' (η/ ≋ x)) (f x)
                                    (ap f' ((≃-sym-is-rinv φ (η/ ≋ x)) ⁻¹))))
      ⦅3⦆ = Σ-change-of-variable _ (_∘ ⌜ φ ⌝)
            (qinvs-are-equivs (_∘ ⌜ φ ⌝)
              (qinv-pre (λ _ _ → dfunext fe) ⌜ φ ⌝
               (equivs-are-qinvs ⌜ φ ⌝ (⌜⌝-is-equiv φ))))
       where
        open import UF-Equiv-FunExt using (qinv-pre)

set-replacement-gives-set-quotients : Set-Replacement pt → set-quotients-exist
set-replacement-gives-set-quotients R = record
 { _/_                          = λ X → X/ₛ≈ R
 ; η/                           = η/ₛ R
 ; η/-identifies-related-points = η/ₛ-identifies-related-points R
 ; /-is-set                     = /ₛ-is-set R
 ; /-induction                  = /ₛ-induction R
 ; /-universality               = /ₛ-universality R
 }

\end{code}
