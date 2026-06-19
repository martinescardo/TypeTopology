Tom de Jong
Reboot: 22 January 2021
Earlier version: 18 September 2020

We show that the type of integers enjoys the symmetric induction principle, as
used in constructing the circle as the type of ℤ-torsors. The symmetric
induction principle appears as Theorem 3.13 in "Construction of the circle in
UniMath" by Bezem, Buchholtz, Grayson and Shulman
(doi:10.1016/j.jpaa.2021.106687).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Naturals.UniversalProperty

open import SyntheticHomotopyTheory.Circle.Integers
open import SyntheticHomotopyTheory.Circle.Integers-Properties

open import MLTT.Spartan
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Subsingletons

module SyntheticHomotopyTheory.Circle.Integers-SymmetricInduction where

ℤ-symmetric-induction : {𝓤 : Universe}
                      → funext 𝓤₀ 𝓤
                      → (A : ℤ → 𝓤 ̇ )
                        (f : (z : ℤ) → A z ≃ A (succ-ℤ z))
                      → (Σ h ꞉ Π A , ((z : ℤ) → h (succ-ℤ z) ＝ ⌜ f z ⌝ (h z)))
                      ≃ A 𝟎
ℤ-symmetric-induction {𝓤} fe A f =
 (Σ h ꞉ Π A , Q₁ h)                                               ≃⟨ I    ⟩
 (Σ h ꞉ (Π (A ∘ ⌜𝟎⌝) × Π (A ∘ inr)) , Q₁ (g₁ h))                  ≃⟨ II   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hᵣ ꞉ Π (A ∘ inr) , Q₁ (g₁ (hₒ , hᵣ)))    ≃⟨ III  ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hᵣ ꞉ (Π (A ∘ pos) × Π (A ∘ neg)),
                         Q₂ hₒ (g₂ hᵣ))                           ≃⟨ IV   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₚ ꞉ Π (A ∘ pos) ,
                       Σ hₙ ꞉ Π (A ∘ neg) , Q₂ hₒ (g₂ (hₚ , hₙ))) ≃⟨ V    ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₚ ꞉ Π (A ∘ pos) ,
                       Σ hₙ ꞉ Π (A ∘ neg) , Qₚ (hₒ ⋆) hₚ
                                          × Qₙ' (hₒ ⋆) hₙ)        ≃⟨ VI   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , ((Σ hₚ ꞉ Π (A ∘ pos) , Qₚ (hₒ ⋆) hₚ)
                     ×  (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ ⋆) hₙ)))    ≃⟨ VII  ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , 𝟙 × (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ ⋆) hₙ))  ≃⟨ VIII ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ ⋆) hₙ)        ≃⟨ IX   ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , Σ hₙ ꞉ Π (A ∘ neg) , Qₙ (hₒ ⋆) hₙ)         ≃⟨ X    ⟩
 (Σ hₒ ꞉ Π (A ∘ ⌜𝟎⌝) , 𝟙)                                         ≃⟨ XI   ⟩
 Π (A ∘ ⌜𝟎⌝)                                                      ≃⟨ XII  ⟩
 A 𝟎 ■
  where
   ⌜𝟎⌝ : 𝟙 {𝓤₀} → ℤ
   ⌜𝟎⌝ _ = 𝟎
   Q₁ : Π A → 𝓤 ̇
   Q₁ h = (z : ℤ) → h (succ-ℤ z) ＝ ⌜ f z ⌝ (h z)
   g₁ : Π (A ∘ ⌜𝟎⌝) × Π (A ∘ inr) → Π A
   g₁ = ⌜ Π×+ fe ⌝
   Q₂ : Π (A ∘ ⌜𝟎⌝) → Π (A ∘ inr) → 𝓤 ̇
   Q₂ hₒ hᵣ = Q₁ (g₁ (hₒ , hᵣ))
   g₂ : Π (A ∘ pos) × Π (A ∘ neg) → Π (A ∘ inr)
   g₂ = ⌜ Π×+ fe ⌝
   Qₚ : A 𝟎 → Π (A ∘ pos) → 𝓤 ̇
   Qₚ aₒ hₚ = (hₚ 0 ＝ ⌜ f 𝟎 ⌝ aₒ)
            × ((n : ℕ) → hₚ (succ n) ＝ ⌜ f (pos n) ⌝ (hₚ n))
   Qₙ' : A 𝟎 → Π (A ∘ neg) → 𝓤 ̇
   Qₙ' a₀ hₙ = (a₀ ＝ ⌜ f (neg 0) ⌝ (hₙ 0))
             × ((n : ℕ) → hₙ n ＝ ⌜ f (neg (succ n)) ⌝ (hₙ (succ n)))
   Qₙ : A 𝟎 → Π (A ∘ neg) → 𝓤 ̇
   Qₙ aₒ hₙ = (hₙ 0 ＝ ⌜ (f (neg 0)) ⌝⁻¹ aₒ)
            × ((n : ℕ) → hₙ (succ n) ＝ ⌜ (f (neg (succ n))) ⌝⁻¹ (hₙ n))
   I    = ≃-sym (Σ-change-of-variable Q₁ g₁ (⌜⌝-is-equiv (Π×+ fe)))
   II   = Σ-assoc
   III  = Σ-cong
          (λ hₒ → ≃-sym (Σ-change-of-variable (Q₂ hₒ) g₂ (⌜⌝-is-equiv (Π×+ fe))))
   IV   = Σ-cong (λ _ → Σ-assoc)
   V    = Σ-cong λ hₒ → Σ-cong (λ hₚ → Σ-cong (λ hₙ → γ hₒ hₚ hₙ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))  (hₚ : Π (A ∘ pos)) (hₙ : Π (A ∘ neg))
       → Q₂ hₒ (g₂ (hₚ , hₙ)) ≃ Qₚ (hₒ ⋆) hₚ × Qₙ' (hₒ ⋆) hₙ
     γ hₒ hₚ hₙ = qinveq φ (ψ , η , ε)
      where
       φ : Q₂ hₒ (g₂ (hₚ , hₙ)) → Qₚ (hₒ ⋆) hₚ × Qₙ' (hₒ ⋆) hₙ
       φ q = ((q 𝟎 , q ∘ pos) , (q (neg 0) , q ∘ neg ∘ succ))
       ψ : (Qₚ (hₒ ⋆) hₚ × Qₙ' (hₒ ⋆) hₙ) → Q₂ hₒ (g₂ (hₚ , hₙ))
       ψ ((qₒ , qₚ) , (qₒ' , qₙ')) = c
        where
         c : Q₂ hₒ (g₂ (hₚ , hₙ))
         c 𝟎              = qₒ
         c (pos n)        = qₚ n
         c (neg zero)     = qₒ'
         c (neg (succ n)) = qₙ' n
       ε : φ ∘ ψ ∼ id
       ε q = refl
       η : ψ ∘ φ ∼ id
       η q = dfunext fe c
        where
         c : (z : ℤ) → (ψ (φ q)) z ＝ q (z)
         c 𝟎              = refl
         c (pos n)        = refl
         c (neg zero)     = refl
         c (neg (succ n)) = refl
   VI   = Σ-cong γ
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → (Σ hₚ ꞉ Π (A ∘ pos) , Σ hₙ ꞉ Π (A ∘ neg) , Qₚ (hₒ ⋆) hₚ × Qₙ' (hₒ ⋆) hₙ)
       ≃ (  (Σ hₚ ꞉ Π (A ∘ pos) , Qₚ (hₒ ⋆) hₚ)
          × (Σ hₙ ꞉ Π (A ∘ neg) , Qₙ' (hₒ ⋆) hₙ))
     γ hₒ = Σ-interchange
   VII  = Σ-cong (λ hₒ → ×-cong (singleton-≃-𝟙 {𝓤} {𝓤₀} (γ hₒ)) (≃-refl _))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → is-singleton ((Σ hₚ ꞉ Π (A ∘ pos) , Qₚ  (hₒ ⋆) hₚ))
     γ hₒ = (ℕ-is-nno-dep fe (A ∘ pos) a₀ s)
      where
       a₀ : A (pos 0)
       a₀ = ⌜ (f 𝟎) ⌝ (hₒ ⋆)
       s : (n : ℕ) → A (pos n) → A (pos (succ n))
       s n = ⌜ f (pos n) ⌝
   VIII = Σ-cong (λ hₒ → 𝟙-lneutral)
   IX   = Σ-cong (λ hₒ → Σ-cong (λ hₙ → γ hₒ hₙ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝)) (hₙ : Π (A ∘ neg))
       → Qₙ' (hₒ ⋆) hₙ ≃ Qₙ (hₒ ⋆) hₙ
     γ hₒ hₙ = ×-cong γ₀ (Π-cong fe fe γₙ)
      where
       f₀ = ⌜ f (neg 0) ⌝
       f₀⁻¹ = ⌜ (f (neg 0)) ⌝⁻¹
       e₀ : is-equiv f₀
       e₀ = ⌜⌝-is-equiv (f (neg 0))
       γ₀ : (hₒ ⋆ ＝ f₀ (hₙ 0))
          ≃ (hₙ 0 ＝ f₀⁻¹ (hₒ ⋆))
       γ₀ = (hₒ ⋆ ＝ f₀ (hₙ 0))             ≃⟨ I₀   ⟩
            (f₀ (hₙ 0) ＝ hₒ ⋆)             ≃⟨ II₀  ⟩
            (f₀ (hₙ 0) ＝ f₀ (f₀⁻¹ (hₒ ⋆))) ≃⟨ III₀ ⟩
            (hₙ 0 ＝ f₀⁻¹ (hₒ ⋆)) ■
        where
         I₀   = ＝-flip
         II₀  = ＝-cong-r (f₀ (hₙ 0)) (hₒ ⋆)
                 ((inverses-are-sections f₀ e₀ (hₒ ⋆)) ⁻¹)
         III₀ = embedding-criterion-converse f₀
                 (equivs-are-embeddings f₀ e₀)
                 (hₙ 0) (f₀⁻¹ (hₒ ⋆))
       fₙ : (n : ℕ) → A (neg (succ n)) → A (neg n)
       fₙ n = ⌜ f (neg (succ n)) ⌝
       eₙ : (n : ℕ) → is-equiv (fₙ n)
       eₙ n = ⌜⌝-is-equiv (f (neg (succ n)))
       fₙ⁻¹ : (n : ℕ) → A (neg n) → A (neg (succ n))
       fₙ⁻¹ n = ⌜ (f (neg (succ n))) ⌝⁻¹
       γₙ : (n : ℕ)
          → (hₙ n ＝ fₙ n (hₙ (succ n)))
          ≃ (hₙ (succ n) ＝ fₙ⁻¹ n (hₙ n))
       γₙ n = (hₙ n ＝ fₙ n (hₙ (succ n)))                 ≃⟨ Iₙ ⟩
              (fₙ n (hₙ (succ n)) ＝ hₙ n)                 ≃⟨ IIₙ ⟩
              (fₙ n (hₙ (succ n)) ＝ fₙ n (fₙ⁻¹ n (hₙ n))) ≃⟨ IIIₙ ⟩
              (hₙ (succ n) ＝ fₙ⁻¹ n (hₙ n))               ■
        where
         Iₙ   = ＝-flip
         IIₙ  = ＝-cong-r (fₙ n (hₙ (succ n))) (hₙ n)
                 ((inverses-are-sections (fₙ n) (eₙ n) (hₙ n)) ⁻¹)
         IIIₙ = embedding-criterion-converse (fₙ n)
                 (equivs-are-embeddings (fₙ n) (eₙ n))
                 (hₙ (succ n)) (fₙ⁻¹ n (hₙ n))
   X    = Σ-cong (λ hₒ → singleton-≃-𝟙 {𝓤} {𝓤₀} (γ hₒ))
    where
     γ : (hₒ : Π (A ∘ ⌜𝟎⌝))
       → is-singleton ((Σ hₙ ꞉ Π (A ∘ neg) , Qₙ  (hₒ ⋆) hₙ))
     γ hₒ = (ℕ-is-nno-dep fe (A ∘ neg) a₀ s)
      where
       a₀ : A (neg 0)
       a₀ = ⌜ (f (neg 0)) ⌝⁻¹ (hₒ ⋆)
       s : (n : ℕ) → A (neg n) → A (neg (succ n))
       s n = ⌜ (f (neg (succ n))) ⌝⁻¹
   XI   = 𝟙-rneutral
   XII  = ≃-sym (𝟙→ fe)

\end{code}

A nondependent instance and a consequence of the symmetric induction principle
are the following, added on 19 June 2026 by Tom de Jong.

The space of maps f : ℤ → X that equalize succ-ℤ and id_ℤ is equivalent to X,
and similarly for pred-ℤ instead of succ-ℤ.

\begin{code}

maps-equalizing-succ-ℤ-and-id-≃ : funext 𝓤₀ 𝓤 → (X : 𝓤 ̇ )
                                → (Σ f ꞉ (ℤ → X) , f ∘ succ-ℤ ＝ f) ≃ X
maps-equalizing-succ-ℤ-and-id-≃ fe X =
 (Σ f ꞉ (ℤ → X) , f ∘ succ-ℤ ＝ f) ≃⟨ Σ-cong (λ f → happly-≃ fe) ⟩
 (Σ f ꞉ (ℤ → X) , f ∘ succ-ℤ ∼ f)  ≃⟨ ind ⟩
 X                                 ■
  where
   ind = ℤ-symmetric-induction fe (λ _ → X) (λ _ → ≃-refl X)

maps-equalizing-pred-ℤ-and-id-≃ : funext 𝓤₀ 𝓤 → (X : 𝓤 ̇ )
                                → (Σ f ꞉ (ℤ → X) , f ∘ pred-ℤ ＝ f) ≃ X
maps-equalizing-pred-ℤ-and-id-≃ fe X =
  (Σ f ꞉ (ℤ → X) , f ∘ pred-ℤ ＝ f)                   ≃⟨ I   ⟩
  (Σ f ꞉ (ℤ → X) , f ∘ pred-ℤ ∘ succ-ℤ ＝ f ∘ succ-ℤ) ≃⟨ II  ⟩
  (Σ f ꞉ (ℤ → X) , f ＝ f ∘ succ-ℤ)                   ≃⟨ III ⟩
  (Σ f ꞉ (ℤ → X) , f ∘ succ-ℤ ＝ f)                   ≃⟨ IV  ⟩
  X                                                   ■
  where
   I   = Σ-cong
          (λ f → ap (_∘ succ-ℤ) ,
                 ap-is-equiv (_∘ succ-ℤ)
                             (dprecomp-is-equiv fe fe (λ _ → X)
                                                succ-ℤ
                                                succ-ℤ-is-equiv))
   II  = Σ-cong (λ f → ＝-cong-l _ _ (dfunext fe
                                       (λ k → ap f (succ-ℤ-is-section k))))
   III = Σ-cong (λ f → ＝-flip)
   IV  = maps-equalizing-succ-ℤ-and-id-≃ fe X

\end{code}