Martin Escardo, March 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import UF-FunExt

module P2 (fe : FunExt) where

open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

open import DiscreteAndSeparated
open import Two
open import Two-Properties

κ : (P : 𝓤 ̇ ) → 𝟚 → (P → 𝟚)
κ P n = λ _ → n

is-pseudo-inhabited : 𝓤 ̇ → 𝓤 ̇
is-pseudo-inhabited P = is-equiv (κ P)

retraction-of-κ-is-section : {P : 𝓤 ̇ }
                           → is-prop P
                           → (r : (P → 𝟚) → 𝟚)
                           → r ∘ κ P ∼ id
                           → κ P ∘ r ∼ id
retraction-of-κ-is-section {𝓤} {P} i r h f = IV
 where
  I : (p : P) → r f ≡ f p
  I p = r f           ≡⟨ ap r III ⟩
        r (κ P (f p)) ≡⟨ h (f p) ⟩
        f p           ∎
   where
    II : f ∼ κ P (f p)
    II q = f q         ≡⟨ ap f (i q p) ⟩
           f p         ≡⟨ refl ⟩
           κ P (f p) q ∎

    III : f ≡ κ P (f p)
    III = dfunext (fe 𝓤 𝓤₀) II

  IV : κ P (r f) ≡ f
  IV = dfunext (fe 𝓤 𝓤₀) I

pseudo-inhabitedness-criterion : {P : 𝓤 ̇ }
                               → is-prop P
                               → is-section (κ P)
                               → is-pseudo-inhabited P
pseudo-inhabitedness-criterion {𝓤} {P} i (r , rκ) =
 qinvs-are-equivs (κ P) (r , rκ , retraction-of-κ-is-section i r rκ)

pseudo-inhabitedness-criterion-necessity : {P : 𝓤 ̇ }
                                         → is-pseudo-inhabited P
                                         → is-section (κ P)
pseudo-inhabitedness-criterion-necessity {𝓤} {P} = equivs-are-sections (κ P)

inhabited-gives-pseudo-inhabited : {P : 𝓤 ̇ }
                                 → is-prop P
                                 → P
                                 → is-pseudo-inhabited P
inhabited-gives-pseudo-inhabited {𝓤} {P} i p = pseudo-inhabitedness-criterion i (γ , γκ)
 where
  γ : (P → 𝟚) → 𝟚
  γ f = f p

  γκ : γ ∘ κ P ∼ id
  γκ n = refl

pseudo-inhabited-gives-irrefutable : {P : 𝓤 ̇ } → is-pseudo-inhabited P → ¬¬ P
pseudo-inhabited-gives-irrefutable {𝓤} {P} e n = zero-is-not-one II
 where
  I : inverse (κ P) e (κ P ₀) ≡ inverse (κ P) e (κ P ₁)
  I = ap (inverse (κ P) e) (κ P ₀ ≡⟨ dfunext (fe 𝓤 𝓤₀) (λ p → 𝟘-elim (n p)) ⟩
                            κ P ₁ ∎)

  II = ₀                       ≡⟨ (inverses-are-retractions (κ P) e ₀)⁻¹ ⟩
       inverse (κ P) e (κ P ₀) ≡⟨ I ⟩
       inverse (κ P) e (κ P ₁) ≡⟨ inverses-are-retractions (κ P) e ₁ ⟩
       ₁                       ∎

P→𝟚-discreteness-criterion : {P : 𝓤 ̇ } → ¬ P + is-pseudo-inhabited P → is-discrete (P → 𝟚)
P→𝟚-discreteness-criterion (inl n) f g = inl (dfunext (fe _ 𝓤₀) (λ p → 𝟘-elim (n p)))
P→𝟚-discreteness-criterion (inr s) f g = retract-is-discrete
                                          (≃-gives-▷ (κ _ , s))
                                          𝟚-is-discrete
                                          f g

P→𝟚-discreteness-criterion-necessity : {P : 𝓤 ̇ }
                                     → is-prop P
                                     → is-discrete (P → 𝟚)
                                     → ¬ P + is-pseudo-inhabited P
P→𝟚-discreteness-criterion-necessity {𝓤} {P} i δ = ϕ (δ (κ P ₀) (κ P ₁))
 where
  ϕ : decidable (κ P ₀ ≡ κ P ₁) → ¬ P + is-pseudo-inhabited P
  ϕ (inl e) = inl (fact e)
   where
    fact : κ P ₀ ≡ κ P ₁ → ¬ P
    fact e p = zero-is-not-one (ap (λ f → f p) e)
  ϕ (inr n) = inr (pseudo-inhabitedness-criterion i (γ , γκ))
   where
    h : (f : P → 𝟚) → decidable (f ≡ κ P ₀) → 𝟚
    h f (inl _) = ₀
    h f (inr _) = ₁

    γ : (P → 𝟚) → 𝟚
    γ f = h f (δ f (κ P ₀))

    δ₀ : (d : decidable (κ P ₀ ≡ κ P ₀)) → h (κ P ₀) d ≡ ₀
    δ₀ (inl _) = refl
    δ₀ (inr d) = 𝟘-elim (d refl)

    δ₁ : (d : decidable (κ P ₁ ≡ κ P ₀)) → h (κ P ₁) d ≡ ₁
    δ₁ (inl e) = 𝟘-elim (n (e ⁻¹))
    δ₁ (inr _) = refl

    γκ : γ ∘ κ P ∼ id
    γκ ₀ = δ₀ (δ (κ P ₀) (κ P ₀))
    γκ ₁ = δ₁ (δ (κ P ₁) (κ P ₀))

\end{code}
