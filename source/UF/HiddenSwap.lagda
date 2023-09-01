Martin Escardo, 1st September 2023

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.FunExt
open import UF.PropTrunc

module UF.HiddenSwap
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

hidden-swap : {X : 𝓤 ̇ }
            → ∥ X ≃ 𝟚 ∥
            → Σ 𝕗 ꞉ X ≃ X , ⌜ 𝕗 ⌝ ≠ id
hidden-swap {𝓤} {X} s = VIII
 where
  I : (x : X) → X ≃ 𝟚 → Σ y ꞉ X , x ≠ y
  I x 𝕘 = ⌜ 𝕘 ⌝⁻¹ (complement (⌜ 𝕘 ⌝ x)) , I₀
   where
    I₀ : x ≠ ⌜ 𝕘 ⌝⁻¹ (complement (⌜ 𝕘 ⌝ x))
    I₀ p = complement-no-fp (⌜ 𝕘 ⌝ x) I₁
     where
      I₁ = ⌜ 𝕘 ⌝ x                                 ＝⟨ ap ⌜ 𝕘 ⌝ p ⟩
            ⌜ 𝕘 ⌝ (⌜ 𝕘 ⌝⁻¹ (complement (⌜ 𝕘 ⌝ x))) ＝⟨ I₂ ⟩
            (complement (⌜ 𝕘 ⌝ x))                 ∎
            where
             I₂ = inverses-are-sections ⌜ 𝕘 ⌝ ⌜ 𝕘 ⌝-is-equiv _

  X-is-set : is-set X
  X-is-set = ∥∥-rec (being-set-is-prop fe) (λ 𝕘 → equiv-to-set 𝕘 𝟚-is-set) s

  II : (x y y' : X) → x ≠ y → x ≠ y' → y ＝ y'
  II x y y' ν ν' = ∥∥-rec X-is-set (λ 𝕘 → d' 𝕘 x y y' ν ν') s
   where
    d' : X ≃ 𝟚 → (x y y' : X) → x ≠ y → x ≠ y' → y ＝ y'
    d' 𝕘 x y y' ν ν' = equivs-are-lc ⌜ 𝕘 ⌝ ⌜ 𝕘 ⌝-is-equiv d₀
     where
      d₀ : ⌜ 𝕘 ⌝ y ＝ ⌜ 𝕘 ⌝ y'
      d₀ = 𝟚-things-distinct-from-a-third-are-equal (⌜ 𝕘 ⌝ y) (⌜ 𝕘 ⌝ y') (⌜ 𝕘 ⌝ x)
             (λ (p : ⌜ 𝕘 ⌝ y ＝ ⌜ 𝕘 ⌝ x)
                   → ν (equivs-are-lc ⌜ 𝕘 ⌝ ⌜ 𝕘 ⌝-is-equiv (p ⁻¹)))
             (λ (p : ⌜ 𝕘 ⌝ y' ＝ ⌜ 𝕘 ⌝ x)
                   → ν' (equivs-are-lc ⌜ 𝕘 ⌝ ⌜ 𝕘 ⌝-is-equiv (p ⁻¹)))

  III : (x : X) → is-prop (Σ y ꞉ X , x ≠ y)
  III x (y , ν) (y' , ν') =
   to-subtype-＝ (λ x → negations-are-props fe) (II x y y' ν ν')

  IV : (x : X) → Σ y ꞉ X , x ≠ y
  IV x = ∥∥-rec (III x) (I x) s

  f : X → X
  f x = pr₁ (IV x)

  V : f ∘ f ∼ id
  V x = V₂
   where
    V₀ : x ≠ f x
    V₀ = pr₂ (IV x)

    V₁ : f x ≠ f (f x)
    V₁ = pr₂ (IV (f x))

    V₂ : f (f x) ＝ x
    V₂ = II (f x) (f (f x)) x V₁ (≠-sym V₀)

  VI : X ≃ X
  VI = qinveq f (f , V , V)

  VII : f ≠ id
  VII p = VII₁
   where
    VII₀ : ∃ x ꞉ X , (x ≠ f x)
    VII₀ = ∥∥-rec ∃-is-prop (λ 𝕘 → ∣ ⌜ 𝕘 ⌝⁻¹ ₀ , pr₂ (IV (⌜ 𝕘 ⌝⁻¹ ₀)) ∣) s

    VII₁ : 𝟘
    VII₁ = ∥∥-rec 𝟘-is-prop (λ (x , ν) → ν (happly (p ⁻¹) x)) VII₀

  VIII :  Σ 𝕗 ꞉ X ≃ X , ⌜ 𝕗 ⌝ ≠ id
  VIII = VI , VII

\end{code}
