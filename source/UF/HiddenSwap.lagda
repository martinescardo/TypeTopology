Martin Escardo, 1st September 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

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
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt

\end{code}

What is noteworthy about the following is that, without knowing a
specific equivalence of X with 𝟚, so that, in particular, we cannot
get any particular point of X, we can still swap the two unknown
points of X, so to speak.

\begin{code}

hidden-swap : {X : 𝓤 ̇ }
            → ∥ X ≃ 𝟚 ∥
            → Σ f ꞉ (X → X) , (f ≠ id) × (f ∘ f ∼ id)
hidden-swap {𝓤} {X} s = VII
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
    d' 𝕘 x y y' ν ν' = equivs-are-lc ⌜ 𝕘 ⌝ ⌜ 𝕘 ⌝-is-equiv II₀
     where
      II₀ : ⌜ 𝕘 ⌝ y ＝ ⌜ 𝕘 ⌝ y'
      II₀ = 𝟚-things-distinct-from-a-third-are-equal (⌜ 𝕘 ⌝ y) (⌜ 𝕘 ⌝ y') (⌜ 𝕘 ⌝ x)
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

  VI : f ≠ id
  VI p = VI₁
   where
    VI₀ : ∃ x ꞉ X , (x ≠ f x)
    VI₀ = ∥∥-rec ∃-is-prop (λ 𝕘 → ∣ ⌜ 𝕘 ⌝⁻¹ ₀ , pr₂ (IV (⌜ 𝕘 ⌝⁻¹ ₀)) ∣) s

    VI₁ : 𝟘
    VI₁ = ∥∥-rec 𝟘-is-prop (λ (x , ν) → ν (happly (p ⁻¹) x)) VI₀

  VII :  Σ f ꞉ (X → X) , (f ≠ id) × (f ∘ f ∼ id)
  VII = f , VI , V

\end{code}

Because involutions are equivalences, we get the following.

\begin{code}

hidden-swap-corollary : {X : 𝓤 ̇ }
                      → ∥ X ≃ 𝟚 ∥
                      → Σ 𝕗 ꞉ X ≃ X , ⌜ 𝕗 ⌝ ≠ id
hidden-swap-corollary {𝓤} {X} s = I (hidden-swap s)
 where
  I : (Σ f ꞉ (X → X) , (f ≠ id) × (f ∘ f ∼ id))
    → Σ 𝕗 ꞉ X ≃ X , (⌜ 𝕗 ⌝ ≠ id)
  I (f , ν , i) = qinveq f (f , i , i) , ν

\end{code}

The above is a solution to exercises proposed on
https://mathstodon.xyz/@MartinEscardo/110991799307299727

An independent solution by github user Seiryn21 is at
https://gist.github.com/Seiryn21/4173b1ee0b88be7b5a6054ac3222c8e1
