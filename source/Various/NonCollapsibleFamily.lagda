Martin Escardo, 1st April 2013

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Various.NonCollapsibleFamily where

open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Hedberg
open import UF.KrausLemma
open import UF.Subsingletons

decidable-equality-criterion : (X : 𝓤 ̇ )
                               (a : 𝟚 → X) → ((x : X) → collapsible (Σ i ꞉ 𝟚 , a i ＝ x))
                             → is-decidable(a ₀ ＝ a ₁)
decidable-equality-criterion {𝓤} X a c = equal-or-different
 where
  κ : (x : X) → (Σ i ꞉ 𝟚 , a i ＝ x) → Σ i ꞉ 𝟚 , a i ＝ x
  κ x = pr₁(c x)

  κ-constant : (x : X) → wconstant(κ x)
  κ-constant x = pr₂(c x)

  prop-fix : (x : X) → is-prop (fix(κ x))
  prop-fix x = fix-is-prop (κ x) (κ-constant x)

  choice : (x : X) → fix(κ x) → Σ i ꞉ 𝟚 , a i ＝ x
  choice x = pr₁

  η : (x : X) → (Σ i ꞉ 𝟚 , a i ＝ x) → fix(κ x)
  η x σ = κ x σ , κ-constant x σ (κ x σ)

  E : 𝓤 ̇
  E = Σ x ꞉ X , fix(κ x)

  r : 𝟚 → E
  r i = a i , η (a i) (i , refl)

  r-splits : (e : E) → Σ i ꞉ 𝟚 , r i ＝ e
  r-splits (x , p) = pr₁ p' , to-Σ-＝ (pr₂ p' , prop-fix x _ p)
   where
    p' : Σ i ꞉ 𝟚 , a i ＝ x
    p' = choice x p

  s : E → 𝟚
  s e = pr₁(r-splits e)

  r-retract : (e : E) → r(s e) ＝ e
  r-retract e = pr₂(r-splits e)

  s-injective : (e e' : E) → s e ＝ s e' → e ＝ e'
  s-injective e e' p = (r-retract e)⁻¹ ∙ ap r p ∙ r-retract e'

  a-r : (i j : 𝟚) → a i ＝ a j → r i ＝ r j
  a-r i j p = to-Σ-＝ (p , prop-fix (a j) _ (η (a j) (j , refl)))

  r-a : (i j : 𝟚) → r i ＝ r j → a i ＝ a j
  r-a i j = ap pr₁

  a-s : (i j : 𝟚) → a i ＝ a j → s(r i) ＝ s(r j)
  a-s i j p = ap s (a-r i j p)

  s-a : (i j : 𝟚) → s(r i) ＝ s(r j) → a i ＝ a j
  s-a i j p = r-a i j (s-injective (r i) (r j) p)

  equal-or-different : (a ₀ ＝ a ₁) + (a ₀ ＝ a ₁ → 𝟘)
  equal-or-different = claim(𝟚-is-discrete (s(r ₀)) (s(r ₁)))
   where
    claim : (s(r ₀) ＝ s(r ₁)) + (s(r ₀) ＝ s(r ₁) → 𝟘) → (a ₀ ＝ a ₁) + (a ₀ ＝ a ₁ → 𝟘)
    claim (inl p) = inl (s-a ₀ ₁ p)
    claim (inr u) = inr (λ p → u (a-s ₀ ₁ p))

\end{code}
