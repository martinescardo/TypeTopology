Martin Escardo, 12th September 2018.

We define the minimum function on ℕ∞ by corecursion as defined in the
module CoNaturals. The lack of definitional equalities make some proof
lengthy.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module CoNaturalsMinimum (fe : ∀ U V → funext U V) where

open import Two
open import GenericConvergentSequence
open import CoNaturals fe

\end{code}


\begin{code}

private
 p : ℕ∞ × ℕ∞ → 𝟙 {U₀} + ℕ∞ × ℕ∞
 p (u , v) = 𝟚-Cases (positivity u)
              (inl *)
              (𝟚-Cases (positivity v)
                (inl *)
                (inr (Pred u , Pred v)))

min : ℕ∞ → ℕ∞ → ℕ∞
min = curry (ℕ∞-corec p)

\end{code}

The defining equations of min are:

\begin{code}

min-eq₀ : ∀ v   → min Zero v ≡ Zero
min-eq₁ : ∀ u   → min (Succ u) Zero ≡ Zero
min-eq₂ : ∀ u v → min (Succ u) (Succ v) ≡ Succ (min u v)

min-eq₀ = λ v   → Coalg-morphism-Zero p (Zero , v) * refl
min-eq₁ = λ u   → Coalg-morphism-Zero p (Succ u , Zero) * refl
min-eq₂ = λ u v → Coalg-morphism-Succ p (Succ u , Succ v) (u , v) refl

\end{code}

The following equation is derived from the above equations by cases on
whether u is positive:

\begin{code}

min-eq₃ : ∀ u → min u Zero ≡ Zero
min-eq₃ u = h u (positivity u) refl
 where
  h : ∀ u n → positivity u ≡ n → min u Zero ≡ Zero
  h u ₀ r = b ∙ a
   where
    a : u ≡ Zero
    a = is-Zero-equal-Zero (fe U₀ U₀) r
    b : min u Zero ≡ u
    b = back-transport (λ - → min - Zero ≡ -) a (min-eq₀ Zero)
  h u ₁ r = back-transport (λ - → min - Zero ≡ Zero) a (min-eq₁ (Pred u))
   where
    a : u ≡ Succ (Pred u)
    a = not-Zero-is-Succ (fe U₀ U₀) (positive-is-not-Zero r)

\end{code}

The following invert the above equations:

\begin{code}

min₀ : ∀ u v → min u v ≡ Zero → (u ≡ Zero) + (v ≡ Zero)
min₀ u v r = h (Zero-or-Succ (fe U₀ U₀) u) (Zero-or-Succ (fe U₀ U₀) v)
 where
  h : (u ≡ Zero) + (u ≡ Succ(Pred u)) → (v ≡ Zero) + (v ≡ Succ(Pred v))
   → (u ≡ Zero) + (v ≡ Zero)
  h (inl u₀) d = inl u₀
  h (inr u₁) (inl v₀) = inr v₀
  h (inr u₁) (inr v₁) = 𝟘-elim (Zero-not-Succ (Zero    ≡⟨ r ⁻¹ ⟩
                                               min u v ≡⟨ s ⟩
                                               Succ _  ∎))
   where
    s : min u v ≡ Succ (min (Pred u) (Pred v))
    s = min u v                             ≡⟨ ap (λ - → min - v) u₁ ⟩
        min (Succ (Pred u)) v               ≡⟨ ap (min (Succ (Pred u))) v₁ ⟩
        min (Succ (Pred u)) (Succ (Pred v)) ≡⟨ min-eq₂ (Pred u) (Pred v) ⟩
        Succ (min (Pred u) (Pred v))        ∎


min₁ : ∀ u v w → min u v ≡ Succ w
    → (u ≡ Succ (Pred u))
    × (v ≡ Succ (Pred v))
    × (w ≡ min (Pred u) (Pred v))
min₁ u v w r = h (Zero-or-Succ (fe U₀ U₀) u) (Zero-or-Succ (fe U₀ U₀) v)
 where
  h : (u ≡ Zero) + (u ≡ Succ(Pred u)) → (v ≡ Zero) + (v ≡ Succ(Pred v)) → _
  h (inl u₀) d =
    𝟘-elim (Zero-not-Succ (Zero       ≡⟨ (min-eq₀ v)⁻¹ ⟩
                           min Zero v ≡⟨ ap (λ - → min - v) (u₀ ⁻¹) ⟩
                           min u v    ≡⟨ r ⟩
                           Succ w     ∎))
  h (inr u₁) (inl v₀) =
   𝟘-elim (Zero-not-Succ (Zero       ≡⟨ (min-eq₃ u)⁻¹ ⟩
                          min u Zero ≡⟨ ap (min u) (v₀ ⁻¹) ⟩
                          min u v    ≡⟨ r ⟩
                          Succ w     ∎))
  h (inr u₁) (inr v₁) = u₁ , v₁ ,
   Succ-lc (Succ w                              ≡⟨ r ⁻¹ ⟩
            min u v                             ≡⟨ ap (λ - → min - v) u₁  ⟩
            min (Succ (Pred u)) v               ≡⟨ ap (min (Succ (Pred u))) v₁ ⟩
            min (Succ (Pred u)) (Succ (Pred v)) ≡⟨ min-eq₂ (Pred u) (Pred v) ⟩
            Succ (min (Pred u) (Pred v))        ∎)

\end{code}

Now

\begin{code}

min-lemma₀ : ∀ u v → min u v ≡ Zero → min v u ≡ Zero
min-lemma₀  u v a = Cases (min₀ u v a)
                     (λ (b : u ≡ Zero) → ap (min v) b ∙ min-eq₃ v)
                     (λ (c : v ≡ Zero) → ap (λ - → min - u) c ∙ min-eq₀ u)

\end{code}
