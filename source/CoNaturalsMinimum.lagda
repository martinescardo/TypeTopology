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
open import UF-Base

\end{code}


\begin{code}

private
 κ : ℕ∞ × ℕ∞ → 𝟙 {U₀} + ℕ∞ × ℕ∞
 κ (u , v) = 𝟚-Cases (positivity u)
              (inl *)
              (𝟚-Cases (positivity v)
                (inl *)
                (inr (Pred u , Pred v)))

min : ℕ∞ × ℕ∞ → ℕ∞
min = ℕ∞-corec κ

\end{code}

The defining equations of min are:

\begin{code}

min-eq₀ : ∀ v   → min (Zero , v) ≡ Zero
min-eq₁ : ∀ u   → min (Succ u , Zero) ≡ Zero
min-eq₂ : ∀ u v → min (Succ u , Succ v) ≡ Succ (min (u , v))

min-eq₀ = λ v   → Coalg-morphism-Zero κ (Zero , v) * refl
min-eq₁ = λ u   → Coalg-morphism-Zero κ (Succ u , Zero) * refl
min-eq₂ = λ u v → Coalg-morphism-Succ κ (Succ u , Succ v) (u , v) refl

\end{code}

Using the equations min-eq₀ and min-eq₂, we have that the function

λ u → min (u , u) is an algebra homomorphism from P to P, where
P : ℕ∞ → 𝟙 + ℕ∞ is the final coalgebra constructed in the module
CoNaturals) and hence is equal to the identity:

\begin{code}

min-idempotent : ∀ u → min (u , u) ≡ u
min-idempotent u = ap (λ - → - u) h-is-corec
 where
  h : ℕ∞ → ℕ∞
  h u = min (u , u)
  h-homomorphism : is-homomorphism PRED h
  h-homomorphism = dfunext (fe U₀ U₀) λ u → φ u (Zero-or-Succ (fe U₀ U₀) u)
   where
    φ : (u : ℕ∞) → (u ≡ Zero) + (u ≡ Succ (Pred u)) → PRED (h u) ≡ 𝟙+ h (PRED u)
    φ u (inl r) =
      PRED (min (u , u))       ≡⟨ ap (λ - → PRED (min (- , -))) r ⟩
      PRED (min (Zero , Zero)) ≡⟨ ap PRED (min-eq₀ Zero) ⟩
      PRED Zero                ≡⟨ 𝟙+id-is-id (PRED Zero) ⁻¹ ⟩
      𝟙+ h (PRED Zero)         ≡⟨ ap (λ - → 𝟙+ h (PRED -)) (r ⁻¹)  ⟩
      𝟙+ h (PRED u)            ∎
    φ u (inr s) =
      PRED (min (u , u))                         ≡⟨ ap (λ - → PRED (min (- , -))) s ⟩
      PRED (min (Succ (Pred u) , Succ (Pred u))) ≡⟨ ap PRED (min-eq₂ (Pred u) (Pred u)) ⟩
      PRED (Succ (min (Pred u , Pred u)))        ≡⟨ refl ⟩
      inr (min (Pred u , Pred u))                ≡⟨ refl ⟩
      𝟙+ h (PRED (Succ (Pred u)))                ≡⟨ ap (λ - → 𝟙+ h (PRED -)) (s ⁻¹) ⟩
      𝟙+ h (PRED u)                              ∎
  h-is-corec : h ≡ id
  h-is-corec = homomorphism-uniqueness PRED h id h-homomorphism id-homomorphism


\end{code}

The following equation is derived from the above equations min-eq₀ and
min-eq₁ by cases on whether u is positive:

\begin{code}

eq₃-from-eq₀-and-eq₁ :
    (h : ℕ∞ × ℕ∞ → ℕ∞)
  → (∀ v   → h (Zero , v) ≡ Zero)
  → (∀ u   → h (Succ u , Zero) ≡ Zero)
  → (∀ u   → h (u , Zero) ≡ Zero)
eq₃-from-eq₀-and-eq₁ h eq₀ eq₁ u = γ u (positivity u) refl
 where
  γ : ∀ u n → positivity u ≡ n → h (u , Zero) ≡ Zero
  γ u ₀ r = b ∙ a
   where
    a : u ≡ Zero
    a = is-Zero-equal-Zero (fe U₀ U₀) r
    b : h (u , Zero) ≡ u
    b = back-transport (λ - → h (- , Zero) ≡ -) a (eq₀ Zero)
  γ u ₁ r = back-transport (λ - → h (- , Zero) ≡ Zero) a (eq₁ (Pred u))
   where
    a : u ≡ Succ (Pred u)
    a = not-Zero-is-Succ (fe U₀ U₀) (positive-is-not-Zero r)

min-eq₃ : ∀ u → min (u , Zero) ≡ Zero
min-eq₃ = eq₃-from-eq₀-and-eq₁ min min-eq₀ min-eq₁

\end{code}

Conversely, if a function satisfies the above equations, then it is a
coalgebra homomorphism and hence is equal to ℕ∞-corec p.

\begin{code}

equations-characterize-homomorphisms :
    (h : ℕ∞ × ℕ∞ → ℕ∞)
  → (∀ v   → h (Zero , v) ≡ Zero)
  → (∀ u   → h (Succ u , Zero) ≡ Zero)
  → (∀ u v → h (Succ u , Succ v) ≡ Succ (h (u , v)))
  → is-homomorphism κ h
equations-characterize-homomorphisms h eq₀ eq₁ eq₂ = dfunext (fe U₀ U₀) γ
  where
   γ : (w : ℕ∞ × ℕ∞) → PRED (h w) ≡ 𝟙+ h (κ w)
   γ (u , v) = φ u (Zero-or-Succ (fe U₀ U₀) u)
    where
     φ : (u : ℕ∞) → (u ≡ Zero) + (u ≡ Succ(Pred u)) → PRED (h (u , v)) ≡ 𝟙+ h (κ (u , v))
     φ u (inl q) =
       PRED (h (u , v))       ≡⟨ ap (λ - → PRED (h (- , v))) q ⟩
       PRED (h (Zero , v))    ≡⟨ ap PRED (eq₀ v) ⟩
       PRED Zero              ≡⟨ refl ⟩
       inl *                  ≡⟨ refl ⟩
       𝟙+ h (inl *)           ≡⟨ refl ⟩
       𝟙+ h (κ (Zero , v))    ≡⟨ ap (λ - → 𝟙+ h (κ (- , v))) (q ⁻¹) ⟩
       𝟙+ h (κ (u , v))       ∎
     φ u (inr r) = ψ v (Zero-or-Succ (fe U₀ U₀) v)
      where
       ψ : (v : ℕ∞) → (v ≡ Zero) + (v ≡ Succ(Pred v)) → PRED (h (u , v)) ≡ 𝟙+ h (κ (u , v))
       ψ v (inl z) =
         PRED (h (u , v))                   ≡⟨ ap (λ - → PRED (h -)) (×-≡ r z)  ⟩
         PRED (h (Succ (Pred u) , Zero))    ≡⟨ ap PRED (eq₁ (Pred u)) ⟩
         PRED Zero                          ≡⟨ refl ⟩
         𝟙+ h (inl *)                       ≡⟨ refl ⟩
         𝟙+ h (κ (Succ (Pred u) , Zero))    ≡⟨ ap (λ - → 𝟙+ h (κ -)) ((×-≡ r z)⁻¹) ⟩
         𝟙+ h (κ (u , v))                   ∎
       ψ v (inr t) =
         PRED (h (u , v))                         ≡⟨ ap (λ - → PRED (h -)) (×-≡ r t)  ⟩
         PRED (h (Succ (Pred u) , Succ (Pred v))) ≡⟨ ap PRED (eq₂ (Pred u) (Pred v)) ⟩
         PRED (Succ (h (Pred u , Pred v)))        ≡⟨ refl ⟩
         inr (h (Pred u , Pred v))                ≡⟨ refl ⟩
         𝟙+ h (inr (Pred u , Pred v))             ≡⟨ refl ⟩
         𝟙+ h (κ (Succ (Pred u) , Succ (Pred v))) ≡⟨ ap (λ - → 𝟙+ h (κ -)) (×-≡ r t ⁻¹) ⟩
         𝟙+ h (κ (u , v))                         ∎

\end{code}

To prove that min is commutative, we show that the following function
h is also a coalgebra homomorphism and hence equal to ℕ∞-corec p:

\begin{code}

min-commutative : ∀ u v → min (u , v) ≡ min (v , u)
min-commutative u v = h (v , u)          ≡⟨ ap (λ - → - (v , u)) h-is-corec ⟩
                      ℕ∞-corec κ (v , u) ∎
 where
  h : ℕ∞ × ℕ∞ → ℕ∞
  h (u , v) = min (v , u)
  h-homomorphism : is-homomorphism κ h
  h-homomorphism = equations-characterize-homomorphisms h h-eq₀ h-eq₁ h-eq₂
   where
    h-eq₀ : (v : ℕ∞) → min (v , Zero) ≡ Zero
    h-eq₀ v = min-eq₃ v
    h-eq₁ : (u : ℕ∞) → min (Zero , Succ u) ≡ Zero
    h-eq₁ u = min-eq₀ (Succ u)
    h-eq₂ : (u v : ℕ∞) → min (Succ v , Succ u) ≡ Succ (min (v , u))
    h-eq₂ u v = min-eq₂ v u
  h-is-corec : h ≡ ℕ∞-corec κ
  h-is-corec = homomorphism-uniqueness κ h (ℕ∞-corec κ) h-homomorphism (ℕ∞-corec-homomorphism κ)

\end{code}

The following two facts invert the equations that characterize min:

\begin{code}

min₀ : ∀ u v → min (u , v) ≡ Zero → (u ≡ Zero) + (v ≡ Zero)
min₁ : ∀ u v w → min (u , v) ≡ Succ w → (u ≡ Succ (Pred u))
                                      × (v ≡ Succ (Pred v))
                                      × (w ≡ min (Pred u , Pred v))

\end{code}

And here are their constructions:

\begin{code}

min₀ u v r = h (Zero-or-Succ (fe U₀ U₀) u) (Zero-or-Succ (fe U₀ U₀) v)
 where
  h : (u ≡ Zero) + (u ≡ Succ(Pred u)) → (v ≡ Zero) + (v ≡ Succ(Pred v))
    → (u ≡ Zero) + (v ≡ Zero)
  h (inl u₀) d = inl u₀
  h (inr u₁) (inl v₀) = inr v₀
  h (inr u₁) (inr v₁) = 𝟘-elim (Zero-not-Succ (Zero        ≡⟨ r ⁻¹ ⟩
                                               min (u , v) ≡⟨ s ⟩
                                               Succ _      ∎))
   where
    s : min (u , v) ≡ Succ (min (Pred u , Pred v))
    s = min (u , v)                          ≡⟨ ap (λ - → min (- , v)) u₁ ⟩
        min (Succ (Pred u) , v)              ≡⟨ ap (λ - → min (Succ (Pred u) , -)) v₁ ⟩
        min (Succ (Pred u) ,  Succ (Pred v)) ≡⟨ min-eq₂ (Pred u) (Pred v) ⟩
        Succ (min (Pred u , Pred v))         ∎


min₁ u v w r = h (Zero-or-Succ (fe U₀ U₀) u) (Zero-or-Succ (fe U₀ U₀) v)
 where
  h : (u ≡ Zero) + (u ≡ Succ(Pred u)) → (v ≡ Zero) + (v ≡ Succ(Pred v)) → _
  h (inl u₀) d =
    𝟘-elim (Zero-not-Succ (Zero           ≡⟨ (min-eq₀ v)⁻¹ ⟩
                           min (Zero , v) ≡⟨ ap (λ - → min (- , v)) (u₀ ⁻¹) ⟩
                           min (u , v)    ≡⟨ r ⟩
                           Succ w         ∎))
  h (inr u₁) (inl v₀) =
   𝟘-elim (Zero-not-Succ (Zero           ≡⟨ (min-eq₃ u)⁻¹ ⟩
                          min (u , Zero) ≡⟨ ap (λ - → min (u , -)) (v₀ ⁻¹) ⟩
                          min (u , v)    ≡⟨ r ⟩
                          Succ w         ∎))
  h (inr u₁) (inr v₁) = u₁ , v₁ ,
   Succ-lc (Succ w                              ≡⟨ r ⁻¹ ⟩
            min (u , v)                         ≡⟨ ap (λ - → min (- , v)) u₁  ⟩
            min (Succ (Pred u) , v)             ≡⟨ ap (λ - → min (Succ (Pred u) , -)) v₁ ⟩
            min (Succ (Pred u) , Succ (Pred v)) ≡⟨ min-eq₂ (Pred u) (Pred v) ⟩
            Succ (min (Pred u , Pred v))        ∎)

\end{code}
