---
layout: default
title : Introduction to Univalent Foundations of Mathematics with Agda
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

<!--
\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module Appendix where

open import Universes
open import MLTT-Agda
open import HoTT-UF-Agda
open import FunExt
open import Inhabitation
\end{code}
-->

[<sub>Table of contents ⇑</sub>](toc.html#contents)
## <a name="appendix"></a> Appendix

### <a name="moreexercises"></a> Additional exercises

Solutions are available [at the end](#mlttexercisessol).

*Exercise.* A sequence of elements of a type `X` is just a function `ℕ
 → X`. Use [Cantor's diagonal
 argument](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)
 to show in Agda that the type of sequences of natural numbers is
 uncountable. Prove a positive version and then derive a negative
 version from it:

\begin{code}
positive-cantors-diagonal : (e : ℕ → (ℕ → ℕ)) → Σ \(α : ℕ → ℕ) → (n : ℕ) → α ≢ e n

cantors-diagonal : ¬(Σ \(e : ℕ → (ℕ → ℕ)) → (α : ℕ → ℕ) → Σ \(n : ℕ) → α ≡ e n)
\end{code}

*Hint.* You may wish to prove that the function `succ` has no fixed points, first.

\begin{code}
𝟚-has-𝟚-automorphisms : dfunext 𝓤₀ 𝓤₀ → (𝟚 ≃ 𝟚) ≃ 𝟚
\end{code}

Universes are not cumulative in Agda, in the sense that from `X : 𝓤`
we would get `X : 𝓤⁺` or `X : 𝓤 ⊔ 𝓥`.  The usual approach is to
consider embeddings of universes into larger universes:

\begin{code}
data Up {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 up : X → Up 𝓥 X
\end{code}

This gives an embedding `Up 𝓥 : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇` and an embedding `up : X
→ Up 𝓥 X`. Prove the following:

\begin{code}
Up-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇ ) (A : Up 𝓥 X → 𝓦 ̇ )
             → ((x : X) → A (up x))
             → ((l : Up 𝓥 X) → A l)

Up-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } {B : 𝓦 ̇ }
             → (X → B) → Up 𝓥 X → B

down : {X : 𝓤 ̇ } → Up 𝓥 X → X

down-up : {X : 𝓤 ̇ } (x : X) → down {𝓤} {𝓥} (up x) ≡ x

up-down : {X : 𝓤 ̇ } (l : Up 𝓥 X) → up (down l) ≡ l

Up-≃ : (X : 𝓤 ̇ ) → Up 𝓥 X ≃ X

Up-left-≃ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → Up 𝓦 X ≃ Y

ap-Up-≃ : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → X ≃ Y → Up 𝓦 X ≃ Up 𝓣 Y
\end{code}

We now discuss alternative formulations of the principle of excluded middle.

\begin{code}
DNE : ∀ 𝓤 → 𝓤 ⁺ ̇
DNE 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → ¬¬ P → P

neg-is-subsingleton : dfunext 𝓤 𝓤₀ → (X : 𝓤 ̇ ) → is-subsingleton (¬ X)

emsanity : dfunext 𝓤 𝓤₀ → (P : 𝓤 ̇ ) → is-subsingleton P → is-subsingleton (P + ¬ P)

ne : (X : 𝓤 ̇ ) → ¬¬(X + ¬ X)

DNE-gives-EM : dfunext 𝓤 𝓤₀ → DNE 𝓤 → EM 𝓤

EM-gives-DNE : EM 𝓤 → DNE 𝓤
\end{code}

The following says that, under univalence, excluded middle holds iff
and only if every subsingleton is the negation of some type (maybe you
want to formulate and prove this - no solution given).

\begin{code}
SN : ∀ 𝓤 → 𝓤 ⁺ ̇
SN 𝓤 = (P : 𝓤 ̇ ) → is-subsingleton P → Σ \(X : 𝓤 ̇ ) → P ⇔ ¬ X

SN-gives-DNE : SN 𝓤 → DNE 𝓤

DNE-gives-SN : DNE 𝓤 → SN 𝓤
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)

### <a name="mlttexercisessol"></a> Solutions to additional exercises

Spoiler alert.

\begin{code}
succ-no-fixed-point : (n : ℕ) → succ n ≢ n
succ-no-fixed-point 0        = positive-not-zero 0
succ-no-fixed-point (succ n) = γ
 where
  IH : succ n ≢ n
  IH = succ-no-fixed-point n
  γ : succ (succ n) ≢ succ n
  γ p = IH (succ-lc p)

positive-cantors-diagonal e = (α , φ)
 where
  α : ℕ → ℕ
  α n = succ(e n n)
  φ : (n : ℕ) → α ≢ e n
  φ n p = succ-no-fixed-point (e n n) q
   where
    q = succ (e n n)  ≡⟨ refl (α n) ⟩
        α n           ≡⟨ ap (λ - → - n) p ⟩
        e n n         ∎

cantors-diagonal (e , γ) = c
 where
  α :  ℕ → ℕ
  α = pr₁ (positive-cantors-diagonal e)
  φ : (n : ℕ) → α ≢ e n
  φ = pr₂ (positive-cantors-diagonal e)
  b : Σ \(n : ℕ) → α ≡ e n
  b = γ α
  c : 𝟘
  c = φ (pr₁ b) (pr₂ b)

𝟚-has-𝟚-automorphisms fe =
 (f , invertibles-are-equivs f (g , η , ε))
 where
  f : (𝟚 ≃ 𝟚) → 𝟚
  f (h , e) = h ₀
  g : 𝟚 → (𝟚 ≃ 𝟚)
  g ₀ = id , id-is-equiv 𝟚
  g ₁ = swap₂ , swap₂-is-equiv
  η : (e : 𝟚 ≃ 𝟚) → g (f e) ≡ e
  η (h , e) = γ (h ₀) (h ₁) (refl (h ₀)) (refl (h ₁))
   where
    γ : (m n : 𝟚) → h ₀ ≡ m → h ₁ ≡ n → g (h ₀) ≡ (h , e)
    γ ₀ ₀ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₀   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))
    γ ₀ ₁ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₀) ₀     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₀) ₁     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)),
                       being-an-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₀ p q = to-Σ-≡ (fe (𝟚-induction (λ n → pr₁ (g (h ₀)) n ≡ h n)
                             (pr₁ (g (h ₀)) ₀ ≡⟨ ap (λ - → pr₁ (g -) ₀) p ⟩
                              pr₁ (g ₁) ₀     ≡⟨ refl ₁ ⟩
                              ₁               ≡⟨ p ⁻¹ ⟩
                              h ₀             ∎)
                             (pr₁ (g (h ₀)) ₁ ≡⟨ ap (λ - → pr₁ (g -) ₁) p ⟩
                              pr₁ (g ₁) ₁     ≡⟨ refl ₀ ⟩
                              ₀               ≡⟨ q ⁻¹ ⟩
                              h ₁             ∎)),
                       being-an-equiv-is-a-subsingleton fe fe _ _ e)
    γ ₁ ₁ p q = !𝟘 (g (h ₀) ≡ (h , e))
                   (₁-is-not-₀ (equivs-are-lc h e (h ₁ ≡⟨ q ⟩
                                                   ₁   ≡⟨ p ⁻¹ ⟩
                                                   h ₀ ∎)))

  ε : (n : 𝟚) → f (g n) ≡ n
  ε ₀ = refl ₀
  ε ₁ = refl ₁

Up-induction 𝓥 X A φ (up x) = φ x

Up-recursion 𝓥 {X} {B} = Up-induction 𝓥 X (λ _ → B)

down = Up-recursion _ id

down-up = refl

Up-≃ {𝓤} {𝓥} X = down {𝓤} {𝓥} , invertibles-are-equivs down (up , up-down , down-up {𝓤} {𝓥})

up-down {𝓤} {𝓥} {X} = Up-induction 𝓥 X
                        (λ l → up (down l) ≡ l)
                        (λ x → up (down {𝓤} {𝓥} (up x)) ≡⟨ ap up (down-up {𝓤} {𝓥}x) ⟩
                               up x                      ∎)

Up-left-≃ {𝓤} {𝓥} {𝓦} X Y e = Up 𝓦 X ≃⟨ Up-≃ X ⟩
                                X     ≃⟨ e ⟩
                                Y     ■

ap-Up-≃ {𝓤} {𝓥} {𝓦} {𝓣} X Y e = Up 𝓦 X  ≃⟨ Up-left-≃ X Y e ⟩
                                 Y       ≃⟨ ≃-sym (Up-≃ Y) ⟩
                                 Up 𝓣 Y  ■

neg-is-subsingleton fe X f g = fe (λ x → !𝟘 (f x ≡ g x) (f x))

emsanity fe P i (inl p) (inl q) = ap inl (i p q)
emsanity fe P i (inl p) (inr n) = !𝟘 (inl p ≡ inr n) (n p)
emsanity fe P i (inr m) (inl q) = !𝟘 (inr m ≡ inl q) (m q)
emsanity fe P i (inr m) (inr n) = ap inr (neg-is-subsingleton fe P m n)

ne X = λ (f : ¬(X + ¬ X)) → f (inr (λ (x : X) → f (inl x)))

DNE-gives-EM fe dne P i = dne (P + ¬ P) (emsanity fe P i) (ne P)

EM-gives-DNE em P i = γ (em P i)
 where
  γ : P + ¬ P → ¬¬ P → P
  γ (inl p) φ = p
  γ (inr n) φ = !𝟘 P (φ n)

SN-gives-DNE {𝓤} sn P i = h
 where
  X : 𝓤 ̇
  X = pr₁ (sn P i)
  f : P → ¬ X
  f = pr₁ (pr₂ (sn P i))
  g : ¬ X → P
  g = pr₂ (pr₂ (sn P i))
  f' : ¬¬ P → ¬(¬¬ X)
  f' = contrapositive (contrapositive f)
  h : ¬¬ P → P
  h = g ∘ tno ∘ f'
  h' : ¬¬ P → P
  h' φ = g (λ (x : X) → φ (λ (p : P) → f p x))

DNE-gives-SN dne P i = (¬ P) , dni , dne P i
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)
