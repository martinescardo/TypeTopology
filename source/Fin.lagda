Martin Escardo, 2014, 21 March 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Fin  where

Fin : ℕ → 𝓤₀ ̇
Fin zero     = 𝟘
Fin (succ n) = Fin n + 𝟙

\end{code}

We have zero and successor for finite sets, with the following types:

\begin{code}

fzero : {n : ℕ} → Fin(succ n)
fzero = inr *

fsucc : {n : ℕ} → Fin n → Fin(succ n)
fsucc = inl

\end{code}

The left cancellability of Fin uses the non-trivial construction
+𝟙-cancellable defined in the module PlusOneLC.lagda.

\begin{code}

open import UF-FunExt

module _ (fe : FunExt) where

 open import PlusOneLC
 open import UF-Equiv

 Fin-lc : (m n : ℕ) → Fin m ≃ Fin n → m ≡ n
 Fin-lc zero zero p = refl
 Fin-lc (succ m) zero p = 𝟘-elim (⌜ p ⌝ fzero)
 Fin-lc zero (succ n) p = 𝟘-elim (⌜ ≃-sym p ⌝ fzero)
 Fin-lc (succ m) (succ n) p = ap succ r
  where
   IH : Fin m ≃ Fin n → m ≡ n
   IH = Fin-lc m n
   remark : Fin m + 𝟙 ≃ Fin n + 𝟙
   remark = p
   q : Fin m ≃ Fin n
   q = +𝟙-cancellable fe p
   r : m ≡ n
   r = IH q

open import DiscreteAndSeparated

Fin-is-discrete : (n : ℕ) → is-discrete (Fin n)
Fin-is-discrete zero     = 𝟘-is-discrete
Fin-is-discrete (succ n) = +discrete (Fin-is-discrete n) 𝟙-is-discrete

\end{code}

Added November 2019.

\begin{code}

open import CompactTypes

Fin-Compact : (n : ℕ) → Σ-Compact (Fin n) 𝓤₀
Fin-Compact zero A d = γ
 where
  w : ¬ Σ \(x : Fin zero) → A x
  w (x , a) = x
  γ : Σ A + ¬ Σ A
  γ = inr w
Fin-Compact (succ n) A d = f (d fzero)
 where
  f : A fzero + ¬ A fzero → Σ A + ¬ Σ A
  f (inl a) = inl (fzero , a)
  f (inr u) = γ
   where
    B : Fin n → 𝓤₀ ̇
    B x = A (fsucc x)
    e : detachable B
    e x = d (fsucc x)
    IH : decidable (Σ B)
    IH = Fin-Compact n B e
    g : Σ B + ¬ Σ B → Σ A + ¬ Σ A
    g (inl (x , b)) = inl (fsucc x , b)
    g (inr v) = inr w
     where
      w : ¬ Σ A
      w (inl x , a) = v (x , a)
      w (inr * , a) = u a
    γ : Σ A + ¬ Σ A
    γ = g IH

\end{code}

\begin{code}

module _ (fe : FunExt) where

 open import Plus-Properties
 open import Swap fe
 open import UF-Base
 open import UF-Equiv
 open import UF-LeftCancellable

\end{code}

Recall that X ↣ Y is the type of left cancellable maps from X to Y.

\begin{code}

 +𝟙-cancel-lemma : {X Y : 𝓤 ̇}
                 → (𝒇 : X + 𝟙 ↣ Y + 𝟙)
                 → ⌈ 𝒇 ⌉ (inr *) ≡ inr *
                 → X ↣ Y
 +𝟙-cancel-lemma {𝓤} {X} {Y} (f , l) p = g , m
  where
   g : X → Y
   g x = pr₁ (inl-preservation {𝓤} {𝓤} {𝓤} {𝓤} f p l x)

   a : (x : X) → f (inl x) ≡ inl (g x)
   a x = pr₂ (inl-preservation f p l x)

   m : left-cancellable g
   m {x} {x'} p = q
    where
     r = f (inl x)  ≡⟨ a x      ⟩
         inl (g x)  ≡⟨ ap inl p ⟩
         inl (g x') ≡⟨ (a x')⁻¹ ⟩
         f (inl x') ∎
     q : x ≡ x'
     q = inl-lc (l r)

 +𝟙-cancel : {X Y : 𝓤 ̇}
           → is-discrete Y
           → X + 𝟙 ↣ Y + 𝟙
           → X ↣ Y
 +𝟙-cancel {𝓤} {X} {Y} i (f , e) = a
  where
   h : Y + 𝟙 → Y + 𝟙
   h = swap (f (inr *)) (inr *) (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated
   d : left-cancellable h
   d = equivs-are-lc h (swap-is-equiv (f (inr *)) (inr *) (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated)
   f' : X + 𝟙 → Y + 𝟙
   f' = h ∘ f
   e' : left-cancellable f'
   e' = left-cancellable-closed-under-∘ f h e d
   p : f' (inr *) ≡ inr *
   p = swap-equation₀ (f (inr *)) (inr *) (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated
   a : X ↣ Y
   a = +𝟙-cancel-lemma (f' , e') p


 open import NaturalsOrder
 open import UF-EquivalenceExamples

 finle : (m n : ℕ) → (Fin m ↣ Fin n) → m ≤ n
 finle zero n e              = zero-minimal n
 finle (succ m) zero (f , i) = 𝟘-elim (f fzero)
 finle (succ m) (succ n) e   = finle m n (+𝟙-cancel (Fin-is-discrete n) e)

 lefin : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
 lefin zero     n        l = unique-from-𝟘 , (λ {x} {x'} p → 𝟘-elim x)
 lefin (succ m) zero     l = 𝟘-elim l
 lefin (succ m) (succ n) l = g , j
  where
   IH : Fin m ↣ Fin n
   IH = lefin m n l
   f : Fin m → Fin n
   f = pr₁ IH
   i : left-cancellable f
   i = pr₂ IH
   g : Fin (succ m) → Fin (succ n)
   g = +functor f unique-to-𝟙
   j : left-cancellable g
   j {inl x} {inl x'} p = ap inl (i (inl-lc p))
   j {inl x} {inr *}  p = 𝟘-elim (+disjoint  p)
   j {inr *} {inl y}  p = 𝟘-elim (+disjoint' p)
   j {inr *} {inr *}  p = refl

\end{code}
