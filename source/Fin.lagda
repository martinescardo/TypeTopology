Martin Escardo, 2014, 21 March 2018

Fin n is a set with n elements. We investigate some of its basic properties.

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

fzero : {n : ℕ} → Fin (succ n)
fzero = inr *

fsucc : {n : ℕ} → Fin n → Fin (succ n)
fsucc = inl

Fin-induction : (P : (n : ℕ) → Fin n → 𝓤 ̇ )
              → ((n : ℕ) → P (succ n) fzero)
              → ((n : ℕ) (i : Fin n) → P n i → P (succ n) (fsucc i))
              →  (n : ℕ) (i : Fin n) → P n i
Fin-induction P β σ zero     i       = 𝟘-elim i
Fin-induction P β σ (succ n) (inr *) = β n
Fin-induction P β σ (succ n) (inl i) = σ n i (Fin-induction P β σ n i)

\end{code}

The left cancellability of Fin uses the non-trivial construction
+𝟙-cancellable defined in the module PlusOneLC.lagda.

\begin{code}

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
  q = +𝟙-cancellable p
  r : m ≡ n
  r = IH q

open import DiscreteAndSeparated

Fin-is-discrete : (n : ℕ) → is-discrete (Fin n)
Fin-is-discrete zero     = 𝟘-is-discrete
Fin-is-discrete (succ n) = +discrete (Fin-is-discrete n) 𝟙-is-discrete

open import UF-Subsingletons
open import UF-Miscelanea

Fin-is-set : (n : ℕ) → is-set (Fin n)
Fin-is-set n = discrete-types-are-sets (Fin-is-discrete n)

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
      w (inr * , a) = u a
      w (inl x , a) = v (x , a)
    γ : Σ A + ¬ Σ A
    γ = g IH

\end{code}

Recall that X ↣ Y is the type of left cancellable maps from X to Y.

\begin{code}

open import Plus-Properties
open import Swap
open import UF-LeftCancellable

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
  d = equivs-are-lc h (swap-is-equiv (f (inr *)) (inr *)
                        (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated)

  f' : X + 𝟙 → Y + 𝟙
  f' = h ∘ f

  e' : left-cancellable f'
  e' = left-cancellable-closed-under-∘ f h e d

  p : f' (inr *) ≡ inr *
  p = swap-equation₀ (f (inr *)) (inr *)
       (+discrete i 𝟙-is-discrete (f (inr *))) new-point-is-isolated

  a : X ↣ Y
  a = +𝟙-cancel-lemma (f' , e') p

open import NaturalsOrder
open import UF-EquivalenceExamples

↣-gives-≤ : (m n : ℕ) → (Fin m ↣ Fin n) → m ≤ n
↣-gives-≤ zero n e              = zero-minimal n
↣-gives-≤ (succ m) zero (f , i) = 𝟘-elim (f fzero)
↣-gives-≤ (succ m) (succ n) e   = ↣-gives-≤ m n (+𝟙-cancel (Fin-is-discrete n) e)


canonical-Fin-inclusion : (m n : ℕ) → m ≤ n → (Fin m → Fin n)
canonical-Fin-inclusion zero n            l = unique-from-𝟘
canonical-Fin-inclusion (succ m) zero     l = 𝟘-elim l
canonical-Fin-inclusion (succ m) (succ n) l = +functor IH unique-to-𝟙
 where
  IH : Fin m → Fin n
  IH = canonical-Fin-inclusion m n l

canonical-Fin-inclusion-lc : (m n : ℕ) (l : m ≤ n)
                           → left-cancellable (canonical-Fin-inclusion m n l)
canonical-Fin-inclusion-lc zero n            l {x} {y} p = 𝟘-elim x
canonical-Fin-inclusion-lc (succ m) zero     l {x} {y} p = 𝟘-elim l
canonical-Fin-inclusion-lc (succ m) (succ n) l {inl x} {inl y} p = γ
 where
  IH : canonical-Fin-inclusion m n l x ≡ canonical-Fin-inclusion m n l y → x ≡ y
  IH = canonical-Fin-inclusion-lc m n l
  γ : inl x ≡ inl y
  γ = ap inl (IH (inl-lc p))
canonical-Fin-inclusion-lc (succ m) (succ n) l {inr *} {inr *} p = refl

≤-gives-↣ : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
≤-gives-↣ m n l = canonical-Fin-inclusion m n l , canonical-Fin-inclusion-lc m n l

\end{code}

An equivalent construction:

\begin{code}
≤-gives-↣' : (m n : ℕ) → m ≤ n → (Fin m ↣ Fin n)
≤-gives-↣' zero     n        l = unique-from-𝟘 , (λ {x} {x'} p → 𝟘-elim x)
≤-gives-↣' (succ m) zero     l = 𝟘-elim l
≤-gives-↣' (succ m) (succ n) l = g , j
 where
  IH : Fin m ↣ Fin n
  IH = ≤-gives-↣' m n l
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

Added 2nd December 2019. An isomorphic copy of Fin n:

\begin{code}

Fin' : ℕ → 𝓤₀ ̇
Fin' n = Σ \(k : ℕ) → k < n

fzero' : {n : ℕ} → Fin' (succ n)
fzero' = 0 , *

fsucc' : {n : ℕ} → Fin' n → Fin' (succ n)
fsucc' (k , l) = succ k , l

Fin-unprime : (n : ℕ) → Fin' n → Fin n
Fin-unprime zero     (k , l)      = 𝟘-elim l
Fin-unprime (succ n) (zero , l)   = fzero
Fin-unprime (succ n) (succ k , l) = fsucc (Fin-unprime n (k , l))

Fin-prime : (n : ℕ) → Fin n → Fin' n
Fin-prime zero     i       = 𝟘-elim i
Fin-prime (succ n) (inl i) = fsucc' (Fin-prime n i)
Fin-prime (succ n) (inr *) = fzero'

ηFin : (n : ℕ) → Fin-prime n ∘ Fin-unprime n ∼ id
ηFin zero     (k , l)      = 𝟘-elim l
ηFin (succ n) (zero , *)   = refl
ηFin (succ n) (succ k , l) = ap fsucc' (ηFin n (k , l))

εFin : (n : ℕ) → Fin-unprime n ∘ Fin-prime n ∼ id
εFin zero     i       = 𝟘-elim i
εFin (succ n) (inl i) = ap fsucc (εFin n i)
εFin (succ n) (inr *) = refl

≃-Fin : (n : ℕ) → Fin n ≃ Fin' n
≃-Fin n = qinveq (Fin-prime n) (Fin-unprime n , εFin n , ηFin n)

\end{code}
