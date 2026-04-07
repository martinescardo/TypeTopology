Martin Escardo and Paulo Oliva, October 2021, with later additions.

We have various versions of argmin and argmax with different assumptions.


\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.ArgMinMax where

open import MLTT.Spartan hiding (_+_ ; J)

\end{code}

In this version of argmin and argmax we a assume a finite domain with
a finite type of outcomes.

\begin{code}

module ArgMinMax-Fin where

 open import Fin.Embeddings
 open import Fin.Order
 open import Fin.Topology
 open import Fin.Type
 open import MLTT.SpartanList
 open import Naturals.Order
 open import Notation.Order
 open import NotionsOfDecidability.Complemented

\end{code}

Every inhabited complemented subset of Fin n has a least and a
greatest element.

\begin{code}

 Fin-wf : {n : ℕ} (A : Fin n → 𝓤 ̇ ) (r₀ : Fin n)
        → is-complemented A
        → A r₀
        → Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → r ≤ s)
 Fin-wf {𝓤} {succ n} A 𝟎 d a = 𝟎 , a , λ s a' → ⟨⟩
 Fin-wf {𝓤} {succ n} A (suc r₀) d a = γ
  where
   IH : Σ r ꞉ Fin n , A (suc r) × ((s : Fin n) → A (suc s) → r ≤ s)
   IH = Fin-wf {𝓤} {n} (λ x → A (suc x)) r₀ (λ x → d (suc x)) a

   r : Fin n
   r = pr₁ IH

   b : A (suc r)
   b = pr₁ (pr₂ IH)

   c : (s : Fin n) → A (suc s) → r ≤ s
   c = pr₂ (pr₂ IH)

   l : ¬ A 𝟎 → (s : Fin (succ n)) → A s → suc r ≤ s
   l ν 𝟎 a       = 𝟘-elim (ν a)
   l ν (suc x) a = c x a

   γ : Σ r ꞉ Fin (succ n) , A r × ((s : Fin (succ n)) → A s → r ≤ s)
   γ = Cases (d 𝟎)
        (λ a₀ → 𝟎 , a₀ , λ s a' → ⟨⟩)
        (λ (ν : ¬ A 𝟎) → suc r , b , l ν)

 Fin-co-wf : {n : ℕ} (A : Fin n → 𝓤 ̇ ) (r₀ : Fin n)
           → is-complemented A
           → A r₀
           → Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → s ≤ r)
 Fin-co-wf {𝓤} {succ n} A 𝟎 d a = γ
  where
   δ : is-decidable (Σ i ꞉ Fin n , A (suc i))
   δ = Fin-Compact (A ∘ suc) (d ∘ suc)

   Γ = Σ r ꞉ Fin (succ n) , A r × ((s : Fin (succ n)) → A s → s ≤ r)

   γ : Γ
   γ = Cases δ f g
    where
     f : Σ i ꞉ Fin n , A (suc i) → Γ
     f (i , b) = suc r' , a' , h
      where
       IH : Σ r' ꞉ Fin n , A (suc r') × ((s' : Fin n) → A (suc s') → s' ≤ r')
       IH = Fin-co-wf {𝓤} {n} (A ∘ suc) i (d ∘ suc) b

       r' : Fin n
       r' = pr₁ IH

       a' : A (suc r')
       a' = pr₁ (pr₂ IH)

       ϕ : (s' : Fin n) → A (suc s') → s' ≤ r'
       ϕ = pr₂ (pr₂ IH)

       h : (s : Fin (succ n)) → A s → s ≤ suc r'
       h 𝟎       c = ⋆
       h (suc x) c = ϕ x c

     g : ¬ (Σ i ꞉ Fin n , A (suc i)) → Γ
     g ν = 𝟎 , a , h
      where
       h : (s : Fin (succ n)) → A s → s ≤ 𝟎
       h (suc x) c = 𝟘-elim (ν (x , c))
       h 𝟎       c = ⋆

 Fin-co-wf {𝓤} {succ n} A (suc x) d a = suc (pr₁ IH) , pr₁ (pr₂ IH) , h
  where
   IH : Σ r ꞉ Fin n , A (suc r) × ((s : Fin n) → A (suc s) → s ≤ r)
   IH = Fin-co-wf {𝓤} {n} (A ∘ suc) x  (d ∘ suc) a

   h : (s : Fin (succ n)) → A s → s ≤ suc (pr₁ IH)
   h 𝟎       b = ⋆
   h (suc x) b = pr₂ (pr₂ IH) x b

 Fin-argmin : {a r : ℕ} (p : Fin (succ a) → Fin r)
            → Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p x ≤ p y)
 Fin-argmin {0} p = 𝟎 , α
  where
   α : (y : Fin 1) → p 𝟎 ≤ p y
   α 𝟎 = ≤-refl ⟦ p 𝟎 ⟧
 Fin-argmin {succ a} p = γ
  where
   IH : Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p (suc x) ≤ p (suc y))
   IH = Fin-argmin {a} (p ∘ suc)

   x = pr₁ IH
   ϕ = pr₂ IH

   γ : Σ x' ꞉ Fin (succ (succ a)) , ((y : Fin (succ (succ a))) → p x' ≤ p y)
   γ = h (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧)
    where
     h : is-decidable (p 𝟎 ≤ p (suc x)) → type-of γ
     h (inl l) = 𝟎 , α
      where
       α : (y : (Fin (succ (succ a)))) → p 𝟎 ≤ p y
       α 𝟎       = ≤-refl ⟦ p 𝟎 ⟧
       α (suc y) = ≤-trans ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧ ⟦ p (suc y) ⟧ l (ϕ y)
     h (inr ν) = suc x , α
      where
       α : (y : (Fin (succ (succ a)))) → p (suc x) ≤ p y
       α 𝟎       = not-less-bigger-or-equal ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧
                    (contrapositive (<-coarser-than-≤ ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧) ν)
       α (suc y) = ϕ y

 argmin : {a r : ℕ} → (Fin (succ a) → Fin r) → Fin (succ a)
 argmin p = pr₁ (Fin-argmin p)

 argmin-correct : {a r : ℕ} (p : Fin (succ a) → Fin r)
                → (y : Fin (succ a)) → p (argmin p) ≤ p y
 argmin-correct p = pr₂ (Fin-argmin p)

 Fin-argmax : {a r : ℕ} (p : Fin (succ a) → Fin r)
            → Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p y ≤ p x)
 Fin-argmax {0} p = 𝟎 , α
  where
   α : (y : Fin 1) → p y ≤ p 𝟎
   α 𝟎 = ≤-refl ⟦ p 𝟎 ⟧
 Fin-argmax {succ a} p = γ
  where
   IH : Σ x ꞉ Fin (succ a) , ((y : Fin (succ a)) → p (suc y) ≤ p (suc x))
   IH = Fin-argmax {a} (p ∘ suc)

   x = pr₁ IH
   ϕ = pr₂ IH

   γ : Σ x' ꞉ Fin (succ (succ a)) , ((y : Fin (succ (succ a))) → p y ≤ p x')
   γ = h (≤-decidable ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧)
    where
     h : is-decidable (p (suc x) ≤ p 𝟎) → type-of γ
     h (inl l) = 𝟎 , α
      where
       α : (y : (Fin (succ (succ a)))) → p y ≤ p 𝟎
       α 𝟎       = ≤-refl ⟦ p 𝟎 ⟧
       α (suc y) = ≤-trans ⟦ p (suc y) ⟧ ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧ (ϕ y) l
     h (inr ν) = suc x , α
      where
       α : (y : (Fin (succ (succ a)))) → p y ≤ p (suc x)
       α 𝟎       = not-less-bigger-or-equal ⟦ p 𝟎 ⟧ ⟦ p (suc x) ⟧
                    (contrapositive (<-coarser-than-≤ ⟦ p (suc x) ⟧ ⟦ p 𝟎 ⟧) ν)
       α (suc y) = ϕ y

\end{code}

We could define argmin and argmax independently of their
specification, and then prove their specification:

\begin{code}

 argmin' : {a r : ℕ} → (Fin (succ a) → Fin r) → Fin (succ a)
 argmin' {0}      p = 𝟎
 argmin' {succ a} p = γ
  where
   m : Fin (succ a)
   m = argmin' {a} (p ∘ suc)

   γ : Fin (succ (succ a))
   γ = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
        (λ (l : p 𝟎 ≤ p (suc m)) → 𝟎)
        (λ otherwise → suc m)

 argmax' : {a r : ℕ} → (Fin (succ a) → Fin r) → Fin (succ a)
 argmax' {0}      p = 𝟎
 argmax' {succ a} p = γ
  where
   m : Fin (succ a)
   m = argmax' {a} (p ∘ suc)

   γ : Fin (succ (succ a))
   γ = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
        (λ (l : p 𝟎 ≤ p (suc m)) → suc m)
        (λ otherwise → 𝟎)

\end{code}

TODO. Complete the following.

\begin{code}

 {-
 argmax'-correct : {a r : ℕ} (p : Fin (succ a) → Fin r)
                → ((y : Fin (succ a)) → p y ≤ p (argmax p))
 argmax'-correct {0}      p 𝟎 = ≤-refl ⟦ p 𝟎 ⟧
 argmax'-correct {succ a} p y = h y
  where
   m : Fin (succ a)
   m = argmax {a} (p ∘ suc)

   IH : (y : Fin (succ a)) → p (suc y) ≤ p (suc m)
   IH = argmax-correct {a} (p ∘ suc)

   γ : Fin (succ (succ a))
   γ = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
        (λ (l : ⟦ p 𝟎 ⟧ ≤ ⟦ p (suc m) ⟧) → suc m)
        (λ otherwise → 𝟎)

   γ₀ : p 𝟎 ≤ p (suc m) → γ ＝ suc m
   γ₀ = {!!}

   γ₁ : ¬ (p 𝟎 ≤ p (suc m)) → γ ＝ 𝟎
   γ₁ = {!!}


   h : (y : Fin (succ (succ a))) → p y ≤ p γ
   h 𝟎 = l
    where
     l : p 𝟎 ≤ p γ
     l = Cases (≤-decidable ⟦ p 𝟎 ⟧ ⟦ p (suc m) ⟧)
          (λ (l : p 𝟎 ≤ p (suc m)) → transport (λ - → p 𝟎 ≤ p -) ((γ₀ l)⁻¹) l)
          (λ otherwise → {!!})
   h (suc x) = l
    where
     l : p (suc x) ≤ p γ
     l = {!!}
 -}

\end{code}

This version of argmin and argmax assumes a compact domain and a
finite type of outcomes.

\begin{code}

module ArgMinMax-Compact-Fin where

 open import Fin.Order
 open import Fin.Topology
 open import Fin.Type
 open import Notation.Order
 open import NotionsOfDecidability.Complemented
 open import TypeTopology.CompactTypes

 open ArgMinMax-Fin

 compact-argmax : {X : 𝓤 ̇ } {n : ℕ} (p : X → Fin n)
                → is-Compact X
                → X
                → Σ x ꞉ X , ((y : X) → p y ≤ p x)
 compact-argmax {𝓤} {X} {n} p κ x₀ = II I
  where
   A : Fin n → 𝓤 ̇
   A r = Σ x ꞉ X , p x ＝ r

   a₀ : A (p x₀)
   a₀ = x₀ , refl

   δ : is-complemented A
   δ r = κ (λ x → p x ＝ r) (λ x → Fin-is-discrete (p x) r)

   I : Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → s ≤ r)
   I = Fin-co-wf A (p x₀) δ a₀

   II : type-of I → Σ x ꞉ X , ((y : X) → p y ≤ p x)
   II (.(p y) , ((y , refl) , ϕ)) = y , (λ y → ϕ (p y) (y , refl))

 compact-argmin : {X : 𝓤 ̇ } {n : ℕ} (p : X → Fin n)
                → is-Compact X
                → X
                → Σ x ꞉ X , ((y : X) → p x ≤ p y)
 compact-argmin {𝓤} {X} {n} p κ x₀ = II I
  where
   A : Fin n → 𝓤 ̇
   A r = Σ x ꞉ X , p x ＝ r

   a₀ : A (p x₀)
   a₀ = x₀ , refl

   δ : is-complemented A
   δ r = κ (λ x → p x ＝ r) (λ x → Fin-is-discrete (p x) r)

   I : Σ r ꞉ Fin n , A r × ((s : Fin n) → A s → r ≤ s)
   I = Fin-wf A (p x₀) δ a₀

   II : type-of I → Σ x ꞉ X , ((y : X) → p x ≤ p y)
   II (.(p y) , ((y , refl) , ϕ)) = y , (λ y → ϕ (p y) (y , refl))


\end{code}

Added 11th September 2024. Simplified and more efficient version for
the boolean-valued case.

\begin{code}

module ArgMinMax-Fin-𝟚 where

 open import Fin.Type
 open import MLTT.Two-Properties
 open import Naturals.Addition

 Min₂ : (i : ℕ) → (Fin (i + 1) → 𝟚) → 𝟚
 Min₂ 0        p = p 𝟎
 Min₂ (succ i) p = min𝟚 (p 𝟎) (Min₂ i (p ∘ suc))

 Max₂ : (i : ℕ) → (Fin (i + 1) → 𝟚) → 𝟚
 Max₂ 0        p = p 𝟎
 Max₂ (succ i) p = max𝟚 (p 𝟎) (Max₂ i (p ∘ suc))

 argMin₂ : (i : ℕ) → (Fin (i + 1) → 𝟚) → Fin (i + 1)
 argMin₂ 0        p = 𝟎
 argMin₂ (succ i) p =
  𝟚-equality-cases
   (λ (_ : p 𝟎 ＝ ₀) → 𝟎)
   (λ (_ : p 𝟎 ＝ ₁) → suc (argMin₂ i (p ∘ suc)))

 argMax₂ : (i : ℕ) → (Fin (i + 1) → 𝟚) → Fin (i + 1)
 argMax₂ 0        p = 𝟎
 argMax₂ (succ i) p =
  𝟚-equality-cases
   (λ (_ : p 𝟎 ＝ ₀) → suc (argMax₂ i (p ∘ suc)))
   (λ (_ : p 𝟎 ＝ ₁) → 𝟎)

 argMin₂-is-selection-for-Min₂ : (i : ℕ)
                                 (p : Fin (i + 1) → 𝟚)
                               → p (argMin₂ i p) ＝ Min₂ i p
 argMin₂-is-selection-for-Min₂ 0        p = refl
 argMin₂-is-selection-for-Min₂ (succ i) p =
  𝟚-equality-cases
   (λ (e : p 𝟎 ＝ ₀)
      → p (argMin₂ (succ i) p)        ＝⟨ ap p (𝟚-equality-cases₀ e) ⟩
        p 𝟎                          ＝⟨ e ⟩
        ₀                            ＝⟨refl⟩
        min𝟚 ₀ (Min₂ i (p ∘ suc))     ＝⟨ ap (λ - → min𝟚 - (Min₂ i (p ∘ suc))) (e ⁻¹) ⟩
        min𝟚 (p 𝟎) (Min₂ i (p ∘ suc)) ＝⟨refl⟩
        Min₂ (succ i) p               ∎)
   (λ (e : p 𝟎 ＝ ₁)
     → p (argMin₂ (succ i) p)        ＝⟨ ap p (𝟚-equality-cases₁ e) ⟩
       p (suc (argMin₂ i (p ∘ suc))) ＝⟨ argMin₂-is-selection-for-Min₂ i (p ∘ suc) ⟩
       Min₂ i (p ∘ suc)              ＝⟨refl⟩
       min𝟚 ₁ (Min₂ i (p ∘ suc))     ＝⟨ ap (λ - → min𝟚 - (Min₂ i (p ∘ suc))) (e ⁻¹) ⟩
       min𝟚 (p 𝟎) (Min₂ i (p ∘ suc)) ＝⟨refl⟩
       Min₂ (succ i) p               ∎)

 argMax₂-is-selection-for-Max₂ : (i : ℕ)
                                 (p : Fin (i + 1) → 𝟚)
                               → p (argMax₂ i p) ＝ Max₂ i p
 argMax₂-is-selection-for-Max₂ 0        p = refl
 argMax₂-is-selection-for-Max₂ (succ i) p =
  𝟚-equality-cases
   (λ (e : p 𝟎 ＝ ₀)
     → p (argMax₂ (succ i) p)        ＝⟨ ap p (𝟚-equality-cases₀ e) ⟩
       p (suc (argMax₂ i (p ∘ suc))) ＝⟨ argMax₂-is-selection-for-Max₂ i (p ∘ suc) ⟩
       Max₂ i (p ∘ suc)              ＝⟨refl⟩
       max𝟚 ₀ (Max₂ i (p ∘ suc))     ＝⟨ ap (λ - → max𝟚 - (Max₂ i (p ∘ suc))) (e ⁻¹) ⟩
       max𝟚 (p 𝟎) (Max₂ i (p ∘ suc)) ＝⟨refl⟩
       Max₂ (succ i) p               ∎)
   (λ (e : p 𝟎 ＝ ₁)
      → p (argMax₂ (succ i) p)        ＝⟨ ap p (𝟚-equality-cases₁ e) ⟩
        p 𝟎                          ＝⟨ e ⟩
        ₁                            ＝⟨refl⟩
        max𝟚 ₁ (Max₂ i (p ∘ suc))     ＝⟨ ap (λ - → max𝟚 - (Max₂ i (p ∘ suc))) (e ⁻¹) ⟩
        max𝟚 (p 𝟎) (Max₂ i (p ∘ suc)) ＝⟨refl⟩
        Max₂ (succ i) p               ∎)

\end{code}

Added 3rd March 2026. Moved and refined from the alpha-beta file.

This version of argmin and argmax assumes a listed domain and
any type of outcomes that has a decidable order.

\begin{code}

module ArgMinMax-Listed
        {𝓤 𝓥 : Universe}
        (R : 𝓤 ̇ )
        (_<_ : R → R → 𝓥 ̇ )
        (δ : (r s : R) → is-decidable (r < s))
      where

 open import MLTT.List

 _≥_ _≤_ : R → R → 𝓥 ̇
 r ≥ s = ¬ (r < s)
 s ≤ r = r ≥ s

 private
  min' max' : (r s : R) → is-decidable (r < s) → R

  min' r s (inl lt) = r
  min' r s (inr ge) = s

  max' r s (inl lt) = s
  max' r s (inr ge) = r

 min max : R → R → R
 min r s = min' r s (δ r s)
 max r s = max' r s (δ r s)

 open import MonadOnTypes.K
 open K-definitions R

 Min Max : {X : 𝓤 ̇ } → listed⁺ X → K X
 Min (x₀ , xs , _) p = foldr (λ x → min (p x)) (p x₀) xs
 Max (x₀ , xs , _) p = foldr (λ x → max (p x)) (p x₀) xs

 private
  argmin' argmax'
   : {X : 𝓤 ̇ } (p : X → R) (x y : X) → is-decidable (p x < p y) → X

  argmin' p x y (inl le) = x
  argmin' p x y (inr ge) = y

  argmax' p x y (inl le) = y
  argmax' p x y (inr ge) = x

  argmin'-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X) (d : is-decidable (p x < p y))
               → p (argmin' p x y d) ＝ min' (p x) (p y) d
  argmin'-spec p x y (inl lt) = refl
  argmin'-spec p x y (inr ge) = refl

  argmax'-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X) (d : is-decidable (p x < p y))
               → p (argmax' p x y d) ＝ max' (p x) (p y) d
  argmax'-spec p x y (inl lt) = refl
  argmax'-spec p x y (inr ge) = refl


 argmin argmax : {X : 𝓤 ̇ } → (X → R) → X → X → X

 argmin p x y = argmin' p x y (δ (p x) (p y))
 argmax p x y = argmax' p x y (δ (p x) (p y))


 argmin-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X)
             → p (argmin p x y) ＝ min (p x) (p y)
 argmin-spec p x y = argmin'-spec p x y (δ (p x) (p y))

 argmax-spec : {X : 𝓤 ̇ } (p : X → R) (x y : X)
             → p (argmax p x y) ＝ max (p x) (p y)
 argmax-spec p x y = argmax'-spec p x y (δ (p x) (p y))

 open import MonadOnTypes.J
 open J-definitions R

 ArgMin ArgMax : {X : 𝓤 ̇ } → listed⁺ X → J X
 ArgMin (x₀ , xs , _) p = foldr (argmin p) x₀ xs
 ArgMax (x₀ , xs , _) p = foldr (argmax p) x₀ xs

 open import MonadOnTypes.JK R

 ArgMin-spec : {X : 𝓤 ̇ } (ℓ : listed⁺ X) → (ArgMin ℓ) attains (Min ℓ)
 ArgMin-spec {X} (x₀ , xs , m) p = I xs
  where
   I : (xs : List X)
     → p (foldr (argmin p) x₀ xs) ＝ foldr (λ x → min (p x)) (p x₀) xs
   I [] = refl
   I (x ∷ xs) = I₀
    where
     IH : p (foldr (argmin p) x₀ xs) ＝ foldr (λ x → min (p x)) (p x₀) xs
     IH = I xs

     I₀ = p (argmin p x (foldr (argmin p) x₀ xs))         ＝⟨ I₁ ⟩
          min (p x) (p (foldr (argmin p) x₀ xs))          ＝⟨ I₂ ⟩
          min (p x) (foldr (λ x₁ → min (p x₁)) (p x₀) xs) ∎
           where
            I₁ = argmin-spec p x (foldr (argmin p) x₀ xs)
            I₂ = ap (min (p x)) IH

 ArgMax-spec : {X : 𝓤 ̇ } (ℓ : listed⁺ X) → (ArgMax ℓ) attains (Max ℓ)
 ArgMax-spec {X} (x₀ , xs , m) p = I xs
  where
   I : (xs : List X)
     → p (foldr (argmax p) x₀ xs) ＝ foldr (λ x → max (p x)) (p x₀) xs
   I [] = refl
   I (x ∷ xs) = I₀
    where
     IH : p (foldr (argmax p) x₀ xs) ＝ foldr (λ x → max (p x)) (p x₀) xs
     IH = I xs

     I₀ = p (argmax p x (foldr (argmax p) x₀ xs))         ＝⟨ I₁ ⟩
          max (p x) (p (foldr (argmax p) x₀ xs))          ＝⟨ I₂ ⟩
          max (p x) (foldr (λ x₁ → max (p x₁)) (p x₀) xs) ∎
           where
            I₁ = argmax-spec p x (foldr (argmax p) x₀ xs)
            I₂ = ap (max (p x)) IH

\end{code}
